{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
module Focusing where

import Control.Lens hiding (Context, Context', uses)
import Control.Monad.Error.Class
import Control.Monad.Except
import Control.Monad.Gen
import Data.Foldable (foldlM, toList)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Map.Merge.Strict (preserveMissing, zipWithMatched)
import qualified Data.Map.Merge.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as Text

import Data.Plur

data F2 = I1 | I2
  deriving Show

type Atom = Text
type Var  = Int
type ContextList = [(Var, Type)]
newtype Context a = Context { unContext :: Map Type a }
  deriving (Show, Eq, Ord, Functor, Foldable, Monoid)
type Context' = Context (Plur Var)

contextFind :: Type -> Context' -> Plur Var
contextFind formula (Context context)
  = Map.findWithDefault Zero formula context

data Type
  = Atom Atom
  | And  Type Type
  | Or   Type Type
  | Impl Type Type
  deriving (Eq, Ord)

instance Show Type where
  showsPrec _d = \case
    Atom t     -> showString (Text.unpack t)
    And  f1 f2 -> showsPrec 1 f1 . showString " * "  . showsPrec 1 f2
    Or   f1 f2 -> showsPrec 2 f1 . showString " + "  . showsPrec 2 f2
    Impl f1 f2 -> showsPrec 3 f1 . showString " -> " . showsPrec 3 f2

-- judgements:

-- invertible
data DerivationInv
  = RAnd DerivationInv DerivationInv
  | LOr Var Type DerivationInv Type DerivationInv
  | RImpl Var Type DerivationInv
  | Foc ContextList Context' DerivationFoc

-- focusing
data DerivationFoc
  = AtomDown DerivationDown
  | StartUp DerivationUp
  | Cut [(Var, DerivationDown)] DerivationInv

-- non-invertible elimination
data DerivationDown
  = LAnd DerivationDown F2
  | LImpl DerivationDown DerivationUp
  | StartDown Context' Var Type

-- non-invertible introduction
data DerivationUp
  = ROr (Either (DerivationUp, Type) (Type, DerivationUp))
  | EndUp DerivationInv

data Obligation
  = Done DerivationDown
  | Request Type (DerivationUp -> Obligation)

decomp :: Type -> [(DerivationDown -> Obligation, Type)]
decomp pa = case pa of
  Atom _ -> [(Done, pa)]
  Or _ _ -> [(Done, pa)]
  And a1 a2 ->
    let prepend side (obli, hd) = (\d -> obli (LAnd d side), hd)
    in fmap (prepend I1) (decomp a1) <> fmap (prepend I2) (decomp a2)
  Impl a b ->
    let prepend (obli, hd)
          = (\dab -> Request a (\da -> obli (LImpl dab da)), hd)
    in fmap prepend (decomp b)

data Term
  = Var Var
  | Lam Var Type Term
  | App Term Term
  | Pair Term Term
  | Proj F2 Term
  | Inj F2 Term
  | Case Var Term Term
  | Let [(Var, Term)] Term

instance Show Term where
  showsPrec _d = \case
    Var n -> showString "x" . shows n
    Lam n ty body
      -> showString "\\x"
       . shows n
       . showString " : "
       . shows ty
       . showString " -> "
       . shows body
    App tm1 tm2 -> showsPrec 11 tm1 . showString " " . showsPrec 11 tm2
    Pair tm1 tm2
      -> showString "("
       . showsPrec 1 tm1
       . showString ", "
       . showsPrec 1 tm2
       . showString ")"
    Proj side tm
      -> showString (case side of { I1 -> "outl "; I2 -> "outr " })
       . showsPrec 11 tm
    Inj side tm
      -> showString (case side of { I1 -> "inl "; I2 -> "inr " })
       . showsPrec 11 tm
    Case n tm1 tm2 -> showString "case x" . shows n
      . showString " of { inl -> " . showsPrec 1 tm1
      . showString "; inr -> " . showsPrec 1 tm2
      . showString "; }"
    Let bindings body
      -> showString "let { "
       . showList bindings
       . showString " } in "
       . shows body

termInv :: DerivationInv -> Term
termInv = \case
  RAnd da db            -> Pair (termInv da) (termInv db)
  LOr v _ta da _tb db   -> Case v (termInv da) (termInv db)
  RImpl v f d           -> Lam v f (termInv d)
  Foc _deltaLi _delta d -> termFoc d

termFoc :: DerivationFoc -> Term
termFoc = \case
  AtomDown d     -> termDown d
  StartUp d      -> termUp d
  Cut bindings d ->
    let bindings' = (\(v, d') -> (v, termDown d')) <$> bindings
        body = termInv d
    in if null bindings' then body else Let bindings' body

termDown :: DerivationDown -> Term
termDown = \case
  LAnd d side             -> Proj side (termDown d)
  LImpl dab da            -> App (termDown dab) (termUp da)
  StartDown _gamma var _t -> Var var

termUp :: DerivationUp -> Term
termUp = \case
  ROr side ->
    let (side', d) = case side of
          Left (d', _)  -> (I1, d')
          Right (_, d') -> (I2, d')
    in Inj side' (termUp d)
  EndUp d -> termInv d

data RedundancyMode = Hyp | Goal

redundant :: RedundancyMode -> Context' -> Type -> Bool
redundant mode gamma t = case t of
  Or a b -> case mode of
    Hyp  -> redundant mode gamma a && redundant mode gamma b
    Goal -> redundant mode gamma a || redundant mode gamma b
  Atom _ -> case contextFind t gamma of
    Two _ _ -> True
    _       -> False
  And a b -> redundant mode gamma a && redundant mode gamma b
  Impl _a b -> redundant mode gamma b

uses :: Set Var -> DerivationDown -> Bool
uses =
  let usesInv sigma = \case
        RAnd da db      -> usesInv sigma da || usesInv sigma db
        LOr _ _ da _ db -> usesInv sigma da || usesInv sigma db
        RImpl _v _a da  -> usesInv sigma da
        Foc _ _  d      -> usesFoc sigma d
      usesFoc sigma = \case
        AtomDown d     -> usesDown sigma d
        StartUp d      -> usesUp sigma d
        Cut bindings d ->
          let newVars = map fst $
                filter (\(_v, d') -> usesDown sigma d') bindings
              newSigma = foldr Set.insert sigma newVars
          in usesInv newSigma d
      usesDown sigma = \case
        LAnd d _        -> usesDown sigma d
        LImpl down up   -> usesDown sigma down || usesUp sigma up
        StartDown _ v _ -> Set.member v sigma
      usesUp sigma = \case
        ROr (Left (d, _))  -> usesUp sigma d
        ROr (Right (_, d)) -> usesUp sigma d
        EndUp d -> usesInv sigma d
  in usesDown

quotient :: ContextList -> Context' -> Context'
quotient delta (Context gamma) =
  let Context delta' = foldl (\ctx (var, ty) -> addContext ty var ctx) mempty delta
      quoti k v = case Map.findWithDefault Zero k gamma of
        Two _ _ -> Zero
        Zero    -> v
        One _   -> case v of
          Two x _ -> One x
          _       -> v

      addContext :: Type -> Var -> Context' -> Context'
      addContext k v (Context t) = Context (Map.insertWith (<>) k (One v) t)
  in Context (imap quoti delta')

data Judgement = Judgement Context' Type
  deriving (Eq, Ord)

newtype Memory = Memory (Map Judgement (Plur ()))
  deriving Monoid

-- Tabulation is used for memoization in the original implementation.
-- Unfortunately I don't know how to do this particular memoization purely.

-- newtype Tabulation a = Tabulation (Map Type (Map Context' a))
--   deriving Monoid

-- withGoal :: Type -> Map Type (Map Context' a) -> Map Context' a
-- withGoal goal tab = Map.findWithDefault mempty goal tab

-- findTab :: Context' -> Type -> Tabulation a -> Maybe a
-- findTab context goal (Tabulation tab)
--   = Map.lookup goal tab >>= Map.lookup context

-- addTab :: Context' -> Type -> a -> Tabulation a -> Tabulation a
-- addTab context goal v (Tabulation tab)
--   = Tabulation (Map.insert goal (Map.insert context v (withGoal goal tab)) tab)

data Failure = Failure
  deriving Show

type M = GenT Var (Except Failure)

runM :: M a -> Either Failure a
runM = runExcept . runGenT

searchInv
  :: Memory -> Context' -> ContextList -> Type -> M (Plur DerivationInv)
searchInv memo gamma delta goal = searchInvSplit memo gamma [] delta goal

fresh :: M Var
fresh = gen

searchInvSplit
  :: Memory
  -> Context'
  -> ContextList
  -> ContextList
  -> Type
  -> M (Plur DerivationInv)
searchInvSplit memo gamma deltaNa sigma goal = case sigma of
  (v, Or a1 a2) : sigma' -> do
    d1 <- searchInvSplit memo gamma deltaNa ((v, a1) : sigma') goal
    d2 <- searchInvSplit memo gamma deltaNa ((v, a2) : sigma') goal
    pure $ LOr v a1 <$> d1 <*> pure a2 <*> d2

  -- Atom, And, Impl
  na : sigma' -> searchInvSplit memo gamma (na : deltaNa) sigma' goal

  [] -> case goal of
    And a b -> do
      da <- searchInvSplit memo gamma deltaNa [] a
      db <- searchInvSplit memo gamma deltaNa [] b
      pure $ RAnd <$> da <*> db
    Impl a b -> do
      v <- fresh
      d <- searchInvSplit memo gamma deltaNa [(v, a)] b
      pure $ RImpl v a <$> d
    pa {- Atom / Or -} -> do
      let deltaRemainder = quotient deltaNa gamma
      d <- searchFoc memo gamma deltaRemainder pa
      pure $ Foc deltaNa deltaRemainder <$> d

searchFoc :: Memory -> Context' -> Context' -> Type -> M (Plur DerivationFoc)
searchFoc memo gamma delta goal =
  if null delta
  then searchFocRight memo gamma goal
  else searchFocLeft memo gamma delta goal

searchFocRight :: Memory -> Context' -> Type -> M (Plur DerivationFoc)
searchFocRight memo gamma goal =
  let request = Judgement gamma goal

      find :: Judgement -> Memory -> Plur ()
      find j (Memory mem) = Map.findWithDefault Zero j mem

      add :: Judgement -> Plur () -> Memory -> Memory
      add j v (Memory mem) = Memory (Map.insert j v mem)

  in case find request memo of
       Two () () -> pure Zero
       calls -> let memo' = add request (calls <> One ()) memo
                in searchFocRight' memo' gamma goal

searchFocRight' :: Memory -> Context' -> Type -> M (Plur DerivationFoc)
searchFocRight' memo gamma goal = case goal of
  Atom atom -> do
    d <- searchDownAtom memo gamma atom
    pure $ AtomDown <$> d
  And  _ _ -> throwError Failure
  Impl _ _ -> throwError Failure
  Or   _ _ -> do
    d <- searchUp memo gamma goal
    pure $ StartUp <$> d

searchFocLeft
  :: Memory -> Context' -> Context' -> Type -> M (Plur DerivationFoc)
searchFocLeft memo (Context gamma) delta@(Context delta') goal =
  let gammaDelta = Context $ Map.merge
        preserveMissing
        preserveMissing
        (zipWithMatched (\_ a b -> a <> b))
        gamma delta'

  in if redundant Goal gammaDelta goal
     then do
       dUp <- searchUp memo gammaDelta goal
       pure $ StartUp <$> dUp
     else do
       satur <- saturate memo gammaDelta delta
       vars  <- traverse (\_ -> fresh) satur
       let (formulas, derivs) = unzip satur
           cut     = zip vars derivs
           context = zip vars formulas
       d <- searchInv memo gammaDelta context goal
       pure $ Cut cut <$> d

searchUp :: Memory -> Context' -> Type -> M (Plur DerivationUp)
searchUp = searchUp' -- case monotony gamma goal

searchUp' :: Memory -> Context' -> Type -> M (Plur DerivationUp)
searchUp' memo gamma goal = case goal of
  Or a1 a2 -> do
    d1 <- searchUp memo gamma a1
    let left = ROr . Left . (, a2) <$> d1
    d2 <- searchUp memo gamma a2
    let right = ROr . Right . (a1,) <$> d2
    pure (left <> right)
  _ -> do
    d <- searchInv memo gamma [] goal
    pure $ EndUp <$> d

selectOblis :: (Type -> Bool) -> Context' -> [Plur (Obligation, Type)]
selectOblis p gamma@(Context gamma') =
  let addOblis na oblis multi =
        let candidates = map
              (\(obli, hd) -> do
                v <- multi
                pure (obli (StartDown gamma v na), hd))
              $ filter (\(_obli, hd) -> p hd)
              $ decomp na
        in candidates <> oblis
  in ifoldl addOblis [] gamma'

searchDownAtom :: Memory -> Context' -> Atom -> M (Plur DerivationDown)
searchDownAtom = searchDownAtom'

-- same as mappend?
-- lazySum :: Plur a -> Plur a -> Plur a

fulfill
  :: (t -> Type -> M (Plur DerivationUp))
  -> t
  -> Obligation
  -> M (Plur DerivationDown)
fulfill mySearchUp gamma obli = case obli of
  Done deriv -> pure $ pure deriv
  Request formula req -> do
    dUp <- mySearchUp gamma formula
    fmap join $ traverse (fulfill mySearchUp gamma) (req <$> dUp)

searchDownAtom' :: Memory -> Context' -> Atom -> M (Plur DerivationDown)
searchDownAtom' memo gamma x =
  let oblis :: [Plur (Obligation, Type)]
      oblis = selectOblis (\case
        Atom y -> x == y
        _      -> False
        )
        gamma

      proofs
        :: Plur DerivationDown
        -> (Obligation, Type)
        -> M (Plur DerivationDown)
      proofs acc (obli, _head) = do
        deriv <- fulfill (searchUp memo) gamma obli
        pure $ acc <> deriv

  in foldlM proofs Zero (concat (toList <$> oblis))

contextAsSet :: Context' -> Set Var
contextAsSet (Context context) = foldMap (Set.fromList . toList) context

saturate :: Memory -> Context' -> Context' -> M [(Type, DerivationDown)]
saturate memo gamma delta = do
  let strictlyPositive = \case
        Or _ _ -> True
        _      -> False
      goodCut t  = strictlyPositive t && not (redundant Hyp gamma t)
      oblis      = selectOblis goodCut gamma
      deltaAsSet = contextAsSet delta

      traverser :: Plur (Obligation, Type) -> M [(Type, DerivationDown)]
      traverser multiObli = case multiObli of
        Zero -> pure []
        One (obli, hd) -> do
          deriv <- fulfill (searchUp memo) gamma obli
          pure $ (hd,) <$> toList deriv
        Two (obli1, head1) (obli2, head2) -> do
          deriv1 <- fulfill (searchUp memo) gamma obli1
          deriv2 <- fulfill (searchUp memo) gamma obli2
          pure $ ((head1,) <$> toList deriv1) <> ((head2,) <$> toList deriv2)

  derivs <- traverse traverser oblis

  pure $ filter (\(_head, deriv) -> uses deltaAsSet deriv) $ concat derivs

search :: Type -> M (Plur DerivationInv)
search = searchInv mempty mempty []

terms :: M (Plur DerivationInv) -> Either Failure [Term]
terms t = case runM t of
  Left f   -> Left f
  Right t' -> Right (fmap termInv (toList t'))

printImpls :: Type -> IO ()
printImpls f = do
  let tms = terms (search f)
  case tms of
    Left err -> print err
    Right tms' -> mapM_ putStrLn (("  * " <>) . show <$> tms')
