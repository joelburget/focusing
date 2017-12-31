{-# language LambdaCase #-}
{-# language GeneralizedNewtypeDeriving #-}
module Main where

import Data.Foldable (toList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Text (Text)

import Data.Plur

data F2 = I1 | I2

type Atom = Text
type Var  = Int
type ContextList = [(Var, Formula)]
newtype Context a = Context { unContext :: Map Formula a }
  deriving (Show, Eq, Ord, Functor, Foldable)
type Context' = Context (Plur Var)

-- contextMerge :: Context -> Context -> Context
-- contextMerge (Context a) (Context b) = Context (Map.merge a b)

data Formula
  = Atom Atom
  | And  Formula Formula
  | Or   Formula Formula
  | Impl Formula Formula
  deriving (Show, Eq, Ord)

data DerivationInv
  = RAnd DerivationInv DerivationInv
  | LOr Var Formula DerivationInv Formula DerivationInv
  | RImpl Var Formula DerivationInv
  | Foc ContextList Context' DerivationFoc

data DerivationFoc
  = AtomDown DerivationDown
  | StartUp DerivationUp
  | Cut [(Var, DerivationDown)] DerivationInv

data DerivationDown
  = LAnd DerivationDown F2
  | LImpl DerivationDown DerivationUp
  | StartDown Context' Var Formula

data DerivationUp
  = ROr (Either (DerivationUp, Formula) (Formula, DerivationUp))
  | EndUp DerivationInv

data Obligation
  = Done DerivationDown
  | Request Formula (DerivationUp -> Obligation)

decomp :: Formula -> [(DerivationDown -> Obligation, Formula)]
decomp pa = case pa of
  Atom _ -> [(Done, pa)]
  Or _ _ -> [(Done, pa)]
  And a1 a2 ->
    let prepend side (obli, hd) = (\d -> obli (LAnd d side), hd)
    in fmap (prepend I1) (decomp a1) <> fmap (prepend I2) (decomp a2)
  Impl a b ->
    let prepend (obli, hd) = (\dab -> Request a (\da -> obli (LImpl dab da)), hd)
    in fmap prepend (decomp b)

data Term
  = Var Var
  | Lam Var Formula Term
  | App Term Term
  | Pair Term Term
  | Proj F2 Term
  | Inj Bool Term
  | Case Var Term Term
  | Let [(Var, Term)] Term

termInv :: DerivationInv -> Term
termInv = \case
  RAnd da db -> Pair (termInv da) (termInv db)
  LOr v _ta da _tb db -> Case v (termInv da) (termInv db)
  RImpl v f d -> Lam v f (termInv d)
  Foc _deltaLi _delta d -> termFoc d

termFoc :: DerivationFoc -> Term
termFoc = \case
  AtomDown d -> termDown d
  StartUp d -> termUp d
  Cut bindings d ->
    let bindings' = (\(v, d') -> (v, termDown d')) <$> bindings
        body = termInv d
    in if null bindings' then body else Let bindings' body

termDown :: DerivationDown -> Term
termDown = \case
  LAnd d side -> Proj side (termDown d)
  LImpl dab da -> App (termDown dab) (termUp da)
  StartDown _gamma var _t -> Var var

termUp :: DerivationUp -> Term
termUp = \case
  ROr side ->
    let (side', d) = case side of
          Left (d', _) -> (True, d')
          Right (_, d') -> (False, d')
    in Inj side' (termUp d)
  EndUp d -> termInv d

data RedundancyMode = Hyp | Goal

-- gamma: Context'
redundant :: RedundancyMode -> Context' -> Formula -> Bool
redundant mode gamma t = case t of
  Or a b -> case mode of
    Hyp  -> redundant mode gamma a && redundant mode gamma b
    Goal -> redundant mode gamma a || redundant mode gamma b
  Atom _ -> undefined
  And a b -> redundant mode gamma a && redundant mode gamma b
  Impl _a b -> redundant mode gamma b

-- sigma: Set Var
uses :: Set Var -> DerivationDown -> Bool
uses =
  let usesInv sigma = \case
        RAnd da db -> usesInv sigma da || usesInv sigma db
        RImpl _v _a da -> usesInv sigma da
        Foc _ _  d -> usesFoc sigma d
      usesFoc sigma = \case
        AtomDown d -> usesDown sigma d
        StartUp d -> usesUp sigma d
        Cut bindings d -> undefined
      usesDown sigma = \case
        LAnd d _ -> usesDown sigma d
        LImpl down up -> usesDown sigma down || usesUp sigma up
        StartDown _ v _ -> undefined
      usesUp sigma = \case
        ROr (Left (d, _)) -> usesUp sigma d
        ROr (Right (_, d)) -> usesUp sigma d
        EndUp d -> usesInv sigma d
  in usesDown

-- delta: ContextList
quotient :: ContextList -> Context' -> Context'
quotient = undefined

addAfter :: Context' -> Context' -> Context'
addAfter gamma delta = undefined

data Judgement = Judgement Context' Formula
  deriving (Eq, Ord)

newtype Memory = Memory (Map Judgement (Plur ()))
  deriving Monoid

find :: Judgement -> Memory -> Plur ()
find j (Memory mem) = Map.findWithDefault Zero j mem

add :: Judgement -> Plur () -> Memory -> Memory
add j v (Memory mem) = Memory (Map.insert j v mem)

newtype Tabulation a = Tabulation (Map Formula (Map Context' a))
  deriving Monoid

withGoal goal tab = Map.findWithDefault mempty goal tab

findTab :: Context' -> Formula -> Tabulation a -> Maybe a
findTab context goal (Tabulation tab) = Map.lookup goal tab >>= Map.lookup context

addTab :: Context' -> Formula -> a -> Tabulation a -> Tabulation a
addTab context goal v (Tabulation tab) = Tabulation (Map.insert goal (Map.insert context v (withGoal goal tab)) tab)

type M = Maybe

searchInv :: Memory -> Context' -> ContextList -> Formula -> M DerivationInv
searchInv memo gamma delta goal = searchInvSplit memo gamma [] delta goal

searchInvSplit :: Memory -> Context' -> ContextList -> ContextList -> Formula -> M DerivationInv
searchInvSplit memo gamma deltaNa sigma goal = case sigma of
  na@(_, Atom _)   : sigma' -> searchInvSplit memo gamma (na : deltaNa) sigma goal
  na@(_, And _ _)  : sigma' -> searchInvSplit memo gamma (na : deltaNa) sigma goal
  na@(_, Impl _ _) : sigma' -> searchInvSplit memo gamma (na : deltaNa) sigma goal
  (v, Or a1 a2) : sigma' -> do
    d1 <- searchInvSplit memo gamma deltaNa ((v, a1) : sigma') goal
    d2 <- searchInvSplit memo gamma deltaNa ((v, a2) : sigma') goal
    pure $ LOr v a1 d1 a2 d2
  [] -> case goal of
    And a b -> do
      da <- searchInvSplit memo gamma deltaNa [] a
      db <- searchInvSplit memo gamma deltaNa [] b
      pure $ RAnd da db
    Impl a b -> do
      let v = undefined
      d <- searchInvSplit memo gamma deltaNa [(v, a)] b
      pure $ RImpl v a d
    pa {- Atom / Or -} -> do
      let deltaRemainder = quotient deltaNa gamma
      d <- searchFoc memo gamma deltaRemainder pa
      pure $ Foc deltaNa deltaRemainder d

searchFoc :: Memory -> Context' -> Context' -> Formula -> M DerivationFoc
searchFoc memo gamma delta goal =
  if null delta
  then searchFocRight memo gamma goal
  else searchFocLeft memo gamma delta goal

searchFocRight :: Memory -> Context' -> Formula -> M DerivationFoc
searchFocRight memo gamma goal =
  let request = Judgement gamma goal
  in case find request memo of
       Two () () -> undefined -- pure Zero
       calls -> let memo' = add request undefined memo -- (calls <> One ()) memo
                in searchFocRight' memo gamma goal

searchFocRight' :: Memory -> Context' -> Formula -> M DerivationFoc
searchFocRight' memo gamma goal = case goal of
  Atom atom -> do
    d <- searchDownAtom memo gamma atom
    pure $ AtomDown d
  And  _ _ -> Nothing
  Impl _ _ -> Nothing
  Or _ _ -> do
    d <- searchUp memo gamma goal
    pure $ StartUp d

searchFocLeft :: Memory -> Context' -> Context' -> Formula -> M DerivationFoc
searchFocLeft memo gamma delta goal =
  let gammaDelta = addAfter gamma delta
  in if redundant Goal gammaDelta goal
     then do
       dUp <- searchUp memo gammaDelta goal
       pure $ StartUp dUp
     else do
       satur <- saturate memo gammaDelta delta
       let vars = fmap (\_ -> undefined) satur
           (formulas, derivs) = unzip satur
           cut = zip vars derivs
           context = zip vars formulas
       d <- searchInv memo gammaDelta context goal
       pure $ Cut cut d

searchUp :: Memory -> Context' -> Formula -> M DerivationUp
searchUp = searchUp' -- case monotony gamma goal

searchUp' :: Memory -> Context' -> Formula -> M DerivationUp
searchUp' memo gamma goal = case goal of
  Or a1 a2 -> do
    d1 <- searchUp memo gamma a1
    let left = One $ ROr (Left (d1, a2))
    d2 <- searchUp memo gamma a2
    let right = One $ ROr (Right (a1, d2))
    pure $ undefined -- left <> right
  _ -> do
    d <- searchInv memo gamma [] goal
    pure $ EndUp d

searchDownAtom :: Memory -> Context' -> Atom -> M DerivationDown
searchDownAtom = searchDownAtom'

selectOblis p gamma = undefined
  -- let addOblis na multi oblis =
  --       let candidates = map
  --             (\(obli, head) -> do
  --               v <- multi

searchDownAtom' :: Memory -> Context' -> Atom -> M DerivationDown
searchDownAtom' memo gamma x =
  let oblis = selectOblis (\case
        Atom y -> x == y
        _ -> False
        )
        gamma
      proofs = undefined
  in undefined -- pure $ foldl proofs Zero oblis

contextAsSet :: Context' -> Set Var
contextAsSet (Context context) =
  foldMap
    (\plurVar -> Set.fromList (toList plurVar))
    context

saturate :: Memory -> Context' -> Context' -> M [(Formula, DerivationDown)]
saturate memo gamma delta =
  let strictlyPositive = \case
        Or _ _ -> True
        _      -> False
      goodCut t = strictlyPositive t && not (redundant Hyp gamma t)
      oblis = selectOblis goodCut gamma
      deltaAsSet = contextAsSet delta
  in undefined
  -- in pure $ filter (\(_head, deriv) -> uses deltaAsSet deriv) $
  --      concat $
  --      map toList $
  --      map (\multiObli -> undefined)
  --      oblis

main :: IO ()
main = putStrLn "Hello, Haskell!"
