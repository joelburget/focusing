{-# language OverloadedStrings #-}
module Focusing.Examples (Example(..), examples) where

import Data.Text (Text)

import Focusing

a, b, c, d :: Type
a = Atom "A"
b = Atom "B"
c = Atom "C"
d = Atom "D"

r :: Type
r = Atom "r"

cont :: Type -> Type -> Type
cont r' a' = Impl (Impl a' r') r'

-- a'F, b'F, c'F, d'F :: Type
-- a'F = Atom "A'"
-- b'F = Atom "B'"
-- c'F = Atom "C'"
-- d'F = Atom "D'"

data Example = Example
  { description :: Text
  , expectedCount :: Int
  , formula :: Type
  }

examples :: [Example]
examples =
  [ Example "a -> b" 0 (Impl a b)
  , Example "(c -> d) -> (c -> d)" 1 (let cd = Impl c d in Impl cd cd)
  , Example "c -> c -> c" 2 (Impl c (Impl c c))
  , Example "a + b -> a + b" 1 (let ab = Or a b in Impl ab ab)
  , Example "a -> (a -> b + c) -> b + c" 1 (Impl a (Impl (Impl a (Or b c)) (Or b c)))
  , Example "a -> (a -> b + b) -> b + c" 1 (Impl a (Impl (Impl a (Or b b)) (Or b c)))
  , Example "a -> (a -> b + b) -> c + c" 0 (Impl a (Impl (Impl a (Or b b)) (Or c c)))
  , Example "a -> (a -> b + b) -> b + b" 2 (Impl a (Impl (Impl a (Or b b)) (Or b b)))
  , Example "cont r a -> cont r a" 2 (Impl (cont r a) (cont r a))
  , Example "(a -> b -> r) -> (b -> a -> r)" 1 $
    let abr = Impl a (Impl b r)
        bar = Impl b (Impl a r)
    in Impl abr bar
  , Example "(a -> b) -> (c -> d) -> a + c -> b + d" 1 $
    Impl
      (Impl a b)
      (Impl
        (Impl c d)
        (Impl
          (Or a c)
          (Or b d)))
  , Example "a -> (a -> a) -> a (church numerals)" 2 (Impl a (Impl (Impl a a) a))
  ]
