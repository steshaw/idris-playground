-- WARNING: This does not compile!

import Data.Vect

-- Cribbed from "Idris 2: Quantitative Type Theory in Practice"
-- https://arxiv.org/pdf/2104.00480.pdf
data Singleton : a -> Type where
  Val : (x : a) -> Singleton x

a : Singleton "hah!"
a = Val "hah!" -- "bah!" will not do!

-- Cribbed from https://gist.github.com/berewt/9f1f735cd0a47847981ab7c8f3bfa39b

data Union : {n: Nat} -> Vect n Type -> Type where
  IsA: t -> {auto e: elem t ts} -> Union ts

StrInt : Type
StrInt = Union [String, Int]

s : StrInt
s = "foo"

i : StrInt
i = 42

-- Usage:
-- the fruit isA $ AnOrange "foo"
-- the fruit isA $ AnApple "bar"
