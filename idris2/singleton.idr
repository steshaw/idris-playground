import Data.Vect

-- Cribbed from "Idris 2: Quantitative Type Theory in Practice"
-- https://arxiv.org/pdf/2104.00480.pdf
data Singleton : a -> Type where
  Val : (x : a) -> Singleton x

a : Singleton "hah!"
a = Val "hah!" -- "bah!" will not do!
