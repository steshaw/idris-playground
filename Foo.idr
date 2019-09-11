p1: a -> Type

testRewrite2: (x = y) -> (p1 y) -> (p1 x)
testRewrite2 a b = rewrite a in ?asdf

rewrite0 : (P : t -> Type) -> x = y -> P y -> P x
rewrite0 P prf a = rewrite prf in ?rewrite0_rhs1
