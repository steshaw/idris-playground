p1 : Type -> Type

testRewrite0 : (x = y) -> (p1 x) -> (p1 y)
testRewrite0 prf a = rewrite (sym prf) in a

testRewrite1 : (x = y) -> (p1 y) -> (p1 x)
testRewrite1 prf a = rewrite prf in a

testRewrite2: (x = y) -> (p1 y) -> (p1 x)
testRewrite2 prf b = ?hole1
