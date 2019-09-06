module Induction

%default total

symmetry : (a = b) -> (b = a)
symmetry Refl = Refl

p1: Nat -> Type
p1 x = (x = 2)

testReplace : (x = y) -> (p1 x) -> (p1 y)
testReplace prf x = replace prf x

rewrite_ : (P : a -> Type) -> (x = y) -> P y -> P x
rewrite_ P Refl prf2 = prf2

testRewrite0: (x = y) -> (p1 y) -> (p1 x)
testRewrite0 prf a = rewrite_ p1 prf a

testRewrite1: (x = y) -> (p1 y) -> (p1 x)
testRewrite1 prf a = replace a prf -- Using replace

testRewrite2: (x = y) -> (p1 y) -> (p1 x)
testRewrite2 prf a = rewrite prf in a

testRewrite3: (x = y) -> (p1 x) -> (p1 y)
testRewrite3 prf a = rewrite (sym prf) in a

testRewrite3a: (x = y) -> (p1 x) -> (p1 y)
testRewrite3a prf a = rewrite (sym prf) in ?hole

testRewrite4: (x = y) -> (p1 y) -> (p1 x)
testRewrite4 Refl prf2 = prf2

testRewrite5: (x = y) -> (p1 x) -> (p1 y)
testRewrite5 Refl prf2 = prf2

namespace Replace1
  ||| Perform substitution in a term according to some equality.
  replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
  replace Refl prf = prf

namespace Replace2
  ||| Perform substitution in a term according to some equality.
  replace : {P : t -> Type} -> x = y -> P x -> P y
  replace Refl prf = prf

plusReducesR : (n : Nat) -> n = plus n 0
plusReducesR Z = Refl
plusReducesR (S k) =
  let ih = plusReducesR k
  in ?plusReduces_hole1

namespace Eq1
  plusSucc : (k, j : Nat) -> (k + S j = S (k + j))
  plusSucc Z j = Refl
  plusSucc (S k) j =
    let ih = plusSucc k j
    in rewrite ih in Refl

namespace Eg2
  eqSucc : {a, b : Nat} -> (a = b) -> (S a = S b)
  eqSucc = cong

  succEq : {a, b : Nat} -> (S a = S b) -> (a = b)
  succEq Refl = Refl

  plusSucc : (k, j : Nat) -> plus k (S j) = S (plus k j)
  plusSucc Z j = Refl
  plusSucc (S k) j =
    let ih = Eg2.plusSucc k j
    in eqSucc ih

namespace Eg3
  eqSucc : (a, b : Nat) -> (a = b) -> (S a = S b)
  eqSucc a b = cong

  plusSucc : (k, j : Nat) -> plus k (S j) = S (plus k j)
  plusSucc Z j = Refl
  plusSucc (S k) j =
    let ih = Eg3.plusSucc k j
    -- Have to get very explicit here if we don't allow Idris to fill in
    -- arguments to eqSucc as in Eg2.
    in Eg3.eqSucc (plus k (S j)) (S (plus k j)) ih
