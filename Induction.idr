module Induction

%default total

||| Perform substitution in a term according to some equality.
preludeReplace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
preludeReplace Refl prf = prf

||| Perform substitution in a term according to some equality.
|||
||| Like `replace`, but with an explicit predicate, and applying the
||| rewrite in the other direction, which puts it in a form usable by
||| the `rewrite` tactic and term.
preludeRewrite__impl : (P : a -> Type) -> x = y -> P y -> P x
preludeRewrite__impl p Refl prf = prf

symmetry : (a = b) -> (b = a)
symmetry Refl = Refl

p1: Nat -> Type
p1 a = (a = 2)

ourReplace : {P : t -> Type} -> x = y -> P x -> P y
ourReplace Refl x = x

testReplace : (x = y) -> (p1 x) -> (p1 y)
testReplace prf x = replace prf x

ourRewrite : (P : a -> Type) -> (x = y) -> P y -> P x
ourRewrite P Refl prf2 = prf2

testRewrite0: (x = y) -> (p1 y) -> (p1 x)
testRewrite0 prf a = ourRewrite p1 prf a

testRewrite1: (x = y) -> (p1 y) -> (p1 x)
testRewrite1 prf a = replace a prf -- Using replace

testRewrite1a: (x = y) -> (p1 x) -> (p1 y)
testRewrite1a prf a = replace prf a -- replace in other direction.

testRewriteY2X: (x = y) -> (p1 y) -> (p1 x)
testRewriteY2X prf a = rewrite prf in ?hole1

testRewriteX2Y: (x = y) -> (p1 x) -> (p1 y)
testRewriteX2Y prf a = rewrite (sym prf) in ?hole2

testReflX2YRefl: (x = y) -> (p1 x) -> (p1 y)
testReflX2YRefl Refl a = a

-- Reverse of testRewritey to x.
testReflY2X: (x = y) -> (p1 y) -> (p1 x)
testReflY2X Refl a = a

namespace Replace1
  ||| Perform substitution in a term according to some equality.
  replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
  replace Refl prf = prf

namespace Replace2
  ||| Perform substitution in a term according to some equality.
  replace : {P : t -> Type} -> x = y -> P x -> P y
  replace Refl prf = prf

preludePlusZeroRightNeutral2 : (left : Nat) -> left + 0 = left
preludePlusZeroRightNeutral2 Z     = Refl
preludePlusZeroRightNeutral2 (S n) =
  let inductiveHypothesis = preludePlusZeroRightNeutral2 n in
    rewrite inductiveHypothesis in Refl

plusZeroRightIdentity : (n : Nat) -> n + 0 = n
plusZeroRightIdentity Z = Refl
plusZeroRightIdentity (S k) =
  let ih = plusZeroRightIdentity k
  in rewrite ih in Refl

plusReducesR : (n : Nat) -> n = plus n Z
plusReducesR Z = Refl
plusReducesR (S k) =
  let
    ih = plusReducesR k
    symIH = sym ih
  in rewrite symIH in Refl

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
