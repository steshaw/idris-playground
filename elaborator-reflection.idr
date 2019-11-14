--
-- Examples from the Idris mailing list
-- https://groups.google.com/d/msg/idris-lang/0kynfemeSvM/ek06v6oPBgAJ
--

double : Nat -> Nat
double Z = 0
double (S k) = S (S (double k))
