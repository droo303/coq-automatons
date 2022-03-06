Add LoadPath "./" as Cpdt.

Require Import BaseDefinitions.v

(* Concat test *)
Section ConcatTest.
Inductive ab_alpha : Alphabet := 
| a
| b
.

Variable w1:Word(ab_alpha).
Variable w2:Word(ab_alpha).

Compute (ConcatWord ab_alpha w1 w2).
End ConcatTest.

Section LangIntersectionTest.

Inductive cd_alpha : Alphabet :=
| c
| d
.

Variable w_ab:Word ab_alpha.
Variable w_cd:Word cd_alpha.

Variable l_ab:Language ab_alpha.
Variable l_cd:Language cd_alpha.

Compute LangIntersection ab_alpha l_ab l_ab w_ab. 

End LangIntersectionTest.


Section LangUnificationTest.

Variable w_ab:Word ab_alpha.
Variable w_cd:Word cd_alpha.

Variable l_ab:Language ab_alpha.
Variable l_cd:Language cd_alpha.

Compute LangUnification ab_alpha l_ab l_ab w_ab. 

End LangUnificationTest.
