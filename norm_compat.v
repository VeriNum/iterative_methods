From Coq Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect ssralg 
              ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas inf_norm_properties.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


(** 2 norm of a vector **)
Definition vec_norm2 {n:nat} (v : 'cV[R]_n.+1) :=
  sqrt (\sum_j (Rsqr (v j ord0))).


Lemma norm2_inf_norm_compat {n:nat} (v : 'cV[R]_n.+1):
  (vec_norm2 v <= sqrt (INR n.+1) * vec_inf_norm v)%Re.
Proof.
unfold vec_norm2, vec_inf_norm.
match goal with |-context[(_ <= _ * ?a)%Re]=>
  replace a with (sqrt (Rsqr a)) 
end.
+ rewrite -sqrt_mult_alt.
  - admit.
  - apply pos_INR.
+ apply sqrt_Rsqr. apply /RleP. apply bigmax_le_0.
  - apply /RleP. apply Rle_refl.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    apply /RleP. apply Rabs_pos.
Admitted.



