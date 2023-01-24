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


Lemma sum_const {n:nat} (a:R): 
  \sum_(j < n) a = (INR n * a)%Re.
Proof.
induction n.
+ rewrite big_ord0 /=. by rewrite RmultE mul0r.
+ rewrite big_ord_recr. rewrite IHn.
  rewrite -addn1. rewrite plus_INR /=.
  rewrite Rmult_plus_distr_r. rewrite -RplusE. nra.
Qed. 


Lemma norm2_inf_norm_compat {n:nat} (v : 'cV[R]_n.+1):
  (vec_norm2 v <= sqrt (INR n.+1) * vec_inf_norm v)%Re.
Proof.
unfold vec_norm2, vec_inf_norm.
match goal with |-context[(_ <= _ * ?a)%Re]=>
  replace a with (sqrt (Rsqr a)) 
end.
+ rewrite -sqrt_mult_alt.
  - apply sqrt_le_1_alt . rewrite -sum_const .
    apply /RleP. apply big_sum_ge_ex_abstract.
    intros. rewrite Rsqr_abs. apply  Rsqr_incr_1.
    * apply Rle_trans with 
      [seq Rabs (v i0 0) | i0 <- enum 'I_n.+1]`_i.
      ++ rewrite seq_equiv. rewrite nth_mkseq. 
         rewrite inord_val. apply Rle_refl.
         apply ltn_ord.
      ++ apply /RleP. 
         apply (@bigmaxr_ler _ 0%Re 
                    [seq Rabs (v i0 0) | i0 <- enum 'I_n.+1] i).
    * rewrite size_map size_enum_ord. apply ltn_ord.
    * apply Rabs_pos.
  - apply /RleP. apply bigmax_le_0. apply /RleP. apply Rle_refl.
    intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H0.
    apply /RleP. apply Rabs_pos.
  - apply pos_INR.
+ apply sqrt_Rsqr. apply /RleP. apply bigmax_le_0.
  - apply /RleP. apply Rle_refl.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    apply /RleP. apply Rabs_pos.
Qed.

Require Import floatlib fma_floating_point_model common fma_dot_acc float_acc_lems dotprod_model.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

(*** error between norm2 float and norm2 real **)
Lemma norm2_error {t} {NANS: Nans} (v : vector t):
  let n := (length v).-1 in
  let v_inj := FT2R_mat (vector_inj v n.+1) in
  Rabs (FT2R (norm2 v) - (vec_norm2 v_inj)) <=  g t (length v) * (vec_norm2 v_inj) + g1 t (length v) (length v - 1).
Proof.
Admitted.



