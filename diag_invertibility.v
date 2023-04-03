Require Import vcfloat.VCFloat vcfloat.FPLib.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp.analysis Require Import Rstruct.
Require Import fma_is_finite dotprod_model.
Require Import floatlib jacob_list_fun_model.
Require Import fma_real_func_model fma_floating_point_model.
Require Import inf_norm_properties common.
Require Import norm_compat.

Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lemmas.
Require Import fma_dot_acc fma_matrix_vec_mult.
From Flocq Require Import Binary.
Require Import finite_lemmas_additional.
Require Import fma_jacobi_forward_error.
Require Import float_acc_lems.
Require Import vec_sum_inf_norm_rel.
Require Import fma_dot_mat_model.
Require Import jacobi_preconditions.
Require Import bound_on_x.

Section WITH_NANS.

Context {NANS: Nans}.

Lemma transpose_implies {n}:
  forall v1 v2: 'rV[R]_n,
  v1^T = v2^T ->
  v1 = v2.
Proof.
intros.
apply matrixP. unfold eqrel. intros.
apply matrixP in H. unfold eqrel in H.
specialize (H y x).
by rewrite !mxE in H.
Qed.

Lemma transpose_implies_col {n}:
  forall v1 v2: 'rV[R]_n.+1,
  v1 = v2 ->
  v1^T = v2^T.
Proof.
intros.
apply matrixP. unfold eqrel. intros.
apply matrixP in H. unfold eqrel in H.
specialize (H y x). by rewrite !mxE.
Qed.


(*
Lemma vec_is_zero_or_not: 
  forall (n:nat) (x : 'cV[R]_n.+1),
   x = 0 \/ x != 0.
Admitted.
*)

Lemma transpose_idempotent {m n:nat} (A: 'M[R]_(m,n)):
  A = (A^T)^T.
Proof.
apply matrixP. unfold eqrel. intros.
by rewrite !mxE. 
Qed.

Lemma vec_norm_implies_vec_zero {n: nat}:
  forall v: 'cV[R]_n.+1,
  vec_inf_norm v = 0%Re ->
  (forall i, v i ord0 = 0%Re).
Admitted.

Lemma vec_norm_not_zero_implies {n:nat}:
  forall v: 'cV[R]_n.+1,
  vec_inf_norm v <> 0%Re ->
  exists k, Rabs (v k ord0) = vec_inf_norm v /\
            v k ord0 <> 0%Re.
Admitted.


Lemma diagonal_dominance_implies_invertibility {t} {n:nat} 
  (A: 'M[ftype t]_n.+1):
  strict_diagonal_dominance A ->
  (FT2R_mat A) \in unitmx.
Proof.
intros.
rewrite -unitmx_tr.
unfold strict_diagonal_dominance in H.
rewrite -row_free_unit.
apply inj_row_free. intros.
pose proof (@transpose_implies_col n ).
specialize (H1 (v *m (FT2R_mat A)^T) 0 H0).
rewrite trmx_mul in H1.
rewrite -transpose_idempotent in H1.
apply transpose_implies.
remember (v^T) as v_c.
rewrite -Heqv_c. rewrite trmx0.
rewrite -Heqv_c trmx0 in H1.
assert (vec_inf_norm v_c = 0%Re \/ vec_inf_norm v_c <> 0%Re).
{ nra. } destruct H2.
+ apply matrixP. unfold eqrel. intros.
  pose proof (@vec_norm_implies_vec_zero n v_c H2 x).
  rewrite !mxE. 
  assert (y = ord0). by apply ord1. rewrite H4.
  apply H3.
+ pose proof (@vec_norm_not_zero_implies n v_c H2).
  destruct H3 as [k [Habs Hneq0]].
  





admit.

Admitted.





End WITH_NANS.