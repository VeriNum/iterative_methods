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

Lemma R0_no_Rabs:
  forall x:R, 
  Rabs x <> 0%Re -> x <> 0%Re.
Proof.
intros. 
pose proof (Rcase_abs x). destruct H0.
+ nra.
+ assert (x = 0%Re \/ (0 < x)%Re). nra.
  destruct H0.
  - rewrite H0 in H. rewrite Rabs_R0 in H. nra.
  - nra.
Qed.


Lemma Rabs_sub: 
  forall x y:R,
  (Rabs x - Rabs y <= Rabs (x + y))%Re.
Proof.
intros.
assert ((x + y)%Re = (x - (-y))%Re). nra.
rewrite H.
rewrite -[in X in (_ - X <= _)%Re]Rabs_Ropp.
apply Rabs_triang_inv.
Qed.

Search "Rabs".

(*
Lemma Rabs_ineq_filter_abstract I r (P: pred I) (E1: I -> R):
  Rabs (\big[+%R/0]_(i <-r | P i) E1 i) <= \big[+%R/0]_(i <-r | P i) (Rabs (E1 i)).
Proof.
intros.
apply /RleP. apply big_rec.
+ admit.
+ intros.


 auto.


apply big_ind2.
+ nra.
+ intros. rewrite -!RplusE. by apply Rplus_le_compat.
+ apply leE12.
Qed.

*)

Lemma Rabs_ineq_filter {n:nat} (f : 'I_n.+1 -> R) P:
  Rabs (\sum_(j < n.+1 | P j) f j) <= \sum_(j < n.+1 | P j) (Rabs (f j)).
Proof.
intros. rewrite big_mkcond /=.
rewrite big
induction n.
+ simpl. rewrite !big_ord_recr //= !big_ord0 !add0r //=.
+ simpl. rewrite big_ord_recr //=.
  assert (\sum_(j < n.+2) Rabs (f j) = 
            \sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) + Rabs (f ord_max)).
  { by rewrite !big_ord_recr//=. } rewrite H. 
  apply /RleP. rewrite -!RplusE.
  apply Rle_trans with 
  (Rabs (\sum_(i < n.+1) f (widen_ord (leqnSn n.+1) i)) +
    Rabs (f ord_max))%Re.
  - apply Rabs_triang.
  - apply Rplus_le_compat_r. apply /RleP. by apply IHn.
Qed.
 *) 

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
  contradict H1.
  apply /eqP. apply /cV0Pn.
  exists k. rewrite !mxE. apply /eqP.
  apply R0_no_Rabs.
  assert (forall x:R, (0 < x)%Re -> x <> 0%Re).
  { intros. nra. } apply H1.
  rewrite (bigD1 k) /=.
  eapply Rlt_le_trans; last by apply Rabs_sub.
  rewrite -RmultE. rewrite Rabs_mult.
  eapply Rlt_le_trans.
  admit.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar. apply /RleP. apply Rabs_ineq.
  Search ( - _ <= - _)%Re.
  





admit.

Admitted.





End WITH_NANS.