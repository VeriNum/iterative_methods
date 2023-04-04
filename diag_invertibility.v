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

Lemma transpose_idempotent {m n:nat} (A: 'M[R]_(m,n)):
  A = (A^T)^T.
Proof.
apply matrixP. unfold eqrel. intros.
by rewrite !mxE. 
Qed.

Lemma vec_norm_implies_vec_zero {n: nat}:
  forall v: 'cV[R]_n.+1,
  vec_inf_norm v = 0%Re ->
  (forall i, Rabs (v i ord0) = 0%Re).
Proof.
intros.
apply Rge_ge_eq in H.
apply Rge_ge_eq.
destruct H as [Ha Hb].
split.
+ apply Rle_ge. apply Rabs_pos.
+ apply Rle_ge. apply Rge_le in Hb.
  unfold vec_inf_norm in Hb.
  pose proof bigmax_le_implies.
  specialize (H 0%Re [seq Rabs (v i 0)
           | i <- enum 'I_n.+1] 0%Re).
  rewrite size_map size_enum_ord in H.
  assert ((0 < n.+1)%nat). by [].
  specialize (H H0  Hb i).
  assert ((i < n.+1)%nat). by apply ltn_ord.
  specialize (H H1). rewrite seq_equiv in H.
  rewrite nth_mkseq in H. rewrite inord_val in H.
  apply H. apply ltn_ord.
Qed.


Local Open Scope R_scope.
Lemma bigmax_destruct (a x0:R) s:
  bigmaxr x0 (a :: s) = a \/ 
  bigmaxr x0 (a :: s) = bigmaxr x0 s.
Admitted.



Lemma bigmax_not_0_implies_aux (x0:R) s:
  (0 < size s)%nat ->
  (exists i, (i < size s)%nat /\
             seq.nth x0 s i = bigmaxr x0 s).
Proof.
intros.
induction s.
+ by simpl in H.
+ pose proof (bigmax_destruct a x0 s).
  destruct H0.
  - exists 0%nat. simpl. split.
    by []. by rewrite H0.
  - assert (s = [::] \/ s != [::]).
    { destruct s.
      + by left.
      + by right.
    } destruct H1.
    * rewrite H1. exists 0%nat.
      simpl. split. by []. by rewrite bigmaxr_un.
    * assert ((0 < size s)%nat).
      { destruct s. by []. by simpl. } specialize (IHs H2).
      destruct IHs as [i [Hsize IHs]].
      exists i.+1. split.
      ++ simpl. by []. 
      ++ simpl. by rewrite H0.
Qed. 
  
Lemma bigmax_not_0_implies (x0:R) s:
  bigmaxr x0 s <> x0 ->
  (exists i, (i < size s)%nat /\
             seq.nth x0 s i = bigmaxr x0 s /\
             seq.nth x0 s i <> x0).
Proof.
intros.
assert (s = [::] \/ s != [::]).
{ destruct s.
  + by left.
  + by right.
} destruct H0.
+ rewrite H0 in H. rewrite bigmaxr_nil in H.
  by contradict H.
+ assert ((0 < size s)%nat).
  { destruct s. by []. by simpl. } 
  pose proof (bigmax_not_0_implies_aux x0 s H1).
  destruct H2 as [i [Hsize H2]].
  exists i. split.
  apply Hsize. split.
  apply H2. by rewrite H2.
Qed.



pose proof eq_bigmax_cond.


assert (exists i, 



pose proof eq_bigmax.
specialize (X 








induction s.

+ simpl. rewrite bigmaxr_nil in H. 
  contradict H. reflexivity.
+ assert (bigmaxr x0 (a :: s) <> x0 ->
            bigmaxr x0 s <> x0 \/ a <> x0).
  { admit. } specialize (H0 H).
  destruct H0.
  - specialize (IHs H0). 
    destruct IHs as [i [Hsize IHs]].
    exists i. split. 
    * apply ltn_trans with (size s); first by [].
      simpl. apply ltnSn.
    * simpl.







 rewrite /bigmaxr. 
  exists 0%nat. split.
  - by simpl. 
  - simpl. 







rewrite big_cons //=.
  assert (s = [::] \/ s != [::]).
  { destruct s.
    + by left.
    + by right.
  } destruct H0.
  - rewrite H0 //=. rewrite H0 //= in H.
    rewrite big_nil. exists 0%nat.
    intros. simpl. rewrite bigmaxr_un in H.
    split. by [].
    split;try apply H. rewrite -RmaxE.
    symmetry. apply Rmax_left. apply Rle_refl.
  - assert (s = seq.head x0 s :: behead s).
    { by apply s_destruct. }
    assert (bigmaxr x0 (a :: s) <> x0 ->
            bigmaxr x0 s <> x0 /\ a <> x0).
    { admit. } specialize (H2 H). 
    destruct H2 as [H2 Ha].
    specialize (IHs H2). destruct IHs as [i [Hsize IHs]].
    exists i. split.
    * apply ltn_trans with (size s). apply Hsize.
      apply ltnSn.
    * simpl. 
      assert (i = 0%nat \/ (0 < i)%nat). by admit.
      destruct H3.
      ++ rewrite H3. simpl. split; try apply Ha.
         admit.
      ++ 



    rewrite H1. rewrite bigrmax_dflt. rewrite -H1.
    assert (bigmaxr x0 (a :: s) = Num.max a (bigmaxr x0 s)).
    { rewrite /bigmaxr. rewrite H1. simpl. rewrite -/bigmaxr.
      rewrite bigmaxr_cons.
      rewrite [in LHS]bigrmax_dflt.


 rewrite bigmaxr_cons.
      rewrite -H1.



            Num.max a
                (\big[Num.max/a]_(j <- 
                 (seq.head x0 s :: behead s)) j)).
    { rewrite /bigmaxr. rewrite H1. rewrite bigrmax_dflt.
      rewrite -H1. simpl.


    rewrite /bigmaxr in H.
    rewrite H1 in H. 
    rewrite bigrmax_dflt in H.
    rewrite le_maxr. apply /orP.
    specialize (H0 0%N). simpl in H0.
    left. by apply H0.




specialize (H0 0%N).
    assert ((0 < 1)%N). { by []. } specialize (H0 H2).
    simpl in H0. rewrite -RmaxE. rewrite Rmax_left.
    * by [].
    * nra.
*)
Admitted.
Close Scope R_scope.


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

Lemma vec_norm_not_zero_implies {n:nat}:
  forall v: 'cV[R]_n.+1,
  vec_inf_norm v <> 0%Re ->
  exists k, Rabs (v k ord0) = vec_inf_norm v /\
            v k ord0 <> 0%Re.
Proof.
intros. unfold vec_inf_norm in H.
pose proof  bigmax_not_0_implies.
specialize (H0 0%Re [seq Rabs (v i ord0)
                          | i <- enum 'I_n.+1] H).
rewrite size_map size_enum_ord in H0.
destruct H0 as [i [Hsize H0]].
exists (@inord n i). 
unfold vec_inf_norm.
rewrite seq_equiv in H0. rewrite nth_mkseq in H0; last by apply Hsize.
destruct H0 as [H0a H0b].
split.
+ rewrite seq_equiv. apply H0a.
+ by apply R0_no_Rabs.
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


Lemma Rabs_ineq_filter {n:nat} (f : 'I_n.+1 -> R) P:
  (Rabs (\sum_(j < n.+1 | P j) f j) <= \sum_(j < n.+1 | P j) (Rabs (f j)))%Re.
Proof.
intros. rewrite big_mkcond /=.
rewrite [in X in (_ <= X)%Re]big_mkcond /=.
induction n.
+ simpl. rewrite !big_ord_recr //= !big_ord0.
  rewrite -!RplusE. rewrite !Rplus_0_l.
  case: (P ord_max).
  - apply Rle_refl.
  - rewrite Rabs_R0. apply Rle_refl.
+ simpl. rewrite big_ord_recr //=.
  rewrite [in X in (_ <= X)%Re]big_ord_recr //=.
  rewrite -!RplusE.
  eapply Rle_trans. apply Rabs_triang.
  apply Rplus_le_compat.
  - apply IHn.
  - case: (P ord_max).
    * apply Rle_refl.
    * rewrite Rabs_R0. apply Rle_refl.
Qed.

Lemma pos_to_gt: 
  forall x:R, x <> 0%Re -> (0 <= x)%Re -> (0 < x)%Re.
Proof.
intros.
assert (x = 0%Re \/ (0 < x)%Re). nra.
destruct H1.
+ rewrite H1 in H. nra.
+ nra.
Qed.


Lemma Rabs_0_implies_0: 
  forall x:R, 
  Rabs x = 0%Re -> x = 0%Re.
Proof.
intros.
pose proof Rcase_abs. specialize (H0 x).
destruct H0.
+ rewrite Rabs_left in H; nra. 
+ rewrite Rabs_right in H; nra.
Qed.


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
  by apply Rabs_0_implies_0.
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
  eapply Rlt_le_trans; last by 
  (apply Rplus_le_compat_l;
    apply Ropp_le_contravar; apply Rabs_ineq_filter).
  assert (\sum_(j < n.+1 | (fun j0 : 'I_n.+1 =>
                    j0 != k) j)
             Rabs ((fun j0 : 'I_n.+1 =>
                        FT2R_mat A k j0 * v_c j0 0) j) = 
          \sum_(j < n.+1 | j != k) (Rabs (FT2R_mat A k j) * Rabs (v_c j ord0))%Re).
  { apply eq_big. by []. intros. rewrite -RmultE. 
    by rewrite Rabs_mult.
  } rewrite H3. rewrite Habs.
  apply Rlt_le_trans with 
  (Rabs (FT2R_mat A k k) * vec_inf_norm v_c -
   (\sum_(j < n.+1 | j != k) (Rabs (FT2R_mat A k j) *
                                  vec_inf_norm v_c)%Re))%Re.
  - rewrite -big_distrl /=. rewrite -RmultE.
    rewrite -Rmult_minus_distr_r.
    apply Rmult_lt_0_compat.
    * specialize (H k). apply Rlt_Rminus.
      apply Rgt_lt. apply H.
    * apply pos_to_gt. apply H2.
      apply /RleP. apply vec_norm_pd.
  - apply Rplus_le_compat_l. apply Ropp_le_contravar.
    apply /RleP. apply big_sum_ge_ex_abstract.
    intros. apply Rmult_le_compat_l. apply Rabs_pos.
    unfold vec_inf_norm.
    apply Rle_trans with 
    [seq Rabs (v_c i0 0)
      | i0 <- enum 'I_n.+1]`_i.
    * rewrite seq_equiv. rewrite nth_mkseq; last by apply ltn_ord.
      rewrite inord_val. apply Rle_refl.
    * apply /RleP. 
      apply (@bigmaxr_ler _ 0%Re [seq Rabs (v_c i0 0)
                                    | i0 <- enum 'I_n.+1] i).
      rewrite size_map size_enum_ord. apply ltn_ord.
  - auto.
Qed.

End WITH_NANS.