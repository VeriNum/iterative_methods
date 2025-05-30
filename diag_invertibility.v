Require Import vcfloat.VCFloat vcfloat.FPStdLib.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp Require Import Rstruct.
Require Import fma_real_func_model fma_floating_point_model. 
Require Import inf_norm_properties. 

Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lemmas.
Require Import jacobi_preconditions.

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

Lemma max_order:
  forall x y:R,
  Rmax x y = x \/ Rmax x y = y.
Proof.
intros.
assert ((x <= y)%Re \/ (y <= x)%Re). nra.
destruct H.
+ rewrite Rmax_right. by right. apply H.
+ rewrite Rmax_left. by left. apply H.
Qed.

(* bigmaxr deprecated *)
(* The following three lemmas are moved to lemmas.v *)
(* Lemma bigmax_destruct (a x0:R) s:
  bigmaxr x0 (a :: s) = a \/ 
  bigmaxr x0 (a :: s) = bigmaxr x0 s.
Proof.
assert (s = [::] \/ s != [::]).
{ destruct s.
  + by left.
  + by right.
} destruct H.
+ rewrite H. rewrite bigmaxr_un. by left.
+ assert (s = seq.head x0 s :: behead s).
  { by apply s_destruct. } rewrite H0.
  rewrite bigmaxr_cons. rewrite -H0.
  rewrite -RmaxE. apply max_order.
Qed. *)


(* Lemma bigmax_not_0_implies_aux (x0:R) s:
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
Qed.  *)
  
(* Lemma bigmax_not_0_implies (x0:R) s:
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
Qed. *)

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
  intros. rewrite /vec_inf_norm in H.
  assert (forall x, x \in [seq Rabs (v i ord0) | i <- enum 'I_n.+1] -> 0 <= x).
  { intros. move /mapP in H0. destruct H0 as [i0 H1 H2]. rewrite H2. 
    apply /RleP. apply Rabs_pos. }
  pose proof (@bigmax_not_0_implies_0head 
    [seq Rabs (v i ord0) | i <- enum 'I_n.+1] H0 H).
  destruct H1 as [i [Hsize [H1 H2]]].
  rewrite size_map in Hsize.
  exists (inord i). split.
  + rewrite /vec_inf_norm.
    rewrite -H1 (@nth_map _ ord0); auto. f_equal. f_equal.
    pose proof (@nth_ord_enum n.+1 ord0 (inord i)).
    rewrite -H3. f_equal. rewrite inordK; auto. by rewrite size_enum_ord in Hsize.
  + assert (seq.nth 0%Re [seq Rabs (v i0 ord0) | i0 <- enum 'I_n.+1] i
      = Rabs (v (inord i) ord0)).
    { rewrite (@nth_map _ ord0); auto. f_equal. f_equal.
      rewrite -(@nth_ord_enum n.+1 ord0 (inord i)). f_equal. 
      rewrite inordK; auto. by rewrite size_enum_ord in Hsize. }
    rewrite H3 in H2. apply R0_no_Rabs. apply H2.
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
    * apply bigmax_ler_0head.
      { apply /mapP. exists i. apply mem_enum.
        rewrite (@nth_map _ ord0).
        f_equal. f_equal. rewrite (@nth_ord_enum n.+1 ord0 i). auto.
        rewrite size_enum_ord. apply ltn_ord. }
      intros.  move /mapP in H5. destruct H5 as [x0 H6 H7]. rewrite H7.
      apply /RleP. apply Rabs_pos.
  - auto.
Qed.

End WITH_NANS.