Require Import vcfloat.VCFloat vcfloat.FPStdLib.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp Require Import Rstruct.
Require Import fma_real_func_model fma_floating_point_model .
Require Import inf_norm_properties common.

Require Import Coq.Lists.List. 
Import ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lemmas.
Require Import finite_lemmas_additional. 
Require Import fma_jacobi_forward_error. 
Require Import float_acc_lems.
From Coquelicot Require Import Coquelicot.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Section WITH_NANS.

Context {NANS: FPCore.Nans}.

(** Define the solution vector at k-th iteration **)
Fixpoint x_k {n:nat} (k: nat) 
  (x0 b : 'cV[R]_n.+1) (A: 'M[R]_n.+1):= 
  match k with 
  | O => x0
  | p.+1 => x_fix (x_k p x0 b A ) b A
  end.

Lemma Rbar_le_real:
  forall (x y :R),
  Rbar_le x y ->
  (x <= y)%Re.
Proof.
intros. 
by unfold Rbar_le in H.
Qed.

Lemma matrix_norm_A2_rel {t: FPStdLib.type} {n:nat}
  (A: 'M[ftype t]_n.+1):
  (matrix_inf_norm
   (A2_J_real (FT2R_mat A)) <=
 matrix_inf_norm (FT2R_mat (A2_J A)))%Re.
Proof.
assert (A2_J_real (FT2R_mat A) = 
        FT2R_mat (A2_J A)).
{ apply /matrixP. unfold eqrel. intros. rewrite !mxE.
  case: (x == y :> nat); simpl; nra.
} rewrite H; nra.
Qed.


Lemma bpow_fprec_lb_strict t : 
(2 < bpow Zaux.radix2 (fprec t))%Re.
Proof. 
pose proof fprec_gt_one t.
eapply Rle_lt_trans with (bpow Zaux.radix2 1).
unfold bpow; simpl; nra.
apply bpow_lt; lia.
Qed.

Local Open Scope Z_scope.
Lemma default_abs_ub_strict t :
(default_abs t < 1)%Re.
Proof.
unfold default_abs.
pose proof bpow_gt_0 Zaux.radix2 (femax t).
pose proof bpow_gt_0 Zaux.radix2 (fprec t).
replace (3 - femax t - fprec t)%Z with (3 +- femax t +- fprec t)%Z by lia.
rewrite !bpow_plus.
rewrite <- !Rmult_assoc.
replace (/ 2 * bpow Zaux.radix2 3)%Re with 4%Re; [|simpl;nra].
rewrite !bpow_opp !Rcomplements.Rlt_div_r. 
field_simplify; try nra.
assert ( (2 * 2 < (/ / bpow Zaux.radix2 (fprec t)) *(/
                / bpow Zaux.radix2 (femax t)))%Re ->
        (2 <
           1 / / bpow Zaux.radix2 (fprec t) /
           / bpow Zaux.radix2 (femax t) / 2)%Re).
{ intros. nra. } apply H1. repeat (rewrite Rinv_involutive; try nra).
apply Rmult_lt_compat; try nra.
apply bpow_fprec_lb_strict.
apply Rlt_le_trans with 4%Re.
nra. apply bpow_femax_lb.
nra. 
apply Rlt_gt. apply Rinv_0_lt_compat. apply bpow_gt_0.
apply Rlt_gt. apply Rinv_0_lt_compat. apply bpow_gt_0.
Qed.

Lemma default_rel_ub_strict t :
(default_rel t < 1)%Re.
Proof.
unfold default_rel.
pose proof bpow_gt_0 Zaux.radix2 (fprec t).
rewrite !bpow_plus.
rewrite <- !Rmult_assoc.
rewrite Rmult_comm.
rewrite <- !Rmult_assoc.
replace (bpow Zaux.radix2 1 * / 2)%Re with 1%Re; [|simpl;nra].
rewrite !bpow_opp !Rcomplements.Rlt_div_r. 
field_simplify; try nra.
replace 1%Re with  (bpow Zaux.radix2 0).
apply bpow_lt. apply fprec_gt_0.
simpl; auto.
apply Rlt_gt;
replace (/ bpow Zaux.radix2 (fprec t))%Re with (1 / bpow Zaux.radix2 (fprec t))%Re by nra;
apply Rdiv_lt_0_compat; try nra.
Qed.

Close Scope Z_scope.

Lemma vec_norm_A1_rel {t: FPStdLib.type} {n:nat}
  (A: 'M[ftype t]_n.+1)
(Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
(Ha : forall i j, finite (A i j)):
(vec_inf_norm (A1_diag (FT2R_mat A))  <=
 (vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t) )%Re.
Proof.
  rewrite /vec_inf_norm. apply bigmax_le_0head.
  { rewrite size_map size_enum_ord. by []. }
  2:{ intros. move /mapP in H. destruct H as [i H1 H2]. 
    rewrite H2. apply /RleP. apply Rabs_pos. } 
  intros.
  rewrite seq_equiv. rewrite nth_mkseq;
  last by rewrite size_map size_enum_ord in H.
  rewrite mxE.
  apply Rcomplements.Rle_div_r. apply Rlt_Rminus.
  apply default_rel_ub_strict.
  apply Rcomplements.Rle_minus_l.
  apply Rle_trans with
  [seq Rabs
          (FT2R_mat (A1_inv_J A) i0 0)
      | i0 <- enum 'I_n.+1]`_i.
  - rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    rewrite !mxE.
    pose proof (@Binv_accurate _ t (A (inord i) (inord i)) (Hinv (@inord n i)) (Ha (@inord n i) (@inord n i)) ).
    destruct H0 as [d [e [Hde [Hd [He H0]]]]].
    rewrite H0.
    assert (e = (- - e)%Re). 
    { symmetry. apply Ropp_involutive. } rewrite H1.
    eapply Rle_trans; last by apply Rabs_triang_inv.
    rewrite Rabs_Ropp.
    apply Rplus_le_compat.
    rewrite Rabs_mult. rewrite real_const_1.
    apply Rmult_le_compat_l. apply Rabs_pos.
    assert (d = (- - d)%Re). 
    { symmetry. apply Ropp_involutive. } rewrite H2.
    eapply Rle_trans; try apply Rabs_triang_inv.
    rewrite Rabs_Ropp. rewrite Rabs_R1.
    apply Rplus_le_compat_l. 
    apply Ropp_le_contravar. apply Hd.
    apply Ropp_le_contravar. apply He.
  - apply bigmax_ler_0head.
    { apply /mapP. exists (inord i). apply mem_enum.
      rewrite seq_equiv. rewrite nth_mkseq; 
      last by rewrite size_map size_enum_ord in H. reflexivity. }
    intros. move /mapP in H0. destruct H0 as [i0 H1 H2]. rewrite H2.
    apply /RleP. apply Rabs_pos.
Qed.

Lemma R_def_lt_1_implies {t} {n:nat}
  (A : 'M[ftype t]_n.+1) 
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let A_real := FT2R_mat A in
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
  (vec_inf_norm (A1_diag A_real) *
    matrix_inf_norm (A2_J_real A_real) <1)%Re.
Proof.
intros.
apply Rle_lt_trans with R_def; last by apply H.
unfold R_def. 
assert (A2_J_real A_real = A2_real).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE /=.
  case: (x == y :> nat); simpl; auto.
} rewrite H0. apply Rmult_le_compat_r.
apply /RleP. apply matrix_norm_pd.
by apply vec_norm_A1_rel.
Qed.

Lemma sub_vec_4 {n:nat}:
  forall a b: 'cV[R]_n,
  a = b + (a - b) .
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. 
assert ((a x y + - b x y)%Re = (a x y - b x y)%Re).
{ nra. } rewrite H. 
assert ((b x y + (a x y - b x y))%Re = 
         (a x y + (b x y - b x y))%Re).
{ nra. } rewrite H0. nra.
Qed.

Lemma opp_equiv {n:nat}:
  forall (a b: 'cV[R]_n),
  - (a - b) = (b - a).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE.
rewrite -RoppE -!RminusE. simpl. Lra.nra.
Qed.

Lemma sub_vec_5 {n:nat}:
  forall a b: 'cV[R]_n,
  a - (a - b) = b .
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite -!RminusE. simpl; Lra.nra.
Qed.

Lemma sub_vec_6 {n:nat}:
  forall a : 'cV[R]_n.+1,
  let x0 := \col_(j < n.+1) 0%Re in 
  x0 - a = -a.
Proof.
intros. unfold x0. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -RminusE. rewrite -RoppE.
nra.
Qed.

Lemma add_vec_distr_4 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a - b) - (a - d) = d - b.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. simpl; Lra.nra.
Qed.


Lemma x_minus_xk_norm {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) 
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  let x0 := \col_(j < n.+1) 0%Re in
  let R_def_real := (vec_inf_norm (A1_diag A_real) * 
                       matrix_inf_norm (A2_J_real A_real))%Re in
  (R_def < 1)%Re ->
  A_real \in unitmx ->
  forall k:nat, 
  (vec_inf_norm
   (x_k k x0 b_real A_real - x1) <=
      R_def_real ^ k * vec_inf_norm x1)%Re.
Proof.
intros.
induction k.
+ simpl. rewrite Rmult_1_l. rewrite sub_vec_6.
  rewrite -vec_inf_norm_opp. nra.
+ simpl. rewrite Rmult_assoc.
  apply Rle_trans with 
  (R_def_real * (vec_inf_norm
         (x_k k x0 b_real A_real - x1)))%Re.
  unfold x1, x_fix.
  rewrite diag_matrix_vec_mult_diff.
  eapply Rle_trans. 
  apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
  rewrite -RmultE. rewrite add_vec_distr_4.
  rewrite -mulmxBr.
  eapply Rle_trans. apply Rmult_le_compat_l.
  apply /RleP. apply vec_norm_pd.
  apply /RleP. apply submult_prop.
  rewrite -RmultE. rewrite -Rmult_assoc.
  unfold R_def_real. apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    apply /RleP. apply vec_norm_pd.
    apply /RleP. apply matrix_norm_pd.
  - rewrite [in X in (X <= _)%Re]vec_inf_norm_opp.
    rewrite opp_equiv.
    pose proof (@x_fixpoint n x b_real A_real).
    rewrite [in X in (X <= _)%Re]H1. 
    rewrite [in X in (X <= _)%Re]/x_fix.
    apply Rle_refl.
    rewrite /x. rewrite mulmxA.
    rewrite mulmxV. by rewrite mul1mx.
    apply H0.
    intros. unfold A_real. rewrite mxE.
    by apply BDIV_FT2R_sep_zero.
  - auto.
  - apply Rmult_le_compat_l; last by apply IHk.
    unfold R_def_real. apply Rmult_le_pos.
    apply /RleP. apply vec_norm_pd.
    apply /RleP. apply matrix_norm_pd.
Qed.

Lemma lim_of_x_minus_xk_is_zero {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) 
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  let x0 := \col_(j < n.+1) 0%Re in
  (R_def < 1)%Re ->
  A_real \in unitmx ->
  is_lim_seq
  (fun n0 : nat =>
   (vec_inf_norm (x_k n0 x0 b_real A_real) -
    vec_inf_norm x1)%Re) 0%Re.
Proof.
intros.
remember (vec_inf_norm (A1_diag A_real) * 
              matrix_inf_norm (A2_J_real A_real))%Re as R_def_real.
apply is_lim_seq_abs_0.
apply (@is_lim_seq_le_le
        (fun _ => 0%Re)
        (fun n0 : nat =>
         Rabs (vec_inf_norm  (x_k n0 x0 b_real A_real) -
                  vec_inf_norm x1))
        (fun k: nat => ((R_def_real)^k * vec_inf_norm x1)%Re)).
+ intros. split.
  apply Rabs_pos.
  apply Rle_trans with 
    (vec_inf_norm ((x_k n0 x0 b_real A_real) - x1)).
  - apply Rabs_le.
    split.
    * apply Rminus_plus_le_minus. rewrite Rplus_comm.
      assert (forall x y:R, (x + -y)%Re = (x - y)%Re).
      { intros. nra. } rewrite H1.
      rewrite [in X in (_ - X <= _)%Re]vec_inf_norm_opp.
      rewrite opp_equiv.
      apply /RleP. apply reverse_triang_ineq.
      rewrite sub_vec_5. apply /RleP. apply Rle_refl.
    * apply /RleP. apply reverse_triang_ineq.
      apply /RleP. apply Rle_refl.
  - pose proof (@x_minus_xk_norm t n A b Hinv Ha H H0 n0) .
    unfold x1, x, b_real, A_real, x0.
    rewrite HeqR_def_real. apply H1.
+ apply is_lim_seq_const.
+ assert (0%Re = (0 * vec_inf_norm x1)%Re).
  { nra. } rewrite H1. apply is_lim_seq_mult'.
  apply is_lim_seq_geom.
  rewrite Rabs_right. rewrite HeqR_def_real.
  by apply R_def_lt_1_implies.
  apply Rle_ge. rewrite HeqR_def_real.
  apply Rmult_le_pos.
  apply /RleP. apply vec_norm_pd.
  apply /RleP. apply matrix_norm_pd.
  apply is_lim_seq_const.
Qed.

Lemma sum_part_equiv (a:R) (k:nat) :
  (1 + a * \sum_(j < k) (a^j)%Re)%Re = 
  (\sum_(j < k) (a^j)%Re + a^k)%Re.
Proof.
intros.
induction k.
+ rewrite big_ord0 /= Rmult_0_r. by rewrite Rplus_0_r Rplus_0_l.
+ rewrite big_ord_recr /=. rewrite -!RplusE.
  rewrite Rmult_plus_distr_l.
  assert ((1 + (a * (\sum_(i < k) (a ^ i)%Re) +
               a * a ^ k))%Re = 
          ((1 + a * (\sum_(i < k) (a ^ i)%Re)) + a * a^k)%Re).
  { nra. } rewrite H. rewrite IHk. 
  reflexivity.
Qed.


Lemma upper_bound_xk {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) 
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  let x0 := \col_(j < n.+1) 0%Re in
  let R_def_real := (vec_inf_norm (A1_diag A_real) * 
                       matrix_inf_norm (A2_J_real A_real))%Re in
  let f := (vec_inf_norm (A1_diag A_real) *
                vec_inf_norm b_real)%Re in
  (R_def < 1)%Re ->
  A_real \in unitmx ->
  forall k: nat,
  (vec_inf_norm (x_k k x0 b_real A_real) <=
      f * (\sum_(j < k) (R_def_real ^ j)%Re))%Re.
Proof.
intros.
induction k.
+ simpl. rewrite big_ord0 /= Rmult_0_r.
  assert (vec_inf_norm x0 = 0%Re).
  { unfold vec_inf_norm, x0. apply bigmaxP_0head.
    - by rewrite size_map size_enum_ord.
    - intros. rewrite (@nth_map 'I_n.+1 ord0).
      rewrite !mxE. rewrite Rabs_R0. lra.
      by rewrite size_map in H1.
    - intros. move /mapP in H1. destruct H1 as [i2 H1 H2].
      rewrite H2. apply /RleP. apply Rabs_pos.
    - apply /mapP. exists ord0. apply mem_enum.
      rewrite mxE. rewrite Rabs_R0. auto.
  } rewrite H1. nra.
+ rewrite big_ord_recr /=. rewrite -RplusE.
  unfold x_fix.
  eapply Rle_trans. apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
  rewrite -RmultE. eapply Rle_trans.
  apply Rmult_le_compat_l. 
  apply /RleP. apply vec_norm_pd.
  apply /RleP. apply triang_ineq. rewrite -RplusE.
  rewrite -vec_inf_norm_opp.
  eapply Rle_trans. apply Rmult_le_compat_l.
  apply /RleP. apply vec_norm_pd.
  apply Rplus_le_compat_l. apply /RleP.
  apply submult_prop. rewrite -RmultE.
  rewrite Rmult_plus_distr_l. fold f. 
  rewrite -Rmult_assoc. fold R_def_real.
  eapply Rle_trans. apply Rplus_le_compat_l.
  apply Rmult_le_compat_l. apply Rmult_le_pos.
  apply /RleP. apply vec_norm_pd.
  apply /RleP. apply matrix_norm_pd.
  apply IHk. 
  assert ((f + R_def_real *
            (f * (\sum_(j < k) (R_def_real ^ j)%Re)))%Re = 
          (f * (1 + R_def_real * (\sum_(j < k) (R_def_real ^ j)%Re)))%Re).
  { nra. } rewrite H1. apply Rmult_le_compat_l.
  apply Rmult_le_pos; 
  (apply /RleP; apply vec_norm_pd).
  rewrite sum_part_equiv. apply Rle_refl.
Qed.

(** Lemma sum_bigop_equiv **)
Lemma sum_big_equiv (k:nat) (x:R):
  \sum_(j < k.+1) (x ^ j)%Re = 
  sum_f_R0 (fun j :nat => (x^j)%Re) k.
Proof.
induction k.
+ simpl. rewrite big_ord_recr big_ord0 /=.
  rewrite -RplusE. by rewrite Rplus_0_l.
+ rewrite big_ord_recr /=. rewrite IHk.
  by rewrite -RplusE.
Qed. 


Lemma x_bound_exists {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) 
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
  A_real \in unitmx ->
   (vec_inf_norm x1 <= 
      (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
        vec_inf_norm (b_real)) / (1 - R_def))%Re.
Proof.
intros.
remember (\col_(j < n.+1) 0%Re) as x0.
assert ((Lim_seq (fun k: nat =>  vec_inf_norm (x_k k x0 b_real A_real)))
          = vec_inf_norm x1).
{ apply is_lim_seq_unique.
  apply is_lim_seq_ext with
  (fun k : nat =>
     (vec_inf_norm x1 + 
       (vec_inf_norm
         (x_k k x0 b_real A_real) - vec_inf_norm x1))%Re).
  intros. nra.
  assert (vec_inf_norm x1 = (vec_inf_norm x1 + 0)%Re).
  { nra. } rewrite [in X in (is_lim_seq _ X)]H1.
  apply is_lim_seq_plus'. 
  apply is_lim_seq_const.
  pose proof (@lim_of_x_minus_xk_is_zero t ).
  specialize (H2 n A b Hinv Ha H).
  unfold x1,x , A_real, b_real. rewrite Heqx0.
  apply H2. by fold A_real.
} apply Rbar_le_real.
rewrite -H1.
assert (Lim_seq (fun _ => ((vec_inf_norm (FT2R_mat (A1_inv_J A)) +
    default_abs t) / (1 - default_rel t) *
   vec_inf_norm b_real / (1 - R_def))%Re) = 
      ((vec_inf_norm (FT2R_mat (A1_inv_J A)) +
    default_abs t) / (1 - default_rel t) *
   vec_inf_norm b_real / (1 - R_def))%Re).
{ apply Lim_seq_const. }
rewrite -H2.
apply Lim_seq_le_loc.
remember (vec_inf_norm (A1_diag A_real) * 
              matrix_inf_norm (A2_J_real A_real))%Re as R_def_real.
assert (is_lim_seq (fun k: nat => (R_def_real ^k)%Re) 0%Re).
{ apply is_lim_seq_geom.
  rewrite Rabs_right.
  rewrite HeqR_def_real. by apply R_def_lt_1_implies .
  apply Rle_ge. rewrite HeqR_def_real.
  apply Rmult_le_pos.
  apply /RleP. apply vec_norm_pd.
  apply /RleP. apply matrix_norm_pd.
} apply is_lim_seq_spec in H3.
unfold is_lim_seq' in H3.
assert ((0 < 1)%Re) by nra.
specialize (H3 (mkposreal 1%Re H4)).
unfold eventually in H3. destruct H3 as [N H3].
unfold eventually. exists N. intros.
specialize (H3 n0 H5). simpl in H3.
match goal with |-context[(_ <= (?a * ?b)/?c)%Re]=>
  replace ((a * b)/c)%Re with ((a * /c)*b)%Re by nra
end. 
pose proof (@upper_bound_xk t n A b Hinv Ha H).
fold A_real in H6. specialize (H6 H0 n0).
eapply Rle_trans.
rewrite Heqx0 /b_real. apply H6.
match goal with |-context[(_ <= (?a * /?c) * ?b)%Re]=>
  replace ((a * /c) * b)%Re with (a * (b * /c))%Re by nra
end. rewrite Rmult_assoc.
apply Rmult_le_compat.
apply /RleP. apply vec_norm_pd.
apply Rmult_le_pos. 
apply /RleP. apply vec_norm_pd.
apply /RleP. apply big_ge_0_ex_abstract.
intros. apply /RleP. apply pow_le.
apply Rmult_le_pos.
apply /RleP. apply vec_norm_pd.
apply /RleP. apply matrix_norm_pd.
by apply vec_norm_A1_rel.
apply Rmult_le_compat_l.
apply /RleP. apply vec_norm_pd.
apply Rle_trans with
(/ (1 - vec_inf_norm (A1_diag A_real) *
        matrix_inf_norm (A2_J_real A_real)))%Re.
+ rewrite -HeqR_def_real.
  assert (n0 = 0%nat \/ (0 < n0)%nat).
  { assert ((0 <= n0)%nat). by [].
    rewrite leq_eqVlt in H7.
    assert ((0%nat == n0) \/ (0 < n0)%nat). by apply /orP.
    destruct H8.
    + rewrite eq_sym in H8. left. by apply /eqP.
    + by right.
  } destruct H7.
  - rewrite H7. rewrite big_ord0 /=.
    apply Rlt_le, Rinv_0_lt_compat.
    apply Rlt_Rminus. rewrite HeqR_def_real. by apply R_def_lt_1_implies.
  - assert (n0 = n0.-1.+1).
    { by rewrite prednK. } rewrite H8.
    rewrite sum_big_equiv.
    pose proof (GP_finite R_def_real n0.-1).
    assert (forall x y z:R, (x * (y - 1))%Re  = (z - 1)%Re ->
                         (x * (1 - y))%Re  = (1 - z)%Re).
    { intros. nra. } apply H10 in H9. clear H10.
    apply Rmult_le_reg_r with (1 - R_def_real)%Re.
    apply Rlt_Rminus. rewrite HeqR_def_real. by apply R_def_lt_1_implies.
    rewrite H9. rewrite Rinv_l.
    assert (forall x:R, (0 <= x)%Re -> (1 - x <= 1)%Re).
    { intros. nra. } apply H10.
    apply pow_le.
    rewrite HeqR_def_real.
    apply Rmult_le_pos.
    apply /RleP. apply vec_norm_pd.
    apply /RleP. apply matrix_norm_pd.
    assert (forall x:R, (0 < x)%Re -> x <> 0%Re). 
    { intros. nra. } apply H10.
    apply Rlt_Rminus. rewrite HeqR_def_real. by apply R_def_lt_1_implies.
+ assert ((1 - R_def <= (1 -
                            vec_inf_norm (A1_diag A_real) *
                            matrix_inf_norm (A2_J_real A_real)))%Re).
    { apply Rplus_le_compat_l, Ropp_le_contravar.
      unfold R_def. 
      assert (A2_J_real A_real = A2_real).
      { apply matrixP. unfold eqrel. intros. rewrite !mxE /=.
        case: (x2 == y :> nat); simpl; auto.
      } rewrite H7. apply Rmult_le_compat_r.
      apply /RleP. apply matrix_norm_pd.
      by apply vec_norm_A1_rel.
    }
    destruct H7.
    * apply Rlt_le, Rinv_lt_contravar.
      apply Rmult_lt_0_compat.
      ++ by apply Rlt_Rminus.
      ++ by apply Rlt_Rminus, R_def_lt_1_implies.
      ++ apply H7.
    * rewrite H7. nra.
Qed.

End WITH_NANS.

