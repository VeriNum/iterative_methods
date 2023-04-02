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
From Coquelicot Require Import Coquelicot.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Section WITH_NANS.

Context {NANS: Nans}.


(** Check (series (fun n: nat => (vec_inf_norm x1))). **)


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

Lemma matrix_norm_A2_rel {t: type} {n:nat}
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

Lemma vec_norm_A1_rel {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1)
(Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
(Ha : forall i j, finite (A i j)):
(vec_inf_norm (A1_diag (FT2R_mat A))  <=
 (vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t) )%Re.
Proof.
unfold vec_inf_norm.
apply bigmax_le.
+ by rewrite size_map size_enum_ord.
+ intros.
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
  - apply /RleP.
    apply (@bigmaxr_ler _ 0%Re [seq Rabs
                                   (FT2R_mat (A1_inv_J A) i0 0)
                               | i0 <- enum 'I_n.+1] i).
    rewrite size_map size_enum_ord.
    by rewrite size_map size_enum_ord in H.
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
rewrite -RoppE -!RminusE. nra.
Qed.

Lemma sub_vec_5 {n:nat}:
  forall a b: 'cV[R]_n,
  a - (a - b) = b .
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite -!RminusE. nra.
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

(** Remove this later **)
Lemma vec_inf_norm_diag_matrix_vec_mult_R {n:nat} (v1 v2 : 'cV[R]_n.+1):
  vec_inf_norm (diag_matrix_vec_mult_R v1 v2) <= 
  vec_inf_norm v1 * vec_inf_norm v2.
Proof.
unfold vec_inf_norm, diag_matrix_vec_mult_R.
rewrite -bigmaxr_mulr.
+ apply /RleP. apply bigmax_le.
  - by rewrite size_map size_enum_ord.
  - intros. rewrite seq_equiv. rewrite nth_mkseq; 
    last by rewrite size_map size_enum_ord in H.
    apply Rle_trans with 
    [seq (bigmaxr 0%Re
           [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
         Rabs (v2 i0 0))%Ri
      | i0 <- enum 'I_n.+1]`_i.
    * assert ([seq bigmaxr 0%Re
                    [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
                  Rabs (v2 i0 0)
                | i0 <- enum 'I_n.+1] = 
               mkseq (fun i: nat => bigmaxr 0%Re
                            [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
                            Rabs (v2 (@inord n i) 0))
                             n.+1).
      { by rewrite !seq_equiv. } rewrite H0.
      rewrite nth_mkseq; 
      last by rewrite size_map size_enum_ord in H.
      rewrite !mxE. rewrite -!RmultE. rewrite Rabs_mult.
      rewrite !nth_vec_to_list_real; try rewrite inord_val.
      ++ apply Rmult_le_compat_r; try apply Rabs_pos.
         apply Rle_trans with 
         [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1]`_i.
         -- rewrite seq_equiv. rewrite nth_mkseq; 
            last by rewrite size_map size_enum_ord in H.
            apply Rle_refl.
         -- apply /RleP.
            apply (@bigmaxr_ler _ 0%Re [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] i).
            rewrite size_map size_enum_ord.
            by rewrite size_map size_enum_ord in H.
      ++ by rewrite size_map size_enum_ord in H.
      ++ by rewrite size_map size_enum_ord in H.
    * apply /RleP.
      apply (@bigmaxr_ler _ 0%Re [seq bigmaxr 0%Re
                     [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
                   Rabs (v2 i0 0)
                 | i0 <- enum 'I_n.+1] i).
       rewrite size_map size_enum_ord.
       by rewrite size_map size_enum_ord in H.
+ apply bigmax_le_0.
  - apply /RleP. apply Rle_refl.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    apply /RleP. apply Rabs_pos.
Qed.

Lemma add_vec_distr_4 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a - b) - (a - d) = d - b.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.

(** Remove this as well **)
Lemma x_fixpoint {n:nat} x b (A: 'M[R]_n.+1):
  A *m x = b ->
  (forall i, A i i <> 0%Re) ->
  x = x_fix x b A.
Proof.
intros.
unfold x_fix. unfold diag_matrix_vec_mult_R.
apply /matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite !nth_vec_to_list_real.
+ rewrite !mxE. 
  assert (x x0 y = ((1 / A (inord x0) (inord x0)) *
                    (A (inord x0) (inord x0) * x x0 y))%Re).
  { assert (((1 / A (inord x0) (inord x0)) *
                    (A (inord x0) (inord x0) * x x0 y))%Re = 
             ((A (inord x0) (inord x0) * / A (inord x0) (inord x0))*
              x x0 y)%Re).
    { nra. } rewrite H1. rewrite Rinv_r.
    nra.  apply H0.
  } rewrite H1.
  assert ((((A (inord x0) (inord x0)) * x x0 y))%Re  = 
           (b (inord x0) ord0 -
              \sum_j A2_J_real (A) (inord x0) j * x j ord0)%Re).   
  { assert (forall x y z:R, (x + y = z)%Re -> (x = z - y)%Re).
    { intros. nra. } apply H2.
    assert (( (A (inord x0) (inord x0)) * x x0 y +
              \sum_j A2_J_real A (inord x0) j * x j ord0)%Re = 
              \sum_j (A x0 j * x j ord0)%Re).
    { unfold A2_J_real. rewrite [in RHS](bigD1 x0) /=.
      rewrite inord_val. 
      assert (y = ord0). { by apply ord1. } rewrite H3. 
      apply Rplus_eq_compat_l. 
      assert (\sum_(i < n.+1 | i != x0)
                    (A x0 i * x i ord0)%Re = 
               \sum_(i < n.+1)
                   (if (~~ (i == x0 :> nat)) then 
                      (A x0 i * x i ord0)%Re else 0%Re)).
      { by rewrite big_mkcond /=. } rewrite H4.
      apply eq_big.
      by []. intros. rewrite !mxE. rewrite eq_sym.
      destruct (i == x0 :>nat).
      + simpl. by rewrite mul0r.
      + simpl. by rewrite -RmultE.
      + by [].
    } rewrite H3. apply matrixP in H. unfold eqrel in H.
    specialize (H x0 y). rewrite !mxE in H.
    assert (y = ord0). { by apply ord1. } rewrite H4 in H.
    rewrite inord_val. by apply H.
  } rewrite H2. by [].
+ apply ltn_ord.
+ apply ltn_ord.
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

(** lemma on bound for ||x_k|| **)
Lemma lim_xk_is_bounded {t} {n:nat}
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
  is_lim_seq
    (fun k : nat =>
     vec_inf_norm
       (x_k k x0 b_real A_real))
    (vec_inf_norm (A1_diag A_real) *
     vec_inf_norm b_real /
     (1 -
      vec_inf_norm (A1_diag A_real) *
      matrix_inf_norm
        (A2_J_real A_real)))%Re.
Proof.
intros.
remember (vec_inf_norm (A1_diag A_real) * 
          vec_inf_norm (b_real))%Re as f.
apply (@is_lim_seq_le_le_loc
        (fun _ => (vec_inf_norm (A1_diag A_real) *
                     vec_inf_norm b_real /
                     (1 -
                      vec_inf_norm (A1_diag A_real) *
                      matrix_inf_norm (A2_J_real A_real)))%Re)
        (fun k : nat => vec_inf_norm (x_k k x0 b_real A_real))
        (fun k: nat => (f * \sum_(j < k) ((R_def_real)^j)%Re)%Re)).
+ assert (is_lim_seq (fun k: nat => (R_def_real ^k)%Re) 0%Re).
  { apply is_lim_seq_geom.
    rewrite Rabs_right.
    unfold R_def_real. by apply R_def_lt_1_implies .
    apply Rle_ge. unfold R_def_real.
    apply Rmult_le_pos.
    apply /RleP. apply vec_norm_pd.
    apply /RleP. apply matrix_norm_pd.
  } 




admit.
+ rewrite Heqf. apply is_lim_seq_const.
+ apply is_lim_seq_mult'.
  apply is_lim_seq_const.
  fold R_def_real.
  assert ((/ (1 - R_def_real))%Re = ((1 - 0) * (/ (1 - R_def_real)))%Re) by nra.
  rewrite H1.
  apply is_lim_seq_ext with
  (fun n0 : nat =>
    ((1 - R_def_real^n0) * (/ (1 - R_def_real)))%Re).
  - intros. admit.
  - apply is_lim_seq_mult'.
    apply is_lim_seq_minus'.
    apply is_lim_seq_const.
    apply is_lim_seq_geom.
    rewrite Rabs_right.
    unfold R_def_real. by apply R_def_lt_1_implies .
    apply Rle_ge. unfold R_def_real.
    apply Rmult_le_pos.
    apply /RleP. apply vec_norm_pd.
    apply /RleP. apply matrix_norm_pd.
    apply is_lim_seq_const.

Admitted.
        








assert ((vec_inf_norm (A1_diag A_real) *
           vec_inf_norm b_real /
           (1 -
            vec_inf_norm (A1_diag A_real) *
            matrix_inf_norm (A2_J_real A_real)))%Re = 
        ((vec_inf_norm (A1_diag A_real) *
           vec_inf_norm b_real /
           (1 -
            vec_inf_norm (A1_diag A_real) *
            matrix_inf_norm (A2_J_real A_real))) + 0)%Re) by nra.
rewrite H1. clear H1.
apply is_lim_seq_ext with 
(fun k: nat =>
  ((vec_inf_norm (A1_diag A_real) *
   vec_inf_norm b_real /
   (1 -
    vec_inf_norm (A1_diag A_real) *
    matrix_inf_norm (A2_J_real A_real))) + 
    ((vec_inf_norm
     (x_k k x0 b_real A_real)) - (vec_inf_norm (A1_diag A_real) *
       vec_inf_norm b_real /
       (1 -
        vec_inf_norm (A1_diag A_real) *
        matrix_inf_norm (A2_J_real A_real)))))%Re).
+ intros. nra.
+ apply is_lim_seq_plus'.
  apply is_lim_seq_const.
  apply is_lim_seq_abs_0.
  apply (@is_lim_seq_le_le
          (fun _ => 0%Re)
          (fun n0 : nat =>
           Rabs
             (vec_inf_norm
                (x_k n0 x0 b_real A_real) -
              vec_inf_norm (A1_diag A_real) *
              vec_inf_norm b_real /
              (1 -
               vec_inf_norm (A1_diag A_real) *
               matrix_inf_norm
                 (A2_J_real A_real))))
          (fun k: nat =>
            ((1 + (R_def_real)^k) *  
                (vec_inf_norm (A1_diag A_real) *
              vec_inf_norm b_real /
              (1 -
               vec_inf_norm (A1_diag A_real) *
               matrix_inf_norm
                 (A2_J_real A_real))) - 
             (vec_inf_norm (A1_diag A_real) *
              vec_inf_norm b_real /
              (1 -
               vec_inf_norm (A1_diag A_real) *
               matrix_inf_norm
                 (A2_J_real A_real))))%Re)).
  - intros. split. 
    * apply Rabs_pos.
    * apply Rabs_le. split.
      ++ 



admit.
  - apply is_lim_seq_const.
  - admit.


Admitted.

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
assert (Lim_seq
         (fun k : nat =>
          vec_inf_norm
            (x_k k x0 b_real A_real))  = 
        ((vec_inf_norm (A1_diag A_real) * vec_inf_norm b_real) / 
        (1 - vec_inf_norm (A1_diag A_real) * 
              matrix_inf_norm (A2_J_real A_real)))%Re).
{ apply is_lim_seq_unique.
  pose proof (@lim_xk_is_bounded t).
  specialize (H2 n A b Hinv Ha H).
  unfold x1,x , A_real, b_real. rewrite Heqx0.
  apply H2. by fold A_real.
}
rewrite H2.
simpl.
match goal with |-context[((?a * ?b) / ?c <= _)%Re]=>
  replace ((a * b) / c)%Re with ((a * /c) * b)%Re by nra
end.
match goal with |-context[(_ <= (?a * ?b)/?c)%Re]=>
  replace ((a * b)/c)%Re with ((a * /c)*b)%Re by nra
end. apply Rmult_le_compat_r.
+ apply /RleP. apply vec_norm_pd.
+ apply Rmult_le_compat.
  - apply /RleP. apply vec_norm_pd.
  - apply Rlt_le, Rinv_0_lt_compat, Rlt_Rminus.
    by apply R_def_lt_1_implies.
  - by apply vec_norm_A1_rel.
  - assert ((1 - R_def <= (1 -
                            vec_inf_norm (A1_diag A_real) *
                            matrix_inf_norm (A2_J_real A_real)))%Re).
    { apply Rplus_le_compat_l, Ropp_le_contravar.
      unfold R_def. 
      assert (A2_J_real A_real = A2_real).
      { apply matrixP. unfold eqrel. intros. rewrite !mxE /=.
        case: (x2 == y :> nat); simpl; auto.
      } rewrite H3. apply Rmult_le_compat_r.
      apply /RleP. apply matrix_norm_pd.
      by apply vec_norm_A1_rel.
    }
    destruct H3.
    * apply Rlt_le, Rinv_lt_contravar.
      apply Rmult_lt_0_compat.
      ++ by apply Rlt_Rminus.
      ++ by apply Rlt_Rminus, R_def_lt_1_implies.
      ++ apply H3.
    * rewrite H3. nra.
Qed.

End WITH_NANS.








