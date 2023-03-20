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

Section WITH_NANS.

Context {NANS: Nans}.


(** bound for ||x|| **)
Lemma x_bound_exists {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) :
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
   (vec_inf_norm x1 <= 
      (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
        vec_inf_norm (b_real)) / (1 - R_def))%Re.
Admitted.

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

Lemma matrix_vec_norm_A1_diag_mult_A {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
(Ha : forall i j, finite (A i j)):
  (vec_inf_norm (A1_diag (FT2R_mat A)) *
     matrix_inf_norm
       (A2_J_real (FT2R_mat A)) <=
  (vec_inf_norm (FT2R_mat (A1_inv_J A)) +
      default_abs t) / (1 - default_rel t) *
      matrix_inf_norm (FT2R_mat (A2_J A)))%Re.
Proof.
apply Rmult_le_compat.
+ apply /RleP. apply vec_norm_pd.
+ apply /RleP. apply matrix_norm_pd.
+ by apply vec_norm_A1_rel .
+ apply matrix_norm_A2_rel.
Qed.


(** relation between the non-computable and computable rho **)
Lemma rho_def_le_alt {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
(Ha : forall i j, finite (A i j)):
  (rho_def A b <= rho_def_alt A b)%Re.
Proof.
unfold rho_def, rho_def_alt.
apply Rplus_le_compat.
+ apply Rplus_le_compat.
  - apply Rmult_le_compat_l.
    * repeat apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
      repeat apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; last by apply g_pos.
         apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos;last by apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         -- apply Rmult_le_pos; first by apply default_rel_ge_0.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
      ++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
    * by apply matrix_vec_norm_A1_diag_mult_A.
  - apply Rmult_le_compat_l.
    * repeat apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
      apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; last by apply g_pos.
         apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos;last by apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         -- apply Rmult_le_pos; first by apply default_rel_ge_0.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
      ++ apply default_abs_ge_0.
    * apply matrix_norm_A2_rel.
+ by apply matrix_vec_norm_A1_diag_mult_A.
Qed.


Lemma rho_1_implies_rho_2 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
  let rho_hat := rho_def_alt A b in 
  (rho_hat < 1)%Re ->
  (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) *
     matrix_inf_norm
       (FT2R_mat (A2_J A)) < 1)%Re.
Proof.
intros. eapply Rle_lt_trans; last by apply H.
unfold rho_hat,rho_def_alt.
match goal with |-context[(_ <= ?a + ?c + ?b)%Re]=>
 replace (a + c + b)%Re with ((a + b) + c)%Re by nra
end.
assert (((vec_inf_norm (FT2R_mat (A1_inv_J A)) +
          default_abs t) /(1 - default_rel t) *
            matrix_inf_norm (FT2R_mat (A2_J A)))%Re = 
        (((vec_inf_norm (FT2R_mat (A1_inv_J A)) +
          default_abs t) /(1 - default_rel t) *
            matrix_inf_norm (FT2R_mat (A2_J A))) + 0)%Re) by nra.
rewrite [in X in (X <= _)%Re]H0.
apply Rplus_le_compat.
+ assert (forall a b:R, (a * b + b = (1 + a)* b)%Re).
  { intros. nra. } rewrite H1.
  assert (((vec_inf_norm (FT2R_mat (A1_inv_J A)) +
            default_abs t) /(1 - default_rel t) *
              matrix_inf_norm (FT2R_mat (A2_J A)))%Re =
              (1 * ((vec_inf_norm (FT2R_mat (A1_inv_J A)) +
                      default_abs t) /(1 - default_rel t) *
                        matrix_inf_norm (FT2R_mat (A2_J A))))%Re).
  { nra. } rewrite [in X in (X <= _)%Re]H2.
  apply Rmult_le_compat_r.
  - repeat apply Rmult_le_pos.
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply /RleP. apply vec_norm_pd.
    apply Rlt_le. apply Rinv_0_lt_compat. apply Rlt_Rminus.
    apply default_rel_ub_strict.
    apply /RleP. apply matrix_norm_pd.
  - assert ((0 <= (((1 + g t n.+1) *
                 (1 + default_rel t) * 
                 g t n.+1 +
                 default_rel t * (1 + g t n.+1) +
                 g t n.+1) * (1 + default_rel t) +
                default_rel t))%Re).
    { apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
      apply Rmult_le_pos.
      + apply Rplus_le_le_0_compat; last by apply g_pos.
        apply Rplus_le_le_0_compat.
        - repeat apply Rmult_le_pos.
          apply Rplus_le_le_0_compat; try nra; try apply g_pos.
          apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
          apply g_pos.
        - apply Rmult_le_pos. apply default_rel_ge_0.
          apply Rplus_le_le_0_compat; try nra; try apply g_pos.
      + apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    }  nra.
+ repeat apply Rmult_le_pos; last by (apply /RleP; apply matrix_norm_pd).
  apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
  apply Rmult_le_pos; last by apply  default_abs_ge_0.
  apply Rplus_le_le_0_compat; try by apply g_pos.
  apply Rplus_le_le_0_compat.
  - repeat apply Rmult_le_pos; last by apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  - apply Rmult_le_pos; first by apply default_rel_ge_0.
    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
Qed.



(** relation between the non-computable and computable d_mag **)
Lemma d_mag_def_le_alt {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
(Ha : forall i j, finite (A i j)):
  let rho_hat := rho_def_alt A b in 
  (rho_hat < 1)%Re ->
  (d_mag_def A b <= d_mag_def_alt A b)%Re.
Proof.
intros ? Hrho.
unfold d_mag_def, d_mag_def_alt.
apply Rplus_le_compat.
+ apply Rplus_le_compat.
  - apply Rplus_le_compat_r. apply Rplus_le_compat.
    * apply Rmult_le_compat_l.
      ++ apply Rplus_le_le_0_compat; try apply default_rel_ge_0.
         apply Rmult_le_pos. apply g_pos.
         apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
      ++ apply Rmult_le_compat_r. apply /RleP. apply vec_norm_pd.
         apply Rplus_le_compat_r. apply Rmult_le_compat_r.
         apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         by apply vec_norm_A1_rel.
    * apply Rmult_le_compat_l.
      ++ repeat apply Rmult_le_pos; try nra; try apply bpow_ge_0; try apply pos_INR.
         apply Rplus_le_le_0_compat; try nra; try apply g_pos.
         apply Rplus_le_le_0_compat; try nra; try apply g_pos.
         apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
      ++ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
         apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         by apply vec_norm_A1_rel.
  - apply Rmult_le_compat_r. apply /RleP. apply vec_norm_pd.
    apply Rplus_le_compat_r. apply Rmult_le_compat_r.
    apply default_rel_ge_0. by apply vec_norm_A1_rel.
+ apply Rmult_le_compat. 
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; try apply default_rel_ge_0.
         apply Rmult_le_pos; last by
         (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
         apply Rplus_le_le_0_compat; last by apply g_pos.
         apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
            apply g_pos.
         -- apply Rmult_le_pos; first by apply default_rel_ge_0.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
      ++ apply Rmult_le_pos. apply /RleP. apply vec_norm_pd.
         apply /RleP. apply matrix_norm_pd.
    * apply Rmult_le_pos; last by (apply /RleP; apply matrix_norm_pd).
      apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
      apply Rmult_le_pos; last by apply default_abs_ge_0.
      apply Rplus_le_le_0_compat; last by apply g_pos.
      apply Rplus_le_le_0_compat.
      ++ repeat apply Rmult_le_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
            apply g_pos.
      ++ apply Rmult_le_pos.
         apply default_rel_ge_0.
         apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  - apply /RleP. apply vec_norm_pd.
  - apply Rplus_le_compat.
    * apply Rmult_le_compat_l.
      ++ apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
         apply Rmult_le_pos; last by 
         (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
         apply Rplus_le_le_0_compat; last by apply g_pos.
         apply Rplus_le_le_0_compat.
         repeat apply Rmult_le_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
            apply g_pos.
         apply Rmult_le_pos.
         apply default_rel_ge_0.
         apply Rplus_le_le_0_compat; try nra; try apply g_pos.
     ++ by apply matrix_vec_norm_A1_diag_mult_A.
   * apply Rmult_le_compat; try (apply /RleP; apply matrix_norm_pd); 
     try apply matrix_norm_A2_rel; try nra.
     apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
     apply Rmult_le_pos; last by apply default_abs_ge_0.
     apply Rplus_le_le_0_compat; last by apply g_pos.
     apply Rplus_le_le_0_compat.
     repeat apply Rmult_le_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
            apply g_pos.
         apply Rmult_le_pos.
         apply default_rel_ge_0.
         apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  - apply x_bound_exists. by apply rho_1_implies_rho_2 with b .
Qed.



Lemma d_mag_def_alt_ge_0 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
   (rho_def_alt A b < 1)%Re ->
   (0 <= d_mag_def_alt A b)%Re.
Proof.
intro Hrho.
unfold d_mag_def_alt.
repeat apply Rplus_le_le_0_compat.
+ repeat try apply Rmult_le_pos; try repeat apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; try apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  - apply default_rel_ge_0.
  - repeat apply Rmult_le_pos.
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0. 
    apply /RleP. apply vec_norm_pd.
    apply Rlt_le. apply Rinv_0_lt_compat. apply Rlt_Rminus.
    apply default_rel_ub_strict.
    apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
  - apply default_abs_ge_0.
  - apply /RleP. apply vec_norm_pd.
+ repeat try apply Rmult_le_pos.
  - apply Rplus_le_le_0_compat. nra. apply g_pos.
  - apply pos_INR.
  - nra.
  - apply bpow_ge_0.
  - apply Rplus_le_le_0_compat. nra. apply g_pos.
  - apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0. 
  - apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply Rmult_le_pos; last by (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
    repeat apply Rmult_le_pos.
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0. 
    apply /RleP. apply vec_norm_pd.
    apply Rlt_le. apply Rinv_0_lt_compat. apply Rlt_Rminus.
    apply default_rel_ub_strict.
+ apply g1_pos.
+ apply Rmult_le_pos; last by (apply /RleP; try apply vec_norm_pd).
  apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
  apply Rmult_le_pos; last by apply default_rel_ge_0.
  repeat apply Rmult_le_pos.
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0. 
    apply /RleP. apply vec_norm_pd.
    apply Rlt_le. apply Rinv_0_lt_compat. apply Rlt_Rminus.
    apply default_rel_ub_strict.
+ repeat apply Rmult_le_pos; try by (apply /RleP; try apply vec_norm_pd).
  repeat apply Rplus_le_le_0_compat.
  - repeat apply Rmult_le_pos.
    * repeat apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
      repeat apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; last by apply g_pos.
         apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos;last by apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         -- apply Rmult_le_pos; first by apply default_rel_ge_0.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
      ++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
    * apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
      apply /RleP. apply vec_norm_pd.
    * apply Rlt_le. apply Rinv_0_lt_compat. 
      apply Rlt_Rminus.  apply default_rel_ub_strict.
    * apply /RleP. apply matrix_norm_pd.
  - repeat apply Rmult_le_pos; last by (apply /RleP; apply matrix_norm_pd).
    repeat apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    repeat apply Rmult_le_pos; last by apply bpow_ge_0.
    * apply Rplus_le_le_0_compat;last by apply g_pos.
      apply Rplus_le_le_0_compat.
      ++ repeat apply Rmult_le_pos;last by apply g_pos.
         apply Rplus_le_le_0_compat; try nra; try apply g_pos.
         apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
      ++ apply Rmult_le_pos; first by apply default_rel_ge_0.
         apply Rplus_le_le_0_compat. nra. apply g_pos.
    * nra.
  - apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply /RleP. apply vec_norm_pd.
  - apply Rlt_le. apply Rinv_0_lt_compat. 
    apply Rlt_Rminus.  apply default_rel_ub_strict.
  - apply Rlt_le. apply Rinv_0_lt_compat.
    apply Rlt_Rminus. by apply rho_1_implies_rho_2 with b.
Qed.



Lemma d_mag_alt_gt_0 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
  (rho_def_alt A b < 1)%Re ->
  (0 < d_mag_def_alt A b)%Re .
Proof.
intro Hrho.
unfold d_mag_def_alt.
apply Rplus_lt_le_0_compat.
+ apply Rplus_lt_le_0_compat.
  - apply Rplus_lt_le_0_compat.
    * apply Rplus_le_lt_0_compat. 
      ++ repeat apply Rmult_le_pos; last by (apply /RleP; apply vec_norm_pd).
         apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
         apply Rmult_le_pos; try by apply g_pos.
         apply Rplus_le_le_0_compat; try nra; try by apply default_rel_ge_0.
         apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
        apply Rmult_le_pos; last by 
        (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
        apply Rmult_le_pos.
        apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
        apply /RleP. apply vec_norm_pd.
        apply Rlt_le, Rinv_0_lt_compat.
        apply Rlt_Rminus. apply default_rel_ub_strict.
      ++ repeat apply Rmult_lt_0_compat; try nra; try apply bpow_gt_0.
         apply Rplus_lt_le_0_compat; try by nra; try by apply g_pos.
         apply g_pos.
         apply lt_0_INR. lia.
         apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
         apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
         apply Rplus_le_lt_0_compat; last by apply default_abs_gt_0.
         apply Rmult_le_pos.
         apply Rmult_le_pos.
         apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
         apply /RleP. apply vec_norm_pd.
         apply Rlt_le, Rinv_0_lt_compat.
         apply Rlt_Rminus. apply default_rel_ub_strict.
         apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    * apply g1_pos.
  - repeat apply Rmult_le_pos; last by (apply /RleP; apply vec_norm_pd).
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply Rmult_le_pos; last by apply default_rel_ge_0.
    apply Rmult_le_pos.
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply /RleP. apply vec_norm_pd.
    apply Rlt_le, Rinv_0_lt_compat.
    apply Rlt_Rminus. apply default_rel_ub_strict.
+ repeat apply Rmult_le_pos.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; try by apply default_rel_ge_0.
         apply Rmult_le_pos; last by 
         (apply Rplus_le_le_0_compat; try nra; try by apply default_rel_ge_0).
         apply Rplus_le_le_0_compat; last by apply g_pos.
         apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos; try by apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         -- apply Rmult_le_pos; first by apply default_rel_ge_0.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
      ++ apply Rmult_le_pos; last by (apply /RleP; apply matrix_norm_pd).
         apply Rmult_le_pos.
         -- apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
            apply /RleP. apply vec_norm_pd.
         -- apply Rlt_le, Rinv_0_lt_compat.
            apply Rlt_Rminus. apply default_rel_ub_strict.
    * apply Rmult_le_pos; last by (apply /RleP; apply matrix_norm_pd).
      apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
      apply Rmult_le_pos; last by apply default_abs_ge_0.
      apply Rplus_le_le_0_compat; last by apply g_pos.
      apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos; try by apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
         -- apply Rmult_le_pos; first by apply default_rel_ge_0.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  - apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply /RleP. apply vec_norm_pd.
  - apply Rlt_le, Rinv_0_lt_compat.
    apply Rlt_Rminus. apply default_rel_ub_strict.
  - apply /RleP. apply vec_norm_pd.
  - apply Rlt_le. apply Rinv_0_lt_compat.
    apply Rlt_Rminus.
    apply rho_1_implies_rho_2  with b. apply Hrho.
Qed.


(** Use: lower case gamma **)

(** relation between non-computable and computable defn of e_o in reals **)
Lemma f_error0_bnd {t: type} {n:nat} (A : 'M[ftype t]_n.+1)
  (b : 'cV[ftype t]_n.+1):
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def :=  (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) *
                    matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
  (@f_error _ _ _ 0 b x0 x A  <=
    vec_inf_norm (FT2R_mat x0) + 
    (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t))
        * vec_inf_norm (b_real)) / (1 - R_def))%Re.
Proof.
intros. 
unfold f_error.
  eapply Rle_trans. apply /RleP. apply triang_ineq .
  rewrite -vec_inf_norm_opp.
  assert (X_m_jacobi 0 x0 b A = x0).
  { by simpl. } rewrite H0. rewrite -RplusE.
  apply Rplus_le_compat_l.
  apply x_bound_exists. apply H.
Qed.

(** Replace Gamma with tau_squared  **)


Lemma diagonal_dominance_implies_invertibility {t} {n:nat} 
  (A: 'M[ftype t]_n.+1):
  strict_diagonal_dominance A ->
  (FT2R_mat A) \in unitmx.
Admitted.

(*** We might not need this ***)
(*
Lemma diagonal_dominance_implies_rho_lt_1 {t} {n:nat} 
  (A: 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1):
  strict_diagonal_dominance A ->
  (rho_def A b < 1)%Re.
Admitted.
*)

(** g  g1  rho d_mag : what do they mean intuitively **)
Lemma d_mag_rel_1 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let rho_hat := rho_def_alt A b in 
  (rho_hat < 1)%Re -> 
  (2 * d_mag_def A b *
   / (1 - rho_def A b) <=
   2 * d_mag_def_alt A b *
   / (1 - rho_def_alt A b))%Re.
Proof.
intros ? Hrho.
apply Rmult_le_compat.
apply Rmult_le_pos. nra. apply d_mag_ge_0.
apply Rlt_le, Rinv_0_lt_compat. 
apply Rlt_Rminus. eapply Rle_lt_trans.
apply rho_def_le_alt; try by []. apply Hrho.
apply Rmult_le_compat_l. nra. by apply d_mag_def_le_alt.
assert ((rho_def A b = rho_def_alt A b)%Re \/
                  (rho_def A b < rho_def_alt A b)%Re).
{ pose proof (@rho_def_le_alt t n A b Hinv Ha).  nra. }
destruct H. 
rewrite H; nra.
apply Rlt_le. apply Rinv_lt_contravar .
apply Rmult_lt_0_compat.
apply Rlt_Rminus. apply Hrho.
apply Rlt_Rminus. eapply Rle_lt_trans.
by apply rho_def_le_alt. apply Hrho.
apply Rplus_le_lt_compat. nra.
by apply Ropp_lt_contravar.
Qed.


Lemma d_mag_rel_2 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let rho_hat := rho_def_alt A b in 
  (rho_hat < 1)%Re -> 
  (1 / (1 - rho_def A b) *
     d_mag_def A b <=
     1 / (1 - rho_def_alt A b) *
     d_mag_def_alt A b)%Re.
Proof.
intros ? Hrho.
apply Rmult_le_compat.
apply Rlt_le.
replace (1 / (1 - rho_def A b))%Re with 
            (/ (1 - rho_def A b))%Re by nra. 
apply Rinv_0_lt_compat. 
apply Rlt_Rminus. eapply Rle_lt_trans.
by apply rho_def_le_alt. apply Hrho.
apply d_mag_ge_0.
assert ((rho_def A b = rho_def_alt A b)%Re \/
                  (rho_def A b < rho_def_alt A b)%Re).
{ pose proof (@rho_def_le_alt t n A b Hinv Ha). nra. }
destruct H. 
rewrite H; nra.
apply Rlt_le. 
replace (1 / (1 - rho_def A b))%Re with 
            (/ (1 - rho_def A b))%Re by nra.
replace (1 / (1 - rho_def_alt A b))%Re with 
            (/ (1 - rho_def_alt A b))%Re by nra.
apply Rinv_lt_contravar .
apply Rmult_lt_0_compat.
apply Rlt_Rminus. apply Hrho.
apply Rlt_Rminus. eapply Rle_lt_trans.
by apply rho_def_le_alt. apply Hrho.
apply Rplus_le_lt_compat. nra.
by apply Ropp_lt_contravar.
by apply d_mag_def_le_alt.
Qed.

 
Lemma input_bound_compute_implies_math {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite  (A i j)):
  let rho_hat := rho_def_alt A b in 
  (rho_hat < 1)%Re -> 
  (0 < f_error 0 b (\col__ Zconst t 0)
         ((FT2R_mat A)^-1 *m  FT2R_mat b) A -
          d_mag_def A b *
       / (1 - rho_def A b))%Re ->
  input_bound_Rcompute A (\col__ Zconst t 0) b ->
  input_bound A (\col__ Zconst t 0) b .
Proof.
intros ? Hrho He0 ? .
repeat split.
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [bnd1 _ ].
  specialize (bnd1 i).
  eapply Rle_lt_trans; last by apply bnd1.
  apply Rmult_le_compat_l. apply Rabs_pos.
  apply Rplus_le_compat.
  - rewrite !Rmult_1_l. apply Rplus_le_compat.
    * apply Rmult_le_compat.
      apply Rplus_le_le_0_compat. nra. by apply rho_ge_0.
      apply Rlt_le. apply He0.
      apply Rplus_le_compat_l. by apply rho_def_le_alt.
      apply Rplus_le_compat. 
      apply f_error0_bnd . by apply rho_1_implies_rho_2 with b.
      apply Ropp_le_contravar.
      apply Rmult_le_pos. apply d_mag_ge_0.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. eapply Rle_lt_trans.
      by apply rho_def_le_alt. apply Hrho.
    * by apply d_mag_rel_1.
  - apply Rmult_le_compat_l. nra.
    apply x_bound_exists. by apply rho_1_implies_rho_2 with b.
+ destruct H as [_[bnd2 _]].
  eapply Rle_lt_trans; last by apply bnd2.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    apply x_bound_exists. by apply rho_1_implies_rho_2 with b.
    rewrite !Rmult_1_l.
    apply f_error0_bnd . by apply rho_1_implies_rho_2 with b.
  - by apply d_mag_rel_2 .
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [_ [_ [bnd3 _]]]. apply bnd3.
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [_[_[_[bnd4 _]]]].
  eapply Rle_lt_trans; last by apply bnd4.
  apply Rplus_le_compat_r. apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat. nra. apply g_pos.
  apply Rmult_le_compat_r.
  - apply /RleP. apply big_ge_0_ex_abstract.
    intros. apply /RleP. apply Rabs_pos.
  - apply Rplus_le_compat.
    * apply Rplus_le_compat.
      apply x_bound_exists. by apply rho_1_implies_rho_2 with b.
      rewrite !Rmult_1_l.
      apply f_error0_bnd . by apply rho_1_implies_rho_2 with b.
    * by apply d_mag_rel_2 .
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [_[_[_[_[bnd5 _]]]]].
  eapply Rle_lt_trans; last by apply bnd5.
  apply Rmult_le_compat_l. apply Rabs_pos.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l. 
  apply Rplus_le_le_0_compat. nra. apply g_pos.
  apply Rmult_le_compat_r.
  - apply /RleP. apply big_ge_0_ex_abstract.
    intros. apply /RleP. apply Rabs_pos.
  - apply Rplus_le_compat.
    * apply Rplus_le_compat.
      apply x_bound_exists. by apply rho_1_implies_rho_2 with b.
      rewrite !Rmult_1_l.
      apply f_error0_bnd . by apply rho_1_implies_rho_2 with b.
    * by apply d_mag_rel_2 .
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [_[_[_[_[_ bnd6]]]]].
  eapply Rle_lt_trans; last by apply bnd6.
  rewrite !Rmult_1_l. 
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    * apply Rmult_le_compat.
      apply Rplus_le_le_0_compat. nra. by apply rho_ge_0.
      apply Rlt_le. apply He0.
      apply Rplus_le_compat_l. by apply rho_def_le_alt.
      apply Rplus_le_compat. 
      apply f_error0_bnd . by apply rho_1_implies_rho_2 with b.
      apply Ropp_le_contravar.
      apply Rmult_le_pos. apply d_mag_ge_0.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. eapply Rle_lt_trans.
      by apply rho_def_le_alt. apply Hrho.
    * by apply d_mag_rel_1.
  - apply Rmult_le_compat_l. nra.
    apply x_bound_exists. by apply rho_1_implies_rho_2 with b.
Qed.

Lemma ln_rho_rel {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  (0 < rho_def_alt A b)%Re ->
  (rho_def_alt A b < 1)%Re ->
  (0 < rho_def A b)%Re ->
(/ ln (1 / rho_def A b) <=
 / ln (1 / rho_def_alt A b))%Re.
Proof.
intros. 
pose proof (@rho_def_le_alt t n A b Hinv Ha).
assert (rho_def A b = rho_def_alt A b \/
        (rho_def A b < rho_def_alt A b)%Re) by nra.
destruct H3. rewrite H3. nra.
apply Rlt_le.
apply Rinv_lt_contravar.
+ apply Rmult_lt_0_compat.
  - rewrite -ln_1. apply ln_increasing. nra.
    replace (1 / rho_def_alt A b)%Re with (/ rho_def_alt A b)%Re by nra.
    replace 1%Re with (/1)%Re by nra.
    apply Rinv_lt_contravar.
    rewrite Rmult_1_r. apply H. apply H0.
  - rewrite -ln_1. apply ln_increasing. nra.
    replace (1 / rho_def A b)%Re with (/ rho_def A b)%Re by nra.
    replace 1%Re with (/1)%Re by nra.
    apply Rinv_lt_contravar.
    rewrite Rmult_1_r. apply H1. 
    apply Rlt_trans with (rho_def_alt A b).
    apply H3.
    apply H0.
+ apply ln_increasing. 
  replace (1 / rho_def_alt A b)%Re with (/ rho_def_alt A b)%Re by nra.
  apply Rinv_0_lt_compat. apply H.
  replace (1 / rho_def_alt A b)%Re with (/ rho_def_alt A b)%Re by nra.
  replace (1 / rho_def A b)%Re with (/ rho_def A b)%Re by nra.
  apply Rinv_lt_contravar. 
  by apply Rmult_lt_0_compat.
  apply H3.
Qed.


Lemma ln_rho_inv_ge_0 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  ( rho_def_alt A b < 1)%Re ->
  (0 < rho_def A b)%Re ->
  (0 <= / ln (1 / rho_def A b))%Re.
Proof.
intros. apply Rlt_le. apply Rinv_0_lt_compat.
rewrite -ln_1. apply ln_increasing.
nra.
replace (1 / rho_def A b)%Re with (/ rho_def A b)%Re by nra.
replace 1%Re with (/1)%Re by nra.
apply Rinv_lt_contravar.
+ by rewrite Rmult_1_r.
+ apply Rle_lt_trans with (rho_def_alt A b).
  by apply rho_def_le_alt.
  apply H.
Qed.
  

Lemma ln_incr (x y:R):
  (0 < x)%Re -> (x <= y)%Re -> (ln x <= ln y)%Re.
Proof.
intros.
assert (x = y \/ (x < y)%Re) by nra.
destruct H1.
+ rewrite H1. nra.
+ apply Rlt_le. by apply ln_increasing.
Qed.


Lemma vec_norm_strong_not_0 {n:nat} (v: 'cV[R]_n.+1):
  (forall i, v i ord0 <> 0%Re) ->
  (0 < vec_inf_norm v)%Re.
Proof.
intros.
unfold vec_inf_norm.
apply Rlt_le_trans with 
[seq Rabs (v i 0) | i <- enum 'I_n.+1]`_0.
+ rewrite seq_equiv. rewrite nth_mkseq; last by [].
  specialize (H (@inord n 0)). by apply Rabs_pos_lt.
+ apply /RleP.
  apply (@bigmaxr_ler _ 0%Re [seq Rabs (v i 0) | i <- enum 'I_n.+1] 0).
  by rewrite size_map size_enum_ord.
Qed.




Lemma tau_sqr_rel{t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (accuracy: ftype t)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A  i j)):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in 
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  ( rho_def_alt A b < 1)%Re -> 
 (FT2R (BMULT accuracy accuracy) >
     g1 t n.+1 (n.+1 - 1)%coq_nat +
     INR n.+1 * (1 + g t n.+1) *
     (g1 t n.+1 (n.+1 - 1)%coq_nat +
      2 * (1 + g t n.+1) * (1 + default_rel t) *
      vec_inf_norm (FT2R_mat (A1_J A)) *
      d_mag * / (1 - rho))²)%Re -> 
  (0 <
   (sqrt
      ((FT2R
          (BMULT accuracy accuracy) -
        g1 t n.+1 (n.+1 - 1)%coq_nat) /
       INR n.+1 / (1 + g t n.+1)) -
    g1 t n.+1 (n.+1 - 1)%coq_nat) /
   (1 + g t n.+1) /
   vec_inf_norm (FT2R_mat (A1_J A)) /
   (1 + default_rel t) -
   2 * d_mag_def A b /
   (1 - rho_def A b))%Re.
Proof.
intros. apply Rlt_Rminus. repeat apply Rdiv_lt_right.
+ apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
+ apply vec_norm_strong_not_0 . intros. rewrite !mxE.
  assert (Hneq: forall i, (FT2R (A i i) <> 0%Re)).
  { intros. by apply BDIV_FT2R_sep_zero. } apply Hneq.
+ apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
+ apply Rcomplements.Rlt_minus_r.
  apply  Rsqr_incrst_0.
  - rewrite Rsqr_sqrt . 
    * repeat apply Rdiv_lt_right.
      apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
      apply lt_0_INR. lia.
      apply Rcomplements.Rlt_minus_r. 
      apply Rgt_lt. unfold rho, d_mag in H0. 
      assert (((2 * d_mag_def A b /
                  (1 - rho_def A b) *
                  (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) *
                  (1 + g t n.+1) +
                  g1 t n.+1 (n.+1 - 1)%coq_nat)² *
                 (1 + g t n.+1) * INR n.+1 +
                 g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
                ((2 * d_mag_def A b * /
                  (1 - rho_def A b) *
                  (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) *
                  (1 + g t n.+1) +
                  g1 t n.+1 (n.+1 - 1)%coq_nat)² *
                 (1 + g t n.+1) * INR n.+1 +
                 g1 t n.+1 (n.+1 - 1)%coq_nat)%Re) by nra.
      rewrite H1. clear H1.
      eapply Rgt_ge_trans. apply H0. apply Rle_ge.
      unfold Rsqr. nra.
    * repeat apply Rmult_le_pos.
      ++ apply Rlt_le. apply Rlt_Rminus.
         eapply Rle_lt_trans; last by apply H0.
         assert (g1 t n.+1 (n.+1 - 1)%coq_nat = 
                  (g1 t n.+1 (n.+1 - 1)%coq_nat + 0)%Re) by nra.
         rewrite [in X in (X <= _)%Re]H1. apply Rplus_le_compat_l.
         apply Rmult_le_pos.
         -- apply Rmult_le_pos. apply pos_INR.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
         -- apply Rle_0_sqr .
      ++ apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR. lia.
      ++ apply Rlt_le, Rinv_0_lt_compat.
         apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
 - apply Rplus_le_le_0_compat; last by apply g1_pos.
   repeat apply Rmult_le_pos; try nra; try apply bpow_ge_0; try apply d_mag_ge_0.
   * apply Rlt_le, Rinv_0_lt_compat. 
     apply Rlt_Rminus.
     apply Rle_lt_trans with (rho_def_alt A b).
      by apply rho_def_le_alt.
      apply H.
   * apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
   * apply /RleP. apply vec_norm_pd.
   * apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  - apply sqrt_pos.
Qed.


Lemma tau_sqr_rel_Rcompute {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (accuracy: ftype t)
  (Hinv: forall i, finite (BDIV (Zconst t 1) (A i i)))
  (Ha : forall i j, finite (A i j)):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in 
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  ( rho_def_alt A b < 1)%Re -> 
  (FT2R (BMULT accuracy accuracy) >
       g1 t n.+1 (n.+1 - 1)%coq_nat +
       INR n.+1 * (1 + g t n.+1) *
       (g1 t n.+1 (n.+1 - 1)%coq_nat +
        2 * (1 + g t n.+1) *
        (1 + default_rel t) *
        vec_inf_norm
          (FT2R_mat (A1_J A)) *
        d_mag_def_alt A b *
        / (1 - rho_def_alt A b))²)%Re ->
  (0 <
     (sqrt
        ((FT2R
            (BMULT accuracy accuracy) -
          g1 t n.+1 (n.+1 - 1)%coq_nat) /
         INR n.+1 / (1 + g t n.+1)) -
      g1 t n.+1 (n.+1 - 1)%coq_nat) /
     (1 + g t n.+1) /
     vec_inf_norm (FT2R_mat (A1_J A)) /
     (1 + default_rel t) -
     2 * d_mag_def_alt A b /
     (1 - rho_def_alt A b))%Re.
Proof.
intros. apply Rlt_Rminus. repeat apply Rdiv_lt_right.
+ apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
+ apply vec_norm_strong_not_0 . intros. rewrite !mxE.
  assert (Hneq: forall i, (FT2R (A i i) <> 0%Re)).
  { intros. by apply BDIV_FT2R_sep_zero. } apply Hneq.
+ apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
+ apply Rcomplements.Rlt_minus_r.
  apply  Rsqr_incrst_0.
  - rewrite Rsqr_sqrt . 
    * repeat apply Rdiv_lt_right.
      apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
      apply lt_0_INR. lia.
      apply Rcomplements.Rlt_minus_r. 
      apply Rgt_lt. 
      assert (((2 * d_mag_def_alt A b /
                  (1 - rho_def_alt A b) *
                  (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) *
                  (1 + g t n.+1) +
                  g1 t n.+1 (n.+1 - 1)%coq_nat)² *
                 (1 + g t n.+1) * INR n.+1 +
                 g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
                ((2 * d_mag_def_alt A b * /
                  (1 - rho_def_alt A b) *
                  (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) *
                  (1 + g t n.+1) +
                  g1 t n.+1 (n.+1 - 1)%coq_nat)² *
                 (1 + g t n.+1) * INR n.+1 +
                 g1 t n.+1 (n.+1 - 1)%coq_nat)%Re) by nra.
      rewrite H1. clear H1.
      eapply Rgt_ge_trans. apply H0. apply Rle_ge.
      unfold Rsqr. nra.
    * repeat apply Rmult_le_pos.
      ++ apply Rlt_le. apply Rlt_Rminus.
         eapply Rle_lt_trans; last by apply H0.
         assert (g1 t n.+1 (n.+1 - 1)%coq_nat = 
                  (g1 t n.+1 (n.+1 - 1)%coq_nat + 0)%Re) by nra.
         rewrite [in X in (X <= _)%Re]H1. apply Rplus_le_compat_l.
         apply Rmult_le_pos.
         -- apply Rmult_le_pos. apply pos_INR.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
         -- apply Rle_0_sqr .
      ++ apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR. lia.
      ++ apply Rlt_le, Rinv_0_lt_compat.
         apply Rplus_lt_le_0_compat; try nra; try apply g_pos.
 - apply Rplus_le_le_0_compat; last by apply g1_pos.
   repeat apply Rmult_le_pos; try nra; try apply bpow_ge_0; try apply d_mag_ge_0.
   * apply d_mag_def_alt_ge_0. apply H.
   * apply Rlt_le, Rinv_0_lt_compat. apply Rlt_Rminus. apply H.
   * apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
   * apply /RleP. apply vec_norm_pd.
   * apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  - apply sqrt_pos.
Qed.

Lemma sub0l_vec:
  forall (n:nat) (v: 'cV[R]_n.+1),
  0 - v = - v.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE.
rewrite -RminusE -!RoppE. 
rewrite Rminus_0_l. nra.
Qed.


(** Refactoring definitions to make them readable and beautiful **)
Lemma jacobi_precond_compute_implies_math {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (accuracy: ftype t) (k: nat)
  (Hrho_gt_0: (0 < rho_def A b)%Re)
  (Hx_lb: (d_mag_def_alt A b / (1 - rho_def_alt A b) <
              vec_inf_norm (x_fix ((FT2R_mat A)^-1 *m (FT2R_mat b))
                                  (FT2R_mat b) (FT2R_mat A)))%Re) :
  jacobi_preconditions_Rcompute A b accuracy k ->
  jacobi_preconditions_math A b accuracy k.
Proof.
intros.
unfold jacobi_preconditions_Rcompute in H.
destruct H as [Hfa [Hrho [Hdom [Hfdiv [HG1 [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]].
unfold jacobi_preconditions_math.
(*assert (Hrho_Re: (0 < rho_def A b)%Re).
{ apply rho_gt_0. apply Hrho. }
*)
assert (HG_re: (FT2R (BMULT accuracy accuracy) >
                 g1 t n.+1 (n.+1 - 1)%coq_nat +
                 INR n.+1 * (1 + g t n.+1) *
                 (g1 t n.+1 (n.+1 - 1)%coq_nat +
                  2 * (1 + g t n.+1) *
                  (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) *
                  d_mag_def A b * / (1 - rho_def A b))²)%Re).
{ apply Rgt_lt. 
  (*destruct HG1 as [HG1 _]. *)
  eapply Rle_lt_trans; try apply HG1.
  apply Rplus_le_compat_l. apply Rmult_le_compat_l.
  - apply Rmult_le_pos. apply pos_INR. 
    apply Rplus_le_le_0_compat. nra. apply g_pos.
  - apply  Rsqr_incr_1.
    * apply Rplus_le_compat_l.
      apply Rmult_le_compat.
      ++ repeat apply Rmult_le_pos. nra.
         apply Rplus_le_le_0_compat. nra. apply g_pos.
         apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
         apply /RleP. apply vec_norm_pd.
         apply d_mag_ge_0.
      ++ apply Rlt_le, Rinv_0_lt_compat. 
         apply Rlt_Rminus. eapply Rle_lt_trans.
         by apply rho_def_le_alt. apply Hrho.
      ++ apply Rmult_le_compat_l.  
         repeat apply Rmult_le_pos. nra.
         apply Rplus_le_le_0_compat. nra. apply g_pos.
         apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
         apply /RleP. apply vec_norm_pd.
         apply d_mag_def_le_alt. intros. apply Hfdiv.
         intros. apply Hfa. apply Hrho.
      ++ assert ((rho_def A b = rho_def_alt A b)%Re \/
                  (rho_def A b < rho_def_alt A b)%Re).
         { pose proof (@rho_def_le_alt t n A b Hfdiv Hfa). nra. }
         destruct H. 
         rewrite H; nra.
         apply Rlt_le. apply Rinv_lt_contravar .
         apply Rmult_lt_0_compat.
         apply Rlt_Rminus. apply Hrho.
         apply Rlt_Rminus. eapply Rle_lt_trans.
         by apply rho_def_le_alt. apply Hrho.
         apply Rplus_le_lt_compat. nra.
         by apply Ropp_lt_contravar.
    * apply Rplus_le_le_0_compat. apply g1_pos.
      repeat apply Rmult_le_pos. nra.
      apply Rplus_le_le_0_compat. nra. apply g_pos.
      apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
      apply /RleP. apply vec_norm_pd.
      apply d_mag_ge_0.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. eapply Rle_lt_trans.
      by apply rho_def_le_alt. apply Hrho.
    * apply Rplus_le_le_0_compat. apply g1_pos.
      repeat apply Rmult_le_pos. nra.
      apply Rplus_le_le_0_compat. nra. apply g_pos.
      apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
      apply /RleP. apply vec_norm_pd.
      apply d_mag_def_alt_ge_0. apply Hrho.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. apply Hrho.
}
assert (Hf_ge: (0 <
                 f_error 0 b (\col__ Zconst t 0)
                   ((FT2R_mat A)^-1 *m FT2R_mat b) A -
                 d_mag_def A b / (1 - rho_def A b))%Re).
{ apply Rlt_Rminus.
  apply Rle_lt_trans with 
  (d_mag_def_alt A b / (1 - rho_def_alt A b))%Re.
  + apply Rmult_le_compat.
    - apply d_mag_ge_0.
    - apply Rlt_le, Rinv_0_lt_compat. apply Rlt_Rminus.
      apply Rle_lt_trans with (rho_def_alt A b).
      by apply rho_def_le_alt. apply Hrho.
    - apply d_mag_def_le_alt. apply Hfdiv. apply Hfa. apply Hrho.
    - assert ((rho_def A b = rho_def_alt A b)%Re \/
                  (rho_def A b < rho_def_alt A b)%Re).
      { pose proof (@rho_def_le_alt t n A b Hfdiv Hfa). nra. }
      destruct H. 
      rewrite H; nra.
      apply Rlt_le. 
      replace (1 / (1 - rho_def A b))%Re with 
                  (/ (1 - rho_def A b))%Re by nra.
      apply Rinv_lt_contravar .
      apply Rmult_lt_0_compat.
      apply Rlt_Rminus. apply Hrho.
      apply Rlt_Rminus. eapply Rle_lt_trans.
      by apply rho_def_le_alt. apply Hrho.
      apply Rplus_le_lt_compat. nra.
      by apply Ropp_lt_contravar.
  + unfold f_error.
    assert (FT2R_mat (X_m_jacobi 0 (\col__ Zconst t 0) b A) = 0).
    { apply matrixP. unfold eqrel. intros. rewrite !mxE. simpl. reflexivity. }
    rewrite H. rewrite sub0l_vec. rewrite -vec_inf_norm_opp.
    apply Hx_lb.
}
repeat split; try apply size_cons; try apply Hfa; try apply Hfdiv;
try apply Hrho; try apply Hfacc; try (intros; apply Hfx0);
try (intros; by rewrite mxE); try (intros; apply HfA2); try (intros; apply Hfb).
+ apply Rle_lt_trans with (rho_def_alt A b).
  by apply rho_def_le_alt. apply Hrho.
+ by apply diagonal_dominance_implies_invertibility.
+ apply HG_re.
+ assert ((ln
             ((f_error 0 b (\col__ Zconst t 0)
                 ((FT2R_mat A)^-1 *m FT2R_mat b)
                 A -
               d_mag_def A b / (1 - rho_def A b)) *
              (1 + rho_def A b) /
              ((sqrt
                  ((FT2R
                      (BMULT accuracy accuracy) -
                    g1 t n.+1 (n.+1 - 1)%coq_nat) /
                   INR n.+1 / (1 + g t n.+1)) -
                g1 t n.+1 (n.+1 - 1)%coq_nat) /
               (1 + g t n.+1) /
               vec_inf_norm (FT2R_mat (A1_J A)) /
               (1 + default_rel t) -
               2 * d_mag_def A b /
               (1 - rho_def A b))) <= 0)%Re \/
            (0 <= (ln
                     ((f_error 0 b (\col__ Zconst t 0)
                         ((FT2R_mat A)^-1 *m FT2R_mat b)
                         A -
                       d_mag_def A b / (1 - rho_def A b)) *
                      (1 + rho_def A b) /
                      ((sqrt
                          ((FT2R
                              (BMULT accuracy accuracy) -
                            g1 t n.+1 (n.+1 - 1)%coq_nat) /
                           INR n.+1 / (1 + g t n.+1)) -
                        g1 t n.+1 (n.+1 - 1)%coq_nat) /
                       (1 + g t n.+1) /
                       vec_inf_norm (FT2R_mat (A1_J A)) /
                       (1 + default_rel t) -
                       2 * d_mag_def A b /
                       (1 - rho_def A b)))))%Re).
  { nra. } destruct H.
  - unfold k_min. rewrite Coqlib.Z_to_nat_neg.
    apply le_lt_trans with (k_min_alt A b accuracy); last by lia.
    unfold k_min_alt. lia.
    apply Zceil_glb. unfold Rlog. apply Rcomplements.Rmult_le_0_r.
    nra. apply ln_rho_inv_ge_0. apply Hfdiv. apply Hfa. apply Hrho. 
    apply Hrho_gt_0.
  - apply le_lt_trans with (k_min_alt A b accuracy); last by apply Hk.
    apply sublist.Z_to_nat_monotone.
    apply Zceil_le.
    unfold Rlog. apply Rmult_le_compat. try by apply ln_rho_rel .
    * apply H.
    * apply ln_rho_inv_ge_0. apply Hfdiv. apply Hfa. apply Hrho. 
      apply Hrho_gt_0.
    * apply ln_incr.
      ++ repeat apply Rmult_lt_0_compat. 
         -- apply Hf_ge.
         -- assert ((0 <= rho_def A b)%Re). { by apply rho_ge_0. }
            nra.
         -- apply Rinv_0_lt_compat. apply tau_sqr_rel.
            apply Hfdiv. apply Hfa. apply Hrho. apply HG_re.
      ++ apply Rmult_le_compat.
         -- apply Rmult_le_pos; last by 
            (apply Rplus_le_le_0_compat; try nra; try apply rho_ge_0).
            nra.
         -- apply Rlt_le.
            apply Rinv_0_lt_compat. apply tau_sqr_rel.
            apply Hfdiv. apply Hfa. apply Hrho. apply HG_re.
         -- apply Rmult_le_compat.
            ** nra.
            ** apply Rplus_le_le_0_compat; try nra; by try apply rho_ge_0.
            ** apply Rplus_le_compat.
               +++ apply f_error0_bnd. apply rho_1_implies_rho_2 with b.
                   apply Hrho.
               +++ apply Ropp_le_contravar. apply Rmult_le_pos.
                   apply d_mag_ge_0. apply Rlt_le, Rinv_0_lt_compat.
                   apply Rlt_Rminus. eapply Rle_lt_trans; last by apply Hrho.
                   by apply rho_def_le_alt.
            ** apply Rplus_le_compat_l. by apply rho_def_le_alt.
         -- apply Rinv_le. apply tau_sqr_rel_Rcompute.
            apply Hfdiv. apply Hfa. apply Hrho. apply HG1.
            apply Rplus_le_compat_l.
            apply Ropp_le_contravar. apply d_mag_rel_1.
            apply Hfdiv. apply Hfa. apply Hrho.
    * apply ln_rho_rel. apply Hfdiv. apply Hfa.
      apply Rlt_le_trans with (rho_def A b)%Re.
      apply Hrho_gt_0. by apply rho_def_le_alt.
      apply Hrho. nra.
+ lia.
+ apply Hf_ge.
+ intros. apply input_bound_compute_implies_math; try by [].  
  apply Hinp.
+ intros. apply input_bound_compute_implies_math;try by []. 
  apply Hinp. 
+ intros. apply Hinp.
+ apply input_bound_compute_implies_math; try by [].
  apply Hinp. 
+ intros. apply input_bound_compute_implies_math; try by [].
  apply Hinp.  
+ intros. apply input_bound_compute_implies_math; try by [].
  apply Hinp. 
Qed.


Definition jacobi_preconditions {t: type}
  (A: matrix t) (b: vector t) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
    matrix_cols A (matrix_rows A) /\
    (0 < length A)%coq_nat /\
    (length A = length b) /\
    let n := (length A).-1 in
    let A_v := @matrix_inj t A n.+1 n.+1 in
    let b_v := @vector_inj t b n.+1 in  
    jacobi_preconditions_Rcompute A_v b_v accuracy k.


Lemma jacobi_iteration_bound_monotone:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k k': nat),
   (k <= k')%nat ->
   jacobi_preconditions A b acc k ->
   jacobi_preconditions A b acc k'.
Proof.
intros.
unfold jacobi_preconditions in H0.
unfold jacobi_preconditions.
destruct H0 as [HAA [HlenA [HeqAb H0]]].
split. apply HAA. split. apply HlenA. split. apply HeqAb.
repeat split; try apply H0.
apply /ssrnat.ltP.
rewrite leq_eqVlt  in H.
assert (k == k' \/ (k < k')%nat).
{ by apply /orP. } destruct H1.
+ assert (k = k'). { by apply /eqP. } rewrite -H2.
  apply /ssrnat.ltP. by apply H0.
+ apply ltn_trans with k.
  apply /ssrnat.ltP. by apply H0.
  by []. 
Qed.

Lemma jacobi_iteration_bound_corollaries:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
   matrix_cols A (matrix_rows A) /\
   Forall (Forall finite) A /\
   Forall finite (invert_diagmatrix (diag_of_matrix A)) /\
   Forall finite b /\ finite acc.
Proof. 
intros.
destruct H as [HAA [HlenA [HeqAb H]]].
remember (length A).-1 as n.
destruct H as [Hfa [Hrho [Hdom [Hfdiv [HG1 [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]].
repeat split.
+ apply HAA.
+ apply Forall_forall. intros. 
  pose proof (@In_nth _ A x []).
  specialize (H0 H). destruct H0 as [i [HiA H0]].
  rewrite -H0.
  apply Forall_forall. intros. 
  pose proof (@In_nth _ (nth i A []) x0 (Zconst t 0)).
  specialize (H2 H1).
  destruct H2 as [j [HjA H2]].
  rewrite -H2.
  specialize (Hfa (@inord n i) (@inord n j)).
  rewrite !mxE in Hfa.
  rewrite !inordK in Hfa.
  - apply Hfa.
  - rewrite Heqn prednK. by apply /ssrnat.ltP. by apply /ssrnat.ltP.
  - rewrite Heqn prednK.
    assert (length (nth i A []) = length A).
    { unfold matrix_cols, matrix_rows in HAA.
      rewrite (@Forall_nth _ (fun r : seq.seq (ftype t)
         =>
         Zcomplements.Zlength r =
         Zcomplements.Zlength A) A) in HAA.
      specialize (HAA i [] HiA). 
      by apply invariants.Zlength_eq.
    } rewrite H3 in HjA. by apply /ssrnat.ltP.
   by apply /ssrnat.ltP.
+ apply Forall_nth. intros.
  unfold invert_diagmatrix. 
  rewrite (nth_map_inrange (Zconst t 0)).
  - specialize (Hfdiv (@inord n i)).
    rewrite !mxE in Hfdiv. unfold diag_of_matrix.
    rewrite nth_map_seq.
    * unfold matrix_index. rewrite inordK in Hfdiv.
      ++ apply Hfdiv.
      ++ rewrite Heqn prednK. rewrite !map_length seq_length /matrix_rows_nat in H.
         by apply /ssrnat.ltP. by apply /ssrnat.ltP.
    * unfold matrix_rows_nat. 
      by rewrite !map_length seq_length /matrix_rows_nat in H.
  - rewrite !map_length seq_length.
    by rewrite !map_length seq_length in H.
+ apply Forall_forall. intros.
  pose proof (@In_nth _ b x (Zconst t 0)).
  specialize (H0 H). destruct H0 as [i [Hjb H0]].
  rewrite -H0.
  specialize (Hfb (@inord n i)).
  rewrite mxE in Hfb. rewrite inordK in Hfb.
  - apply Hfb.
  - rewrite Heqn prednK.
    * rewrite HeqAb. by apply /ssrnat.ltP.
    * by apply /ssrnat.ltP.
+ 
  apply BMULT_finite_e in Hfacc. by destruct Hfacc .
Qed.
  
  
(** finiteness of dot product **)
Lemma dotprod_finite {t: type} (v : vector t)
(Hg1: (g1 t ((length v).+1 + 1)%coq_nat (length v).+1 <= fmax t)%Re):
(forall xy : ftype t,
  In xy (rev v) ->
  finite xy /\
  (let n := length (rev v) in
   (Rabs (FT2R xy) < sqrt  (fun_bnd t n))%Re)) ->
   finite (dotprod v v).
Proof.
intros.
pose proof (@finite_fma_from_bounded _ t (rev v) (rev v)).
specialize (H0 (dotprod v v)).
pose proof (@fma_dot_prod_rel_fold_right _ t).
specialize (H1 v v).
rewrite -combine_rev in H1; last by [].
assert (fma_dotprod t v v = dotprod v v).
{ by unfold fma_dotprod, dotprod. }
rewrite H2 in H1. specialize (H0 H1).
rewrite -rev_combine in H0; last by [].
rewrite rev_length combine_length Nat.min_id in H0.
apply H0.
apply Hg1.
intros.
repeat split;
try (specialize (H x.1); apply in_rev in H3;
      destruct x; apply in_combine_l in H3; simpl in *;
      apply in_rev in H3; try rewrite rev_length in H;by apply H);
try (specialize (H x.2); apply in_rev in H3;
      destruct x; apply in_combine_r in H3; simpl in *;
      apply in_rev in H3; try rewrite rev_length in H;by apply H).
Qed.


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).



Definition residual_math {t}  {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat):=
  diag_vector_mult (A1_J A) 
    ((X_m_jacobi k.+1 x0 b A) -f (X_m_jacobi k x0 b A)).


Lemma A1_equiv {t: type} :
 forall (A: matrix t) (x : nat),
 (x < length A)%coq_nat ->
 nth x (diag_of_matrix A) (Zconst t 0) =
 nth x (nth x A []) (Zconst t 0). 
Proof.
intros. 
by rewrite  /diag_of_matrix nth_map_seq ?/matrix_index ?/matrix_rows_nat.
Qed.

Lemma Rabs_def3 : forall x a:R, (Rabs x <= a)%Re -> 
  (x <= a /\ - a <= x)%Re.
Proof.
intros.
assert (Rabs x = a \/(Rabs x < a)%Re).
{ nra. } destruct H0.
+ assert ((0 <= x)%Re \/ (x < 0)%Re) by nra.
  destruct H1.
  - rewrite Rabs_right in H; nra.
  - rewrite Rabs_left in H; nra.
+ apply Rabs_def2 in H0. nra.
Qed.

Lemma res_xkp1_minus_xk  {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in  
  (m < n.+1)%nat ->
  forward_error_cond A x0 b  ->
  (0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re ->
  (Rabs (FT2R (A (inord m) (inord m))) *
   Rabs
     (FT2R
        (X_m_jacobi k.+1 x0 b A (inord m) ord0) +
       -
        FT2R
          (X_m_jacobi k x0 b A (inord m) ord0)) <
   (sqrt (fun_bnd t n.+1) - default_abs t) /
   (1 + default_rel t) / (1 + default_rel t))%Re.
Proof.
intros.
eapply Rle_lt_trans. apply Rmult_le_compat_l.
apply Rabs_pos. eapply Rle_trans.
apply Rabs_triang.
rewrite Rabs_Ropp.
pose proof (@jacobi_forward_error_bound _ t n).
assert ((f_error k.+1 b x0 x A <=
          rho ^ k.+1 * f_error 0 b x0 x A +
          (1 - rho ^ k.+1) / (1 - rho) * d_mag)%Re).
{ unfold forward_error_cond in H0.
  unfold rho_def in H0.
  apply H2; try (intros; apply H0). 
}
assert ((f_error k b x0 x A <=
          rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag)%Re).
{ unfold forward_error_cond in H0.
  unfold rho_def in H0.
  apply H2; try (intros; apply H0). 
} clear H2.
apply (x_k_bound (@inord n m)) in H3.
apply (x_k_bound (@inord n m)) in H4.
apply Rplus_le_compat.
apply H3. apply H4.
rewrite -/x.
rewrite -/rho -/d_mag.
assert ((vec_inf_norm
           (x_fix x (FT2R_mat b) (FT2R_mat A)) +
         rho ^ k.+1 * f_error 0 b x0 x A +
         (1 - rho ^ k.+1) / (1 - rho) * d_mag +
         (vec_inf_norm
            (x_fix x (FT2R_mat b) (FT2R_mat A)) +
          rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
       ((rho ^ k.+1 * f_error 0 b x0 x A +
         (1 - rho ^ k.+1) / (1 - rho) * d_mag + 
        rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag) + 
        2 * (vec_inf_norm
              (x_fix x (FT2R_mat b) (FT2R_mat A))))%Re).
{ nra. } rewrite H2. clear H2.
remember (f_error 0 b x0 x A) as e_0.
assert ((rho ^ k.+1 * e_0 +
                     (1 - rho ^ k.+1) / (1 - rho) * d_mag +
                     (rho ^ k * e_0 +
                      (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
               ((rho^k.+1 * (1 - rho) * e_0 + (1 - rho^k.+1) * d_mag + 
                rho^k * (1- rho) * e_0 + (1 - rho^k) * d_mag) * / (1-rho))%Re).
{ assert ((rho ^ k.+1 * e_0 +
                     (1 - rho ^ k.+1) / (1 - rho) * d_mag +
                     (rho ^ k * e_0 +
                      (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
                  ((rho ^ k.+1 * e_0 * (1 - rho)) * / (1-rho) +
                     ((1 - rho ^ k.+1) * d_mag) * / (1 - rho)  +
                     ((rho ^ k * e_0 * (1 - rho)) * / (1- rho)  +
                      ((1 - rho ^ k) * d_mag) * / (1 - rho)))%Re).
  { assert (((rho ^ k.+1 * e_0 * (1 - rho)) * / (1-rho))%Re = 
                     ((rho ^k.+1 * e_0) * ((1 - rho) * / (1-rho)))%Re).
    { nra. } rewrite H2.
    assert ((rho < 1)%Re) by apply H0.
    rewrite Rinv_r; last by nra.
    rewrite Rmult_1_r.
    assert (((rho ^ k * e_0 * (1 - rho)) * / (1- rho))%Re = 
                     ( (rho^k * e_0) * ((1 - rho) * / (1- rho)))%Re).
    { nra. } rewrite H4. rewrite Rinv_r; nra.
  } rewrite H2. clear H2. nra.
} 
assert ((rho ^ k.+1 * e_0 +
          (1 - rho ^ k.+1) / (1 - rho) *
          d_mag +
          (rho ^ k * e_0 +
           (1 - rho ^ k) / (1 - rho) *
           d_mag))%Re = 
        (rho ^ k.+1 * e_0 +
           (1 - rho ^ k.+1) / (1 - rho) * d_mag +
           rho ^ k * e_0 +
           (1 - rho ^ k) / (1 - rho) * d_mag)%Re) by nra.
rewrite -H3. clear H3.
rewrite H2. clear H2.
assert ((rho ^ k.+1 * (1 - rho) * e_0 +
                  (1 - rho ^ k.+1) * d_mag +
                  rho ^ k * (1 - rho) * e_0 +
                  (1 - rho ^ k) * d_mag)%Re = 
                (rho ^ k * (1+ rho) * (1 - rho) * e_0 + 
                  2* d_mag  - rho^k * (1 + rho) * d_mag)%Re).
{ simpl. nra. } rewrite H2. clear H2.
assert ((rho ^ k * (1 + rho) * (1 - rho) * e_0 +
                  2 * d_mag - rho ^ k * (1 + rho) * d_mag)%Re = 
                ((rho ^ k * (1 + rho) * ((1-rho) * e_0 - d_mag)) + 2 * d_mag)%Re).
{ nra. } rewrite H2. clear H2.
rewrite Rmult_plus_distr_r.
assert ((rho ^ k * (1 + rho) *
                    ((1 - rho) * e_0 - d_mag) * / (1 - rho))%Re =
                (rho ^ k * (1 + rho) * 
                (e_0 * ( (1 - rho) * / (1 - rho)) - d_mag * /(1 - rho)))%Re).
{ nra. } rewrite H2. clear H2. 
assert ((rho < 1)%Re) by apply H0.
rewrite Rinv_r; last by nra.
rewrite Rmult_1_r.
rewrite Heqe_0.
apply bound_1; try apply H0.
rewrite Heqe_0 in H1.
apply H1.
Qed.


Lemma bound_6 {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  input_bound A x0 b  ->
  (rho < 1)%Re -> 
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  (rho ^ k * (1 + rho) *
 ((f_error 0 b x0 x A) - d_mag * / (1 - rho)) +
 2 * d_mag * / (1 - rho) +
 2 *
 vec_inf_norm
   (x_fix x (FT2R_mat b) (FT2R_mat A)) <
 (bpow Zaux.radix2 (femax t) -
  default_abs t) / (1 + default_rel t))%Re.
Proof.
intros.
unfold input_bound in H.
destruct H as [_ [_ [_ [_ [_ bnd6]]]]].
apply Rle_lt_trans with 
(1 * (1 + rho_def A b) *
        (f_error 0 b x0
           ((FT2R_mat A)^-1 *m FT2R_mat b) A -
         d_mag_def A b * / (1 - rho_def A b)) +
        2 * d_mag_def A b *
        / (1 - rho_def A b) +
        2 *
        vec_inf_norm
          (x_fix
             ((FT2R_mat A)^-1 *m FT2R_mat b)
             (FT2R_mat b) (FT2R_mat A)))%Re.
+ apply Rplus_le_compat_r.
  unfold d_mag, rho. apply Rplus_le_compat_r.
  unfold x, A_real, b_real.
  apply Rmult_le_compat_r. apply Rlt_le. apply H1.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat; try nra; by try apply rho_ge_0.
  assert ( 1%Re = (1 ^ k)%Re) by (rewrite pow1; nra).
  rewrite H. apply pow_incr.
  split. by apply rho_ge_0.
  apply Rlt_le. apply H0.
+ apply bnd6.
Qed.



Lemma no_overflow_xkp1_minus_xk {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
   let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
   (m < n.+1)%coq_nat ->
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  (Rabs
   (FT2R
      (X_m_jacobi k.+1 x0 b A 
         (inord m) ord0) +
    -
    FT2R
      (X_m_jacobi k x0 b A 
         (inord m) ord0)) <
 (bpow Zaux.radix2 (femax t) -
  default_abs t) / (1 + default_rel t))%Re.
Proof.
intros.
eapply Rle_lt_trans. apply Rabs_triang.
rewrite Rabs_Ropp.
pose proof (@jacobi_forward_error_bound _ t n).
assert ((f_error k.+1 b x0 x A <=
          rho ^ k.+1 * f_error 0 b x0 x A +
          (1 - rho ^ k.+1) / (1 - rho) * d_mag)%Re).
{ unfold forward_error_cond in H0.
  unfold rho_def in H0.
  by apply H2; try (intros; apply H0). 
}
assert ((f_error k b x0 x A <=
          rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag)%Re).
{ unfold forward_error_cond in H0.
  unfold rho_def in H0.
  by apply H2; try (intros; apply H0). 
} clear H2.
apply (x_k_bound (@inord n m)) in H3.
apply (x_k_bound (@inord n m)) in H4.
eapply Rle_lt_trans.
apply Rplus_le_compat.
apply H3. apply H4.
rewrite -/x.
rewrite -/rho -/d_mag.
assert ((vec_inf_norm
           (x_fix x (FT2R_mat b) (FT2R_mat A)) +
         rho ^ k.+1 * f_error 0 b x0 x A +
         (1 - rho ^ k.+1) / (1 - rho) * d_mag +
         (vec_inf_norm
            (x_fix x (FT2R_mat b) (FT2R_mat A)) +
          rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
       ((rho ^ k.+1 * f_error 0 b x0 x A +
         (1 - rho ^ k.+1) / (1 - rho) * d_mag + 
        rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag) + 
        2 * (vec_inf_norm
              (x_fix x (FT2R_mat b) (FT2R_mat A))))%Re).
{ nra. } rewrite H2. clear H2.
remember (f_error 0 b x0 x A) as e_0.
assert ((rho ^ k.+1 * e_0 +
                     (1 - rho ^ k.+1) / (1 - rho) * d_mag +
                     (rho ^ k * e_0 +
                      (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
               ((rho^k.+1 * (1 - rho) * e_0 + (1 - rho^k.+1) * d_mag + 
                rho^k * (1- rho) * e_0 + (1 - rho^k) * d_mag) * / (1-rho))%Re).
{ assert ((rho ^ k.+1 * e_0 +
                     (1 - rho ^ k.+1) / (1 - rho) * d_mag +
                     (rho ^ k * e_0 +
                      (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
                  ((rho ^ k.+1 * e_0 * (1 - rho)) * / (1-rho) +
                     ((1 - rho ^ k.+1) * d_mag) * / (1 - rho)  +
                     ((rho ^ k * e_0 * (1 - rho)) * / (1- rho)  +
                      ((1 - rho ^ k) * d_mag) * / (1 - rho)))%Re).
  { assert (((rho ^ k.+1 * e_0 * (1 - rho)) * / (1-rho))%Re = 
                     ((rho ^k.+1 * e_0) * ((1 - rho) * / (1-rho)))%Re).
    { nra. } rewrite H2.
    assert ((rho < 1)%Re) by apply H0.
    rewrite Rinv_r; last by nra.
    rewrite Rmult_1_r.
    assert (((rho ^ k * e_0 * (1 - rho)) * / (1- rho))%Re = 
                     ( (rho^k * e_0) * ((1 - rho) * / (1- rho)))%Re).
    { nra. } rewrite H6. rewrite Rinv_r; nra.
  } rewrite H2. clear H2. nra.
} 
assert ((rho ^ k.+1 * e_0 +
          (1 - rho ^ k.+1) / (1 - rho) *
          d_mag +
          (rho ^ k * e_0 +
           (1 - rho ^ k) / (1 - rho) *
           d_mag))%Re = 
        (rho ^ k.+1 * e_0 +
           (1 - rho ^ k.+1) / (1 - rho) * d_mag +
           rho ^ k * e_0 +
           (1 - rho ^ k) / (1 - rho) * d_mag)%Re) by nra.
rewrite -H5. clear H5.
rewrite H2. clear H2.
assert ((rho ^ k.+1 * (1 - rho) * e_0 +
                  (1 - rho ^ k.+1) * d_mag +
                  rho ^ k * (1 - rho) * e_0 +
                  (1 - rho ^ k) * d_mag)%Re = 
                (rho ^ k * (1+ rho) * (1 - rho) * e_0 + 
                  2* d_mag  - rho^k * (1 + rho) * d_mag)%Re).
{ simpl. nra. } rewrite H2. clear H2.
assert ((rho ^ k * (1 + rho) * (1 - rho) * e_0 +
                  2 * d_mag - rho ^ k * (1 + rho) * d_mag)%Re = 
                ((rho ^ k * (1 + rho) * ((1-rho) * e_0 - d_mag)) + 2 * d_mag)%Re).
{ nra. } rewrite H2. clear H2.
rewrite Rmult_plus_distr_r.
assert ((rho ^ k * (1 + rho) *
                    ((1 - rho) * e_0 - d_mag) * / (1 - rho))%Re =
                (rho ^ k * (1 + rho) * 
                (e_0 * ( (1 - rho) * / (1 - rho)) - d_mag * /(1 - rho)))%Re).
{ nra. } rewrite H2. clear H2. 
assert ((rho < 1)%Re) by apply H0.
rewrite Rinv_r; last by nra.
rewrite Rmult_1_r.
rewrite Heqe_0.
apply bound_6.
apply H0. apply H0. 
rewrite Heqe_0 in H1.
apply H1.
Qed.


Lemma finite_xkp1_minus_xk {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
   (m < n.+1)%coq_nat ->
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  finite (BPLUS
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0)
                  (BOPP
                     (X_m_jacobi k x0 b A
                        (inord m) ord0))).
Proof.
intros ? ? ? ? ? ? Hcond Hf0.
apply BPLUS_no_overflow_is_finite; try rewrite ?finite_BOPP;
try (pose proof (@jacobi_forward_error_bound _ t n);
  unfold forward_error_cond in Hcond;
  unfold rho_def in Hcond;apply H0; try (intros; apply Hcond); try apply size_cons).
unfold Bplus_no_overflow.
destruct (@generic_round_property t 
            (FT2R
               (X_m_jacobi k.+1 x0 b A 
                  (inord m) ord0) +
             FT2R
               (BOPP
                  (X_m_jacobi k x0 b A 
                    (inord m) ord0))))
   as [d [e [Hde [Hd [He H0]]]]].
rewrite H0.
eapply Rle_lt_trans. apply Rabs_triang.
eapply Rle_lt_trans. apply Rplus_le_compat_l.
apply He.
apply Rcomplements.Rlt_minus_r.
rewrite Rabs_mult.
eapply Rle_lt_trans. apply Rmult_le_compat_l.
apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l.
apply Hd. apply Rcomplements.Rlt_div_r.
apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
rewrite [in X in (Rabs ( _ + X) < _)%Re]/FT2R B2R_Bopp.
fold (@FT2R t).
by apply no_overflow_xkp1_minus_xk.
Qed.

Lemma fun_bnd_lt_fmax {t} {n:nat}:
  @size_constraint t n ->
  (fun_bnd t n.+1 < bpow Zaux.radix2 (femax t))%Re.
Proof.
intro size_cons.
unfold fun_bnd.
apply Rle_lt_trans with 
((fmax t - default_abs t) / (1 + default_rel t) -
  g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
+ match goal with |-context[(_ <= ?a)%Re]=>
    replace a with (a * 1)%Re by nra
  end. 
  apply Rmult_le_compat.
  - rewrite Rmult_1_r. apply fun_bnd_pos_1. by apply g1_constraint.
  - apply Rlt_le. 
    replace (1 /  (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re with
    (/ (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re by nra.
    apply Rinv_0_lt_compat. 
    apply Rplus_lt_le_0_compat; try nra.
    apply Rmult_le_pos. apply pos_INR.
    apply Rplus_le_le_0_compat. apply g_pos.
    nra.
  - nra.
  - assert (1%Re = (/1)%Re) by nra.
    rewrite [in X in (_ <= X)%Re]H.
    replace (1 /  (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re with
    (/ (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re by nra.
    apply Rlt_le. apply Rinv_lt_contravar.
    * rewrite Rmult_1_l. 
      apply Rplus_lt_le_0_compat; try nra.
      apply Rmult_le_pos. apply pos_INR.
      apply Rplus_le_le_0_compat. apply g_pos.
      nra.
    * assert ((0 <  INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1))%Re).
      { apply Rmult_lt_0_compat. apply lt_0_INR. lia.
        apply Rplus_le_lt_0_compat. apply g_pos. nra.
      } nra.
+ unfold fmax. apply Rcomplements.Rlt_minus_l.
  apply Rcomplements.Rlt_div_l.
  apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
  apply Rcomplements.Rlt_minus_l.
  assert (bpow Zaux.radix2 (femax t) = 
          (bpow Zaux.radix2 (femax t) + 0)%Re) by nra.
  rewrite [in X in (X < _ )%Re]H. 
  apply Rplus_lt_le_compat; last by apply default_abs_ge_0.
  assert (bpow Zaux.radix2 (femax t) = 
          (bpow Zaux.radix2 (femax t) * 1)%Re) by nra.
  rewrite [in X in (X < _)%Re]H0.
  apply Rmult_lt_compat.
  - apply bpow_ge_0.
  - nra.
  - rewrite [in X in (X < _)%Re]H.
    apply Rplus_lt_compat_l.
    assert (n.+1 = S (n.+1 - 1)%coq_nat).
    { lia. } 
    assert (g1 t n.+1 (n.+1 - 1)%coq_nat = 
            g1 t (S (n.+1 - 1)%coq_nat) (n.+1 - 1)%coq_nat).
    { by rewrite -H1. } rewrite H2.
    apply Rlt_le_trans with
    (g1 t (n.+1 - 1)%coq_nat (n.+1 - 1)%coq_nat + default_abs t)%Re.
    * apply Rplus_le_lt_0_compat. apply g1_pos.
      apply default_abs_gt_0.
    * apply plus_e_g1_le .
  - assert ((0 < default_rel t)%Re) by apply default_rel_gt_0.
    nra.
Qed.
  

Lemma fun_bnd_gt_1 {t} {n:nat}:
  @size_constraint t n ->
  (1 < fun_bnd t n.+1)%Re.
Proof.
intros size_cons.
unfold fun_bnd.
replace (1 /  (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re with
(/ (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re by nra.
assert (((1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)) * 
          /(1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re = 1%Re).
{ apply Rinv_r.
  assert ((0 < (1 + INR n.+1 * (g t (n.+1 - 1)%coq_nat + 1)))%Re).
  { apply Rplus_lt_le_0_compat. nra.
    apply Rmult_le_pos. apply pos_INR.
    apply Rplus_le_le_0_compat. apply g_pos. nra.
  }  nra.
} rewrite -[in X in (X < _)%Re]H.
apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat.
apply Rplus_lt_le_0_compat. nra.
apply Rmult_le_pos. apply pos_INR.
apply Rplus_le_le_0_compat. apply g_pos. nra.
rewrite Rplus_comm.
assert (forall x y z:R, (x < z - y)%Re -> (x + y < z)%Re) 
by (intros; nra).
apply H0.
apply Rcomplements.Rlt_div_r.
apply Rplus_le_lt_0_compat. apply g_pos. nra.
apply size_cons.
Qed.

Lemma sqrt_fun_bnd_lt_fmax {t} {n:nat}:
  @size_constraint t n ->
  (sqrt (fun_bnd t n.+1) <
        bpow Zaux.radix2 (femax t))%Re.
Proof.
intros.
eapply Rlt_trans.
apply sqrt_less_alt.
+ by apply fun_bnd_gt_1.
+ by apply fun_bnd_lt_fmax.
Qed.


Lemma finite_Bmult_res {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  (m < n.+1)%coq_nat ->
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  finite (BMULT (A (inord m) (inord m))
                ((X_m_jacobi k.+1 x0 b A -f
                  X_m_jacobi k x0 b A) 
                   (inord m) ord0)).
Proof.
intros ? ? ? ? ? ? ? Hf0.
apply BMULT_no_overflow_is_finite.
+ unfold forward_error_cond in H0. apply H0.
+ rewrite mxE. apply Bplus_bminus_opp_implies.
  by apply finite_xkp1_minus_xk.
+ unfold Bmult_no_overflow. unfold rounded.
  pose proof (@generic_round_property t 
                (FT2R (A (inord m) (inord m)) *
                   FT2R
                     ((X_m_jacobi k.+1 x0 b A -f
                       X_m_jacobi k x0 b A) 
                        (inord m) ord0))).
  destruct H1 as [d [e [Hde [Hd [He H1]]]]].
  rewrite H1. 
  eapply Rle_lt_trans. apply Rabs_triang.
  eapply Rle_lt_trans. apply Rplus_le_compat_l. apply He.
  apply Rcomplements.Rlt_minus_r.
  rewrite Rabs_mult.
  eapply Rle_lt_trans. apply Rmult_le_compat_l.
  apply Rabs_pos.
  eapply Rle_trans. apply Rabs_triang.
  rewrite Rabs_R1. apply Rplus_le_compat_l.
  apply Hd. apply Rcomplements.Rlt_div_r.
  apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
  rewrite Rabs_mult. rewrite mxE.
  rewrite Bminus_bplus_opp_equiv;
  try by apply finite_xkp1_minus_xk.
    pose proof (@BPLUS_accurate' _ t).
    specialize (H2 (X_m_jacobi k.+1 x0 b A 
                      (inord m) ord0)
                    (BOPP
                      (X_m_jacobi k x0 b A 
                         (inord m) ord0))).
    specialize (H2 (finite_xkp1_minus_xk _ _ _ _ _ H H0 Hf0)).
    destruct H2 as [d1 [Hd1 H2]].
    rewrite H2.
    rewrite [in X in (_ * Rabs (( _ + X) * _) < _)%Re]/FT2R B2R_Bopp.
    fold (@FT2R t). rewrite Rabs_mult.
    rewrite -Rmult_assoc. 
    eapply Rle_lt_trans. apply Rmult_le_compat_l.
    apply Rmult_le_pos; apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l.
    apply Hd1. apply Rcomplements.Rlt_div_r.
    apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
    pose proof (@res_xkp1_minus_xk t n A x0 b k m). 
    assert ((m < n.+1)%nat). { by apply /ssrnat.ltP. }
    specialize (H3 H4 H0 Hf0).
    eapply Rlt_trans. 
    apply H3. 
    repeat apply Rmult_lt_compat_r;
    try apply Rinv_0_lt_compat;
    try apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0. 
    apply Rplus_lt_compat_r.
    apply sqrt_fun_bnd_lt_fmax. apply H0.
Qed.


Lemma residual_finite {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) (k:nat):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  let x0 := \col_(j < n.+1) (Zconst t 0) in 
  let resid := residual_math A x0 b in
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  finite (norm2
       (rev
          (vec_to_list_float n.+1 (resid k)))).
Proof.
intros ? ? ? ? ? ? ? Hcond Hf0.
unfold norm2. apply dotprod_finite.
rewrite rev_length length_veclist.
apply g1_constraint_Sn. 
apply Hcond.
intros.
repeat split.
+ apply in_rev in H.
  pose proof (@In_nth _ (rev
                           (vec_to_list_float n.+1
                              (diag_vector_mult (A1_J A)
                                 (X_m_jacobi k.+1 x0 b A -f
                                  X_m_jacobi k x0 b A)))) xy (Zconst t 0) H).
  destruct H0 as [m [Hlenk Hmth]].
  rewrite -Hmth.
  rewrite rev_nth; last by rewrite rev_length in Hlenk.
  rewrite length_veclist.
  assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
  { lia. } rewrite H0.
  rewrite nth_vec_to_list_float; 
  last by (rewrite rev_length length_veclist in Hlenk; apply /ssrnat.ltP).
  rewrite !mxE.
  repeat (rewrite nth_vec_to_list_float; last by 
  (rewrite inordK;
   rewrite rev_length length_veclist in Hlenk;
   apply /ssrnat.ltP)).
  rewrite mxE inord_val.
  apply BMULT_no_overflow_is_finite.
  - unfold forward_error_cond in Hcond.
    apply Hcond. 
  - rewrite mxE.  apply Bplus_bminus_opp_implies.
    apply Bplus_no_ov_finite.
    * pose proof (@jacobi_forward_error_bound _ t n).
      unfold forward_error_cond in Hcond.
      unfold rho_def in Hcond.
      apply H1; try (intros; apply Hcond).
    * rewrite  finite_BOPP. 
      pose proof (@jacobi_forward_error_bound _ t n).
      unfold forward_error_cond in Hcond.
      unfold rho_def in Hcond.
      apply H1; try (intros; apply Hcond).
    * (*apply Bplus_x_kp_x_k_no_oveflow. *)
      unfold Bplus_no_overflow.
      pose proof (generic_round_property t 
                     (FT2R
                         (X_m_jacobi k.+1 x0 b A
                            (inord m) ord0) +
                       FT2R
                         (BOPP
                            (X_m_jacobi k x0 b A
                               (inord m) ord0)))).
      destruct H1 as [d2 [e2 [Hde2 [Hd2 [He2 H1]]]]].
      rewrite H1.
      rewrite [in X in (Rabs (( _ + X) * _ + _) < _)%Re]/FT2R B2R_Bopp.
      fold (@FT2R t).
      eapply Rle_lt_trans. apply Rabs_triang.
      eapply Rle_lt_trans. apply Rplus_le_compat_l. apply He2.
      apply Rcomplements.Rlt_minus_r.
      rewrite Rabs_mult. 
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      eapply Rle_trans. apply Rabs_triang.
      rewrite Rabs_R1. apply Rplus_le_compat_l.
      apply Hd2.
      apply Rcomplements.Rlt_div_r.
      apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
      apply no_overflow_xkp1_minus_xk; try by [].
      by rewrite rev_length length_veclist in Hlenk.
  - unfold Bmult_no_overflow. unfold rounded.
    pose proof (@generic_round_property t 
                (FT2R (A (inord m) (inord m)) *
                   FT2R
                     ((X_m_jacobi k.+1 x0 b A -f
                       X_m_jacobi k x0 b A) 
                        (inord m) ord0))).
    destruct H1 as [d3 [e3 [Hde3 [Hd3 [He3 H1]]]]].
    rewrite H1. rewrite mxE.
    eapply Rle_lt_trans. apply Rabs_triang.
    eapply Rle_lt_trans. apply Rplus_le_compat_l.
    apply He3. 
    apply Rcomplements.Rlt_minus_r. rewrite Rabs_mult.
    eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang. rewrite Rabs_R1.
    apply Rplus_le_compat_l. apply Hd3.
    apply Rcomplements.Rlt_div_r.
    apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
    rewrite Rabs_mult.
    assert (finite (BPLUS (X_m_jacobi k.+1 x0 b A (inord m) ord0)
                  (BOPP  (X_m_jacobi k x0 b A (inord m) ord0)))).
    { apply finite_xkp1_minus_xk; try by [].
      by rewrite rev_length length_veclist in Hlenk.
    }
    rewrite Bminus_bplus_opp_equiv.
    * pose proof (@BPLUS_accurate' _ t).
      specialize (H3 (X_m_jacobi k.+1 x0 b A 
                          (inord m) ord0) 
                      (BOPP
                          (X_m_jacobi k x0 b A 
                             (inord m) ord0)) H2).
      destruct H3 as [d4 [Hd4 H3]].
      rewrite H3.
      rewrite [in X in (_ * Rabs (( _ + X) * _ ) < _)%Re]/FT2R B2R_Bopp.
      fold (@FT2R t). rewrite Rabs_mult.
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rmult_le_compat_l. apply Rabs_pos.
      eapply Rle_trans. apply Rabs_triang. rewrite Rabs_R1.
      apply Rplus_le_compat_l. apply Hd4.
      rewrite -Rmult_assoc.
      apply Rcomplements.Rlt_div_r.
      apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
      pose proof (@res_xkp1_minus_xk  t n A x0 b k m).
      assert ((m < n.+1)%nat). 
      { rewrite rev_length length_veclist in Hlenk. by apply /ssrnat.ltP. }
      specialize (H4 H5 Hcond Hf0).
      eapply Rlt_trans. 
      apply H4. 
      repeat apply Rmult_lt_compat_r;
      try apply Rinv_0_lt_compat;
      try apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
      apply Rplus_lt_compat_r.
      apply sqrt_fun_bnd_lt_fmax. apply Hcond.
    * apply H2.
+ rewrite !rev_length  length_veclist.
  rewrite rev_involutive in H.
  unfold residual_math in H.
  apply in_rev in H. 
  pose proof (@In_nth _ (rev
                           (vec_to_list_float n.+1
                              (diag_vector_mult (A1_J A)
                                 (X_m_jacobi k.+1 x0 b A -f
                                  X_m_jacobi k x0 b A)))) xy (Zconst t 0) H).
  destruct H0 as [m [Hlenk Hmth]].
  rewrite -Hmth.
  rewrite rev_nth; last by rewrite rev_length in Hlenk.
  rewrite length_veclist.
  assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
  { lia. } rewrite H0.
  rewrite nth_vec_to_list_float; 
  last by (rewrite rev_length length_veclist in Hlenk; apply /ssrnat.ltP).
  rewrite !mxE.
  repeat (rewrite nth_vec_to_list_float; last by 
  (rewrite inordK;
   rewrite rev_length length_veclist in Hlenk;
   apply /ssrnat.ltP)).
  rewrite mxE inord_val.
  pose proof (@BMULT_accurate' _ t).
  specialize (H1 (A (inord m) (inord m)) 
                 ((X_m_jacobi k.+1 x0 b A -f
                    X_m_jacobi k x0 b A) (inord m) ord0)).
  assert (finite
             (BMULT (A (inord m) (inord m))
                ((X_m_jacobi k.+1 x0 b A -f
                  X_m_jacobi k x0 b A) 
                   (inord m) ord0))).
  { apply finite_Bmult_res; try by [].
    by rewrite rev_length length_veclist in Hlenk.
  }
  specialize (H1 H2).
  destruct H1 as [d5 [e5 [Hde5 [Hd5 [He5 H1]]]]].
  rewrite H1. intros.
  eapply Rle_lt_trans. apply Rabs_triang.
  eapply Rle_lt_trans. apply Rplus_le_compat_l.
  apply He5. apply Rcomplements.Rlt_minus_r.
  rewrite Rabs_mult. eapply Rle_lt_trans.
  apply Rmult_le_compat_l. apply Rabs_pos.
  eapply Rle_trans. apply Rabs_triang.
  rewrite Rabs_R1. apply Rplus_le_compat_l.
  apply Hd5. 
  apply Rcomplements.Rlt_div_r.
  apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
  rewrite Rabs_mult. rewrite mxE.
  assert (finite 
               (BPLUS
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0)
                  (BOPP
                     (X_m_jacobi k x0 b A
                        (inord m) ord0))) ).
  { apply finite_xkp1_minus_xk; try by [].
     by rewrite rev_length length_veclist in Hlenk.
  }
  rewrite Bminus_bplus_opp_equiv.
  - pose proof (@BPLUS_accurate' _ t).
    specialize (H4 (X_m_jacobi k.+1 x0 b A 
                        (inord m) ord0)
                   (BOPP
                      (X_m_jacobi k x0 b A 
                         (inord m) ord0))).
    specialize (H4 H3).
    destruct H4 as [d6 [Hd6 H4]].
    rewrite H4. rewrite Rabs_mult. rewrite -Rmult_assoc.
    eapply Rle_lt_trans. apply Rmult_le_compat_l. 
    apply Rmult_le_pos; apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd6.
    apply Rcomplements.Rlt_div_r.
    apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
    unfold n0.
    rewrite [in X in (_ * (Rabs (_ + X)) < _)%Re]/FT2R B2R_Bopp.
    fold (@FT2R t). apply res_xkp1_minus_xk.
    rewrite rev_length length_veclist in Hlenk. by apply /ssrnat.ltP.
    apply Hcond. apply Hf0.
  - apply H3.
Qed.

Lemma vector_residual_equiv {t: type} :
 forall (A: matrix t) (b x0: vector t) (k:nat),
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  let x0' := @vector_inj _ x0 n.+1 in
  length b = length A ->
  length x0 = length A ->
  (0 < length A)%coq_nat ->
  @vector_inj _ (resid (jacobi_n A b x0 k)) n.+1 = 
  residual_math A' x0' b' k.
Proof.
intros.
apply /matrixP. unfold eqrel. intros. rewrite !mxE.
unfold resid, jacobi_residual. 
+ unfold diagmatrix_vector_mult, map2, uncurry.
  rewrite (nth_map_inrange (Zconst t 0, Zconst t 0)).
  - rewrite combine_nth.
    * rewrite nth_vec_to_list_float; last by apply ltn_ord.
      rewrite nth_vec_to_list_float; last by apply ltn_ord.
      simpl.
      rewrite !mxE. rewrite inord_val.
      rewrite A1_equiv.
      ++ rewrite nth_vec_to_list_float; last by apply ltn_ord.
         rewrite nth_vec_to_list_float; last by apply ltn_ord.
         unfold vector_sub, map2, uncurry.
         rewrite (nth_map_inrange (Zconst t 0, Zconst t 0)).
         -- rewrite combine_nth.
            assert (nth x (jacobi_n A b x0 k) (Zconst t 0) = 
                      X_m_jacobi k x0' b' A' x ord0).
            { pose proof (@func_model_equiv _ t A b x0 k).
              unfold x0', b', A'. unfold n.
              rewrite -H2. rewrite !mxE. by [].
              by apply /ssrnat.ltP. apply H. apply H0.
            } rewrite -H2.
            assert (nth x
                        (jacob_list_fun_model.jacobi_iter
                           (diag_of_matrix A)
                           (remove_diag A) b
                           (jacobi_n A b x0 k)) 
                        (Zconst t 0) = BMULT (A1_inv_J A' (inord x) ord0)
                    ((b' -f
                      A2_J A' *f X_m_jacobi k x0' b' A')
                       (inord x) ord0)).
            { rewrite !mxE. unfold jacob_list_fun_model.jacobi_iter.
              unfold diagmatrix_vector_mult, map2, uncurry.
              rewrite (nth_map_inrange (Zconst t 1, Zconst t 0)).
              + rewrite combine_nth.
                rewrite A1_invert_equiv. 
                - rewrite inord_val. unfold vector_sub, map2, uncurry.
                  rewrite (nth_map_inrange (Zconst t 0, Zconst t 0)).
                  * rewrite combine_nth. rewrite residual_equiv.
                    ++ unfold A', x0', b', n. rewrite func_model_equiv.
                       rewrite inord_val. reflexivity.
                       by apply /ssrnat.ltP. by []. by [].
                    ++ by apply /ssrnat.ltP.
                    ++ unfold jacobi_n, jacob_list_fun_model.jacobi_iter.
                       by rewrite iter_length.
                    ++ assert (length A  = n.+1).
                       { unfold n. rewrite prednK. by []. 
                         by apply /ssrnat.ltP.
                       } rewrite H3. apply ltn_ord.
                    ++ unfold matrix_vector_mult. 
                       rewrite !map_length seq_length.
                       by unfold matrix_rows_nat.
                  * rewrite combine_length. 
                    rewrite !map_length !seq_length /matrix_rows_nat.
                    rewrite H Nat.min_id.
                    assert (length A  = n.+1).
                    { unfold n. rewrite prednK. by []. 
                      by apply /ssrnat.ltP.
                    } rewrite H3. apply /ssrnat.ltP. apply ltn_ord.
                -  assert (length A  = n.+1).
                    { unfold n. rewrite prednK. by []. 
                      by apply /ssrnat.ltP.
                    } rewrite H3. apply /ssrnat.ltP. apply ltn_ord.
                - rewrite !map_length !seq_length /matrix_rows_nat.
                  rewrite combine_length !map_length !seq_length /matrix_rows_nat.
                  by rewrite H Nat.min_id.
            + repeat rewrite combine_length !map_length !seq_length /matrix_rows_nat.
              rewrite H !Nat.min_id.
              assert (length A  = n.+1).
                    { unfold n. rewrite prednK. by []. 
                      by apply /ssrnat.ltP.
                    } rewrite H3. apply /ssrnat.ltP. apply ltn_ord.
          } rewrite H3. reflexivity.
          unfold jacobi_n, jacob_list_fun_model.jacobi_iter.
          rewrite iter_length; last by []; last by [].  
          unfold diagmatrix_vector_mult, map2, uncurry.
          repeat rewrite !map_length !combine_length.
          unfold matrix_vector_mult.
          rewrite !map_length. rewrite !seq_length.
          unfold matrix_rows_nat. by rewrite H !Nat.min_id.
       -- rewrite combine_length. unfold jacobi_n.
          unfold jacob_list_fun_model.jacobi_iter.
          rewrite iter_length; last by []; last by [].
          repeat rewrite !map_length !combine_length.
          rewrite seq_length !map_length.
          rewrite seq_length /matrix_rows_nat H !Nat.min_id.
          assert (length A  = n.+1).
          { unfold n. rewrite prednK. by []. 
            by apply /ssrnat.ltP.
          } rewrite H2. apply /ssrnat.ltP. apply ltn_ord.
      ++ apply /ssrnat.ltP. 
         assert (length A = n.+1). 
         { rewrite /n prednK. by []. by apply /ssrnat.ltP. }
         rewrite H2. apply ltn_ord.
   * unfold vector_sub, map2, uncurry, jacobi_n.
     rewrite !map_length combine_length. 
     unfold jacob_list_fun_model.jacobi_iter.
     repeat rewrite !map_length !combine_length iter_length;
     last by []; last by [].
     repeat rewrite /matrix_vector_mult !map_length !combine_length .
     rewrite !map_length /matrix_rows_nat.
     by rewrite !seq_length H !Nat.min_id.
 - rewrite combine_length. 
   rewrite !map_length !combine_length. 
    unfold jacob_list_fun_model.jacobi_iter.
     repeat rewrite !map_length !combine_length iter_length;
     last by []; last by [].
    rewrite !map_length /matrix_rows_nat !combine_length.
    repeat rewrite /matrix_vector_mult !map_length !combine_length .
     rewrite !map_length /matrix_rows_nat.
    rewrite !seq_length H !Nat.min_id.
    assert (length A  = n.+1).
    { unfold n. rewrite prednK. by []. 
      by apply /ssrnat.ltP.
    } rewrite H2. apply /ssrnat.ltP. apply ltn_ord.
Qed.



Lemma add_vec_distr_5 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a- b) - (c - b) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.

Lemma dotprod_finite_implies {t: type} (v : vector t):
  finite (dotprod (rev v) (rev v)) ->
(forall x, In x v -> finite x).
Proof.
intros.
induction v.
+ by simpl in H0.
+ assert (dotprod (rev (a :: v)) (rev (a :: v)) = 
           @BFMA _ t a a (dotprod (rev v) (rev v))).
  { rewrite [in LHS]/dotprod.
    assert (combine (rev (a :: v)) (rev (a :: v))  = 
            (combine (rev v) (rev v)) ++ [(a,a)]).
    { rewrite combine_rev . simpl. 
      by rewrite combine_rev. by [].
    } rewrite H1. rewrite <- fold_left_rev_right.
    rewrite rev_unit. simpl. unfold dotprod.
    rewrite combine_rev. rewrite <- fold_left_rev_right. by [].
    by [].
  } rewrite H1 in H.
  apply BFMA_finite_e in H.
  destruct H as [Ha1 [Ha2 Hd]].
  destruct H0.
  - by rewrite -H.
  - by specialize (IHv Hd H).
Qed.
 

Lemma vec_succ_err {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b x0 x A in
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  (vec_inf_norm (FT2R_mat ((X_m_jacobi k.+1 x0 b A) -f (X_m_jacobi k x0 b A))) <=
    (rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))%Re.
Proof.
intros ? ? ? ? ? ?  ?  Hcond Hf0.
pose proof (@vec_float_sub_1 _ t n).
specialize (H (X_m_jacobi k.+1 x0 b A) (X_m_jacobi k x0 b A)).
assert (forall xy : ftype t * ftype t,
             In xy
               (combine
                  (vec_to_list_float n.+1
                     (X_m_jacobi k.+1 x0 b A))
                  (vec_to_list_float n.+1
                     (X_m_jacobi k x0 b A))) ->
             finite xy.1 /\
             finite xy.2 /\
             finite (BPLUS xy.1 (BOPP xy.2))).
{ (** if the  residual is finite then 
      x_k+1 - x_k is finite
  **)
  intros. 
  pose proof (@residual_finite  t n A b k Hcond Hf0).
  unfold norm2 in H1. 
  pose proof (@dotprod_finite_implies t).
  specialize (H2 (
             (vec_to_list_float n.+1
                (residual_math A x0 b k))) H1).
  pose proof (@dotprod_finite_implies t).
  specialize (H3 (
             (vec_to_list_float n.+1
                (residual_math A x0 b k))) H1).
  unfold residual_math in H3.
  remember (combine
          (vec_to_list_float n.+1
             (X_m_jacobi k.+1 x0 b A))
          (vec_to_list_float n.+1
             (X_m_jacobi k x0 b A))) as v_l.
  apply in_rev  in H0.
  assert (exists m, (m < length (rev v_l))%coq_nat /\
                    nth m (rev v_l) (Zconst t 0, Zconst t 0) = xy).
  { by apply In_nth. } destruct H4 as [m [Hm Hnth]].
  specialize (H3 (nth m (rev
                          (vec_to_list_float n.+1
                             (diag_vector_mult 
                                (A1_J A)
                                (X_m_jacobi k.+1 x0 b A -f
                                 X_m_jacobi k x0 b A)))) (Zconst t 0))).
  assert (In
           (nth m
              (rev
                 (vec_to_list_float n.+1
                    (diag_vector_mult 
                       (A1_J A)
                       (X_m_jacobi k.+1 x0 b A -f
                        X_m_jacobi k x0 b A))))
              (Zconst t 0))
           (
              (vec_to_list_float n.+1
                 (diag_vector_mult 
                    (A1_J A)
                    (X_m_jacobi k.+1 x0 b A -f
                     X_m_jacobi k x0 b A))))).
  { rewrite rev_nth. apply nth_In. rewrite Heqv_l in Hm.
    rewrite length_veclist . lia. rewrite Heqv_l in Hm.
    rewrite rev_length combine_length !length_veclist Nat.min_id in Hm.
    by rewrite !length_veclist.
  } specialize (H3 H4).
  rewrite rev_nth in H3.
  rewrite length_veclist in H3.
  assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
  { lia. } rewrite H5 in H3.
  rewrite nth_vec_to_list_float in H3.
  + rewrite !mxE in H3. 
    rewrite nth_vec_to_list_float in H3.
    - rewrite nth_vec_to_list_float in H3; last 
      by rewrite inordK; rewrite  Heqv_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
      apply /ssrnat.ltP.
      apply BMULT_finite_e in H3.
      destruct H3 as [Hf1 Hf2].
      rewrite mxE in Hf2.
      apply Bminus_bplus_opp_implies in Hf2.
      rewrite Heqv_l in Hnth. rewrite rev_nth in Hnth.
      rewrite combine_length !length_veclist Nat.min_id in Hnth.
      rewrite combine_nth in Hnth.
      assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
      { lia. } rewrite H3 in Hnth. 
      rewrite nth_vec_to_list_float in Hnth.
      * rewrite nth_vec_to_list_float in Hnth;
        last by  rewrite  Heqv_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
           apply /ssrnat.ltP. 
        rewrite inord_val in Hf2.
        assert (finite (X_m_jacobi k.+1 x0 b A
                                    (inord m) ord0)  /\
                finite  (X_m_jacobi k x0 b A
                                  (inord m) ord0)).
        { apply BPLUS_finite_e  in Hf2.
          split; try apply Hf2.
          rewrite finite_BOPP in Hf2.
          try apply Hf2.
        } 
        assert (xy.1 = X_m_jacobi k.+1 x0 b A  (inord m) ord0).
        { destruct xy. simpl in *. 
          apply pair_equal_spec in Hnth. 
          destruct Hnth as [Hnth1 Hnth2].
          by rewrite Hnth1.
        }
        assert (xy.2 = X_m_jacobi k x0 b A  (inord m) ord0).
        { destruct xy. simpl in *. 
          apply pair_equal_spec in Hnth. 
          destruct Hnth as [Hnth1 Hnth2].
          by rewrite Hnth2.
        } rewrite H7 H8. repeat split; try apply H6; try apply Hf2.
      * by  rewrite  Heqv_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
        apply /ssrnat.ltP.
      * by rewrite !length_veclist.
      * rewrite Heqv_l in Hm. by rewrite rev_length in Hm.
    - by rewrite inordK; rewrite  Heqv_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
      apply /ssrnat.ltP.
  + rewrite  Heqv_l rev_length combine_length !length_veclist Nat.min_id in Hm.
    by apply /ssrnat.ltP.
  + rewrite length_veclist.
    by rewrite  Heqv_l rev_length combine_length !length_veclist Nat.min_id in Hm.
} specialize (H H0).
apply reverse_triang_ineq in H.
apply Rle_trans with
(vec_inf_norm
      (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
       FT2R_mat (X_m_jacobi k x0 b A)) * (1 + default_rel t))%Re.
+ rewrite Rmult_plus_distr_l Rmult_1_r.
  assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
  { intros. nra. } apply H1.
  by apply /RleP.
+ apply Rmult_le_compat_r.
  - apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  - assert (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                FT2R_mat (X_m_jacobi k x0 b A) = 
            (FT2R_mat (X_m_jacobi k.+1 x0 b A) - x) - 
            (FT2R_mat (X_m_jacobi k x0 b A) - x)).
    { by rewrite add_vec_distr_5. } rewrite H1.
    eapply Rle_trans.
    * apply /RleP. apply triang_ineq .
    * rewrite -vec_inf_norm_opp. rewrite -RplusE.
      assert (x = x_fix x b_real A_real).
      { apply x_fixpoint.
        + unfold x. rewrite mulmxA.
          assert (FT2R_mat A *m A_real^-1 = 1).
          { fold A_real.  rewrite mulmxV . by []. apply Hcond. }
          rewrite H2. by rewrite mul1mx /b_real.
        + intros. unfold A_real. rewrite !mxE. apply BDIV_FT2R_sep_zero; apply Hcond.
      }  rewrite H2.
      assert (vec_inf_norm
                 (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                  x_fix x b_real A_real) = f_error k.+1 b x0 x A).
      { by rewrite /f_error. }
      assert (vec_inf_norm
                 (FT2R_mat (X_m_jacobi k x0 b A) -
                  x_fix x b_real A_real) = f_error k b x0 x A).
      { by rewrite /f_error. } rewrite H3 H4.
      pose proof (@jacobi_forward_error_bound _ t n A b).
      assert (forall i : 'I_n.+1,finite (A i i)) by apply Hcond.
      assert ((rho < 1)%Re) by apply Hcond.
      assert (FT2R_mat A \in unitmx). 
      { apply Hcond. }
      assert (forall i : 'I_n.+1,
              finite (BDIV (Zconst t 1) (A i i))) by apply Hcond.
      unfold forward_error_cond in Hcond.
      unfold rho_def in Hcond. specialize (H5 _  Hcond).
     assert ((f_error k.+1 b x0 x A <= rho^k.+1 * (f_error 0 b x0 x A) + 
                    ((1 - rho^k.+1) / (1 - rho))* d_mag)%Re).
     { by apply (H5 k.+1). }
     assert ((f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + 
                    ((1 - rho^k) / (1 - rho))* d_mag)%Re).
     { by apply (H5 k). } 
     eapply Rle_trans.
     ++ apply Rle_trans with
        ((rho ^ k.+1 * f_error 0 b x0 x A +
            (1 - rho ^ k.+1) / (1 - rho) * d_mag) + 
        (rho ^ k * f_error 0 b x0 x A +
          (1 - rho ^ k) / (1 - rho) * d_mag))%Re.
        -- by apply Rplus_le_compat.
        -- apply Rle_refl.
     ++ fold e_0.
        assert ((rho ^ k.+1 * e_0 +
                     (1 - rho ^ k.+1) / (1 - rho) * d_mag +
                     (rho ^ k * e_0 +
                      (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
               ((rho^k.+1 * (1 - rho) * e_0 + (1 - rho^k.+1) * d_mag + 
                rho^k * (1- rho) * e_0 + (1 - rho^k) * d_mag) * / (1-rho))%Re).
        { assert ((rho ^ k.+1 * e_0 +
                     (1 - rho ^ k.+1) / (1 - rho) * d_mag +
                     (rho ^ k * e_0 +
                      (1 - rho ^ k) / (1 - rho) * d_mag))%Re = 
                  ((rho ^ k.+1 * e_0 * (1 - rho)) * / (1-rho) +
                     ((1 - rho ^ k.+1) * d_mag) * / (1 - rho)  +
                     ((rho ^ k * e_0 * (1 - rho)) * / (1- rho)  +
                      ((1 - rho ^ k) * d_mag) * / (1 - rho)))%Re).
          { assert (((rho ^ k.+1 * e_0 * (1 - rho)) * / (1-rho))%Re = 
                     ((rho ^k.+1 * e_0) * ((1 - rho) * / (1-rho)))%Re).
            { nra. } rewrite H12. rewrite Rinv_r; last by nra.
            rewrite Rmult_1_r.
            assert (((rho ^ k * e_0 * (1 - rho)) * / (1- rho))%Re = 
                     ( (rho^k * e_0) * ((1 - rho) * / (1- rho)))%Re).
            { nra. } rewrite H13. rewrite Rinv_r; nra.
          } rewrite H12. clear H12. nra.
        } rewrite H12. clear H12.
        assert ((rho ^ k.+1 * (1 - rho) * e_0 +
                  (1 - rho ^ k.+1) * d_mag +
                  rho ^ k * (1 - rho) * e_0 +
                  (1 - rho ^ k) * d_mag)%Re = 
                (rho ^ k * (1+ rho) * (1 - rho) * e_0 + 
                  2* d_mag  - rho^k * (1 + rho) * d_mag)%Re).
        { simpl. nra. } rewrite H12. clear H12.
        assert ((rho ^ k * (1 + rho) * (1 - rho) * e_0 +
                  2 * d_mag - rho ^ k * (1 + rho) * d_mag)%Re = 
                ((rho ^ k * (1 + rho) * ((1-rho) * e_0 - d_mag)) + 2 * d_mag)%Re).
        { nra. } rewrite H12. clear H12.
        rewrite Rmult_plus_distr_r.
        assert ((rho ^ k * (1 + rho) *
                    ((1 - rho) * e_0 - d_mag) * / (1 - rho))%Re =
                (rho ^ k * (1 + rho) * 
                (e_0 * ( (1 - rho) * / (1 - rho)) - d_mag * /(1 - rho)))%Re).
        { nra. } rewrite H12. clear H12. rewrite Rinv_r; last by nra.
        rewrite Rmult_1_r. nra.
Qed.






Lemma Gamma_constraint {t}  {n:nat} 
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat) (acc : ftype t) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let Gamma := FT2R (BMULT acc acc) in 
  (rho < 1)%Re ->
  (forall i : 'I_n.+1, FT2R_mat (A1_J A) i ord0 <> 0%Re) ->
  (Gamma > g1 t n.+1 (n.+1 - 1)%coq_nat + 
          (INR n.+1 * (1 + g t n.+1) * 
           Rsqr (g1 t n.+1 (n.+1 - 1)%coq_nat + 
           2 * (1 + g t n.+1) * (1 + default_rel t) * 
           vec_inf_norm (FT2R_mat (A1_J A)) * d_mag */ (1 - rho))))%Re ->
  (0 <
 (sqrt
    ((Gamma - g1 t n.+1 (n.+1 - 1)%coq_nat) /
     INR n.+1 / (1 + g t n.+1)) -
  g1 t n.+1 (n.+1 - 1)%coq_nat) /
 (1 + g t n.+1) /
 vec_inf_norm (FT2R_mat (A1_J A)) /
 (1 + default_rel t) -
 2 * d_mag / (1 - rho))%Re.
Proof.
intros.
apply Rlt_Rminus.
repeat apply Rdiv_lt_right.
+ apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
+ by apply vec_norm_strong_not_0.
+ apply Rplus_lt_le_0_compat. nra. apply g_pos.
+ apply Rcomplements.Rlt_minus_r.
  assert ((2 * d_mag / (1 - rho) * (1 + default_rel t) *
             vec_inf_norm (FT2R_mat (A1_J A)) *
             (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
           sqrt (Rsqr (2 * d_mag / (1 - rho) * (1 + default_rel t) *
                       vec_inf_norm (FT2R_mat (A1_J A)) *
                       (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat))).
  { rewrite sqrt_Rsqr; try nra.
    apply Rplus_le_le_0_compat; try apply g1_pos.
    repeat apply Rmult_le_pos; try nra; try apply d_mag_ge_0;
    (try apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0; try apply g_pos).
    + apply Rlt_le, Rinv_0_lt_compat. apply Rlt_Rminus.
      apply H.
    + apply /RleP. apply vec_norm_pd.
  } rewrite H2. clear H2.
  apply sqrt_lt_1_alt . split.
  - apply Rle_0_sqr.
  - repeat apply Rdiv_lt_right.
    * apply Rplus_lt_le_0_compat. nra. apply g_pos.
    * apply lt_0_INR. lia.
    * apply Rcomplements.Rlt_minus_r. apply Rgt_lt. 
      assert (((2 * d_mag */ (1 - rho) * (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) *
                  (1 + g t n.+1) +
                  g1 t n.+1 (n.+1 - 1)%coq_nat)² *
                 (1 + g t n.+1) * INR n.+1 +
                 g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
              (g1 t n.+1 (n.+1 - 1)%coq_nat +
                 INR n.+1 * (1 + g t n.+1) *
                 (g1 t n.+1 (n.+1 - 1)%coq_nat +
                  2 * (1 + g t n.+1) * (1 + default_rel t) *
                  vec_inf_norm (FT2R_mat (A1_J A)) * d_mag */
                  (1 - rho))²)%Re).
      { rewrite Rplus_comm. apply Rplus_eq_compat_l.
        rewrite Rmult_comm. rewrite [in RHS]Rmult_assoc.
        apply Rmult_eq_compat_l. rewrite Rmult_comm.
        apply Rmult_eq_compat_l. 
        assert ((2 * d_mag * / (1 - rho) * (1 + default_rel t) *
                   vec_inf_norm (FT2R_mat (A1_J A)) *
                   (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
                (g1 t n.+1 (n.+1 - 1)%coq_nat +
                   2 * (1 + g t n.+1) * (1 + default_rel t) *
                   vec_inf_norm (FT2R_mat (A1_J A)) * d_mag *
                   / (1 - rho))%Re).
        { rewrite Rplus_comm. apply Rplus_eq_compat_l.
          rewrite ![in RHS]Rmult_assoc. 
          rewrite ![in LHS]Rmult_assoc.
          apply Rmult_eq_compat_l. rewrite [in RHS]Rmult_comm.
          rewrite -![in RHS]Rmult_assoc. 
          rewrite -![in LHS]Rmult_assoc.
          apply Rmult_eq_compat_r. rewrite Rmult_comm. nra.
        } by rewrite H2.
      } rewrite H2. apply H1.
Qed.


(*** Bound for the residual ***)
Lemma residual_bound {t: type} {n:nat} 
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat):
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0:=  \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b x0 x A in
  let resid := residual_math A x0 b in
  let v_l := (vec_to_list_float n.+1 (resid k)) in
  (0 < f_error 0 b x0 x A - d_mag / (1 - rho))%Re ->
  forward_error_cond A x0 b ->
  (Rabs (FT2R (norm2 (rev v_l))) <= 
    INR n.+1 * 
    (Rsqr (vec_inf_norm (FT2R_mat (A1_J A)) * 
      ((rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
        * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
      (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
Proof.
intros ? ? ? ? ? ? ? ? ?  He0 Hcond .
eapply Rle_trans.
+ apply norm2_vec_inf_norm_rel.
  - intros.
    pose proof (@residual_finite  t n A  b k Hcond He0).
    unfold norm2 in H0. 
    pose proof (@dotprod_finite_implies t).
    specialize (H1 (
               (vec_to_list_float n.+1
                  (residual_math A x0 b k))) H0).
    pose proof (@dotprod_finite_implies t).
    specialize (H2 (
                     (vec_to_list_float n.+1
                        (residual_math A x0 b k))) H0).
    remember (combine
                (vec_to_list_float n.+1 (resid k))
                (vec_to_list_float n.+1 (resid k))) as r_l.
    apply in_rev  in H.
    assert (exists m, (m < length (rev r_l))%coq_nat /\
                      nth m (rev r_l) (Zconst t 0, Zconst t 0) = xy).
    { by apply In_nth. } destruct H3 as [m [Hm Hnth]].
    specialize (H2 (nth m (rev
                            (vec_to_list_float n.+1
                               (residual_math A x0 b k))) (Zconst t 0))).
    assert (In
             (nth m
                (rev
                   (vec_to_list_float n.+1
                      (residual_math A x0 b k)))
                (Zconst t 0))
             (
                (vec_to_list_float n.+1
                   (residual_math A x0 b k)))).
    { rewrite rev_nth. apply nth_In. rewrite Heqr_l in Hm.
      rewrite length_veclist . lia. rewrite Heqr_l in Hm.
      rewrite rev_length combine_length !length_veclist Nat.min_id in Hm.
      by rewrite !length_veclist.
    } specialize (H2 H3). 
    rewrite Heqr_l in Hnth.
    rewrite -combine_rev in Hnth; last by [].
    rewrite combine_nth in Hnth ; last by [].
    assert (xy.1 = nth m
                      (rev
                         (vec_to_list_float n.+1
                            (resid k))) (Zconst t 0)).
    { destruct xy. simpl in *. 
          apply pair_equal_spec in Hnth. 
          destruct Hnth as [Hnth1 Hnth2].
          by rewrite Hnth1.
    }
    assert (xy.2 = nth m
                      (rev
                         (vec_to_list_float n.+1
                            (resid k))) (Zconst t 0)).
    { destruct xy. simpl in *. 
          apply pair_equal_spec in Hnth. 
          destruct Hnth as [Hnth1 Hnth2].
          by rewrite Hnth2.
    } rewrite H4 H5. unfold resid. split; by apply H2.
  - by apply residual_finite .
  (** finiteness of residual and elements in the list **)
+ apply Rplus_le_compat_r. 
  match goal with |-context[((?a * ?b) *?c <= _)%Re]=>
    replace ((a * b) * c)%Re with (a * (b * c))%Re by nra
  end. apply Rmult_le_compat_l.
  - apply pos_INR.
  - apply Rmult_le_compat_r.
    * apply Rplus_le_le_0_compat; try nra; try apply g_pos.
    * Search (Rsqr _ <= Rsqr _)%Re.
      apply Rsqr_incr_1.
      ++ unfold resid, residual_math. 
         apply Rle_trans with
         (vec_inf_norm 
            (diag_matrix_vec_mult_R (FT2R_mat (A1_J A))
            (FT2R_mat (X_m_jacobi k.+1 x0 b A -f
                          X_m_jacobi k x0 b A))) +
          vec_inf_norm (FT2R_mat (A1_J A)) *
          vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0 b A -f
                          X_m_jacobi k x0 b A)) * 
          g t n.+1 +  g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
         -- pose proof (@vec_norm_diag _ t n (A1_J A) 
                        (X_m_jacobi k.+1 x0 b A -f
                          X_m_jacobi k x0 b A)).
            assert (forall xy : ftype t * ftype t,
                     In xy
                       (combine
                          (vec_to_list_float n.+1 (A1_J A))
                          (vec_to_list_float n.+1
                             (X_m_jacobi k.+1 x0 b A -f
                              X_m_jacobi k x0 b A))) ->
                     finite xy.1 /\
                     finite xy.2 /\
                     finite (BMULT xy.1 xy.2)).
            { intros.
              pose proof (@residual_finite  t n A b k Hcond He0).
              unfold norm2 in H1.
              pose proof (@dotprod_finite_implies t).
              specialize (H2 (
                         (vec_to_list_float n.+1
                            (residual_math A x0 b k))) H1).
              pose proof (@dotprod_finite_implies t).
              specialize (H3 (
                              (vec_to_list_float n.+1
                                 (residual_math A x0 b k))) H1).
              remember (combine
                          (vec_to_list_float n.+1 (A1_J A))
                          (vec_to_list_float n.+1
                             (X_m_jacobi k.+1 x0 b A -f
                              X_m_jacobi k x0 b A))) as r_l.
              apply in_rev  in H0.
              assert (exists m, (m < length (rev r_l))%coq_nat /\
                                nth m (rev r_l) (Zconst t 0, Zconst t 0) = xy).
              { by apply In_nth. } destruct H4 as [m [Hm Hnth]].
              unfold residual_math in H3.
              specialize (H3 (nth m (rev
                          (vec_to_list_float n.+1
                             (diag_vector_mult 
                                (A1_J A)
                                (X_m_jacobi k.+1 x0 b A -f
                                 X_m_jacobi k x0 b A)))) (Zconst t 0))).
              assert (In
                       (nth m
                          (rev
                             (vec_to_list_float n.+1
                                (diag_vector_mult 
                                   (A1_J A)
                                   (X_m_jacobi k.+1 x0 b A -f
                                    X_m_jacobi k x0 b A))))
                          (Zconst t 0))
                       (
                          (vec_to_list_float n.+1
                             (diag_vector_mult 
                                (A1_J A)
                                (X_m_jacobi k.+1 x0 b A -f
                                 X_m_jacobi k x0 b A))))).
              { rewrite rev_nth. apply nth_In. rewrite Heqr_l in Hm.
                rewrite length_veclist . lia. rewrite Heqr_l in Hm.
                rewrite rev_length combine_length !length_veclist Nat.min_id in Hm.
                by rewrite !length_veclist.
              } specialize (H3 H4).
              rewrite rev_nth in H3.
              rewrite length_veclist in H3.
              assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
              { lia. } rewrite H5 in H3.
              rewrite nth_vec_to_list_float in H3.
              + rewrite !mxE in H3.
                rewrite nth_vec_to_list_float in H3; last 
                by rewrite inordK;
                 rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP.
                rewrite nth_vec_to_list_float in H3; last 
                by rewrite inordK;
                 rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP.
                rewrite inord_val in H3. 
                assert (finite (A1_J A (inord m) ord0) /\
                        finite  ((X_m_jacobi k.+1 x0 b A -f
                                          X_m_jacobi k x0 b A) (inord m) ord0)).
                { apply BMULT_finite_e  in H3.
                  split; try apply H3.
                }  rewrite Heqr_l in Hnth. rewrite rev_nth in Hnth.
                rewrite combine_length !length_veclist Nat.min_id in Hnth.
                assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
                { lia. } rewrite H7 in Hnth. rewrite combine_nth in Hnth.
               repeat (rewrite nth_vec_to_list_float in Hnth; last 
                by rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP).
               - assert (xy.1 =(A1_J A (inord m) ord0)).
                  { destruct xy. simpl in *. 
                    apply pair_equal_spec in Hnth. 
                    destruct Hnth as [Hnth1 Hnth2].
                    by rewrite Hnth1.
                  }
                  assert (xy.2 = (X_m_jacobi k.+1 x0 b A -f
                                  X_m_jacobi k x0 b A)  (inord m) ord0).
                  { destruct xy. simpl in *. 
                    apply pair_equal_spec in Hnth. 
                    destruct Hnth as [Hnth1 Hnth2].
                    by rewrite Hnth2.
                  } rewrite H8 H9. split. apply H6. split. apply H6. apply H3.
               - by rewrite !length_veclist.
               - by rewrite Heqr_l rev_length in Hm. 
             + by rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP.
             + rewrite Heqr_l rev_length combine_length !length_veclist Nat.min_id in Hm.
               by rewrite length_veclist.
           (** Implied by finiteness of the residual **) } specialize (H H0).
            assert ((vec_inf_norm
                     (FT2R_mat
                        (diag_vector_mult (A1_J A)
                           (X_m_jacobi k.+1 x0 b A -f
                            X_m_jacobi k x0 b A)) -
                      diag_matrix_vec_mult_R
                        (FT2R_mat (A1_J A))
                        (FT2R_mat
                           (X_m_jacobi k.+1 x0 b A -f
                            X_m_jacobi k x0 b A))) <=
                   vec_inf_norm (FT2R_mat (A1_J A)) *
                   vec_inf_norm
                     (FT2R_mat
                        (X_m_jacobi k.+1 x0 b A -f
                         X_m_jacobi k x0 b A)) * 
                   g t n.+1 + g1 t n.+1 (n.+1 - 1))).
           { by apply /RleP. } apply reverse_triang_ineq in H1.
           match goal with |-context[(_ <= ?a + ?b + ?c)%Re]=>
            replace (a + b + c)%Re with (a + (b + c))%Re by nra
           end.
           assert (forall x y z:R,  (x - y <= z)%Re -> (x <= y + z)%Re).
           { intros. nra. } apply H2.  by apply /RleP. 
        -- (** vec_inf_norm_diag_matrix_vec_mult_R **)
           eapply Rle_trans. 
           ** repeat apply Rplus_le_compat_r.
              apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
           ** rewrite -RmultE.
              assert ((vec_inf_norm (FT2R_mat (A1_J A)) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi k.+1 x0 b A -f
                             X_m_jacobi k x0 b A)) +
                       vec_inf_norm (FT2R_mat (A1_J A)) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi k.+1 x0 b A -f
                             X_m_jacobi k x0 b A)) * 
                       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
                      (vec_inf_norm (FT2R_mat (A1_J A)) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi k.+1 x0 b A -f
                             X_m_jacobi k x0 b A)) * ( 1 + g t n.+1) + 
                       g1 t n.+1 (n.+1 - 1)%coq_nat)%Re).
             { nra. } rewrite H.
             apply Rplus_le_compat_r. apply Rmult_le_compat_r.
             +++ apply Rplus_le_le_0_compat; try nra; try apply g_pos.
             +++ apply Rmult_le_compat_l. 
                 --- apply /RleP. apply vec_norm_pd.
                 --- by apply vec_succ_err .
      ++ apply /RleP. apply vec_norm_pd.
      ++ apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos.
            ** apply /RleP. apply vec_norm_pd.
            ** apply Rplus_le_le_0_compat.
               +++ repeat apply Rmult_le_pos.
                   --- apply pow_le. by apply rho_ge_0.
                   --- apply Rplus_le_le_0_compat; try nra; try by apply rho_ge_0.
                   --- apply Rlt_le, He0.
               +++ repeat apply Rmult_le_pos.
                   --- nra.
                   --- apply d_mag_ge_0.
                   --- apply Rlt_le. apply Rinv_0_lt_compat.
                       apply Rlt_Rminus. apply Hcond.
            ** apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
            ** apply Rplus_le_le_0_compat. nra. apply g_pos.
         -- apply g1_pos.
Qed.

Local Open Scope Z_scope.
Lemma Zceil_INR: forall x:Z,
  (0 <= x)%Z ->
  INR (Z.to_nat x) = IZR x.
Proof.
intros.
destruct x.
+ auto.
+ unfold IZR.
  rewrite Z2Nat.inj_pos. apply INR_IPR.
+ auto.
  contradict H. lia.
Qed.


Lemma IZR_ceil_rel (p : R):
  (p <= INR (Z.to_nat (Zceil p)))%Re.
Proof.
assert ((p < 0)%Re \/ (0 <= p)%Re).
{ nra. } destruct H.
+ apply Rle_trans with 0%Re.
  nra. 
  apply pos_INR.
+ rewrite Zceil_INR.
  apply Zceil_ub.
  assert (Zceil 0 = 0).
  { by rewrite Zceil_IZR. }
  rewrite -H0.
  by apply Zceil_le.
Qed.

Close Scope Z_scope.

Lemma jacobi_iteration_bound {t: type} {n : nat} :
 forall (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (acc: ftype t) (k: nat),
   jacobi_preconditions_math A b acc k -> 
   let acc2 := BMULT acc acc in
   let x0 := \col_(j < n.+1) (Zconst t 0) in
   let resid := residual_math A x0 b in
   finite acc2 /\ 
   exists j,
    (j <= k)%nat /\
    (forall i, (i <= j)%nat -> finite (norm2 (rev (vec_to_list_float n.+1 (resid i))))) /\
    BCMP Lt false (norm2 (rev (vec_to_list_float n.+1 (resid j)))) acc2 = false.
    (** rev (_ ) fits perfectly well with norm2_vec_inf_norm_rel **)
Proof.
intros.
unfold jacobi_preconditions_math in H.
destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [Hfx0 [HfA1_inv [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]]].
split.
+ auto.
+ exists (k_min A b acc).+1. 
  repeat split.
  - apply /ssrnat.ltP. apply Hk.
  - intros.
    apply residual_finite.
    unfold forward_error_cond. 
    repeat split; try (by intros); try apply Hrho; try apply Hinp; try apply Hrho; try apply size_cons.
    apply He0.
  - unfold BCMP.
    rewrite Bcompare_correct. 
    * rewrite Rcompare_Lt; first by [].
      change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
      remember (FT2R acc2) as Gamma.
      assert ((FT2R
                 (norm2
                    (rev
                       (vec_to_list_float n.+1
                          (resid (k_min A b acc).+1)))) < 0)%Re \/             
               (0 <= FT2R
                 (norm2
                    (rev
                       (vec_to_list_float n.+1
                          (resid (k_min A b acc).+1)))))%Re).
      { nra. } destruct H.
      apply Rlt_le_trans with 0%Re.
      nra. apply Rle_trans with 
      (g1 t n.+1 (n.+1 - 1)%coq_nat +
      INR n.+1 * (1 + g t n.+1) *
      (g1 t n.+1 (n.+1 - 1)%coq_nat +
       2 * (1 + g t n.+1) *
       (1 + default_rel t) *
       vec_inf_norm (FT2R_mat (A1_J A)) *
       d_mag_def A b * / (1 - rho_def A b))²)%Re.
        apply Rplus_le_le_0_compat; first by apply g1_pos.
          apply Rmult_le_pos. apply Rmult_le_pos. apply pos_INR.
          apply Rplus_le_le_0_compat; try nra; try apply g_pos.
          apply Rle_0_sqr.
       rewrite HeqGamma. unfold acc2. nra. 
      assert (FT2R (norm2 (rev (vec_to_list_float n.+1 (resid (k_min A b acc).+1)))) = 
              Rabs (FT2R (norm2 (rev (vec_to_list_float n.+1 (resid (k_min A b acc).+1)))))).
      { rewrite Rabs_right. nra. by apply Rle_ge. } 
      rewrite H0.
      remember (rho_def A b) as rho.
      remember (d_mag_def A b) as d_mag.
      remember (mulmx ((FT2R_mat A)^-1) (FT2R_mat b)) as x.
      remember (f_error 0 b x0 x A) as e_0.
      apply Rle_lt_trans with
      (INR n.+1 * 
        (Rsqr (vec_inf_norm (FT2R_mat (A1_J A)) * 
          ((rho ^ (k_min A b acc).+1 * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
            * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
          (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
      ++ pose proof (@residual_bound t n A b (k_min A b acc).+1).
         rewrite Heqx Heqd_mag Heqrho in He0. specialize (H1 He0).
         assert (forward_error_cond A (\col__ Zconst t 0) b ).
         { unfold forward_error_cond. repeat split; try by intros; try by (intros; apply Hinp).
           + rewrite Heqrho in Hrho. apply Hrho.
           + apply size_cons.
           + apply size_cons.
         } specialize (H1 H2).  unfold resid,x0. rewrite Heqe_0 Heqrho Heqd_mag Heqx.
         unfold x0. apply H1. 
      ++ assert ((rho = 0%Re \/ (0 < rho)%Re)).
         { pose proof (@rho_ge_0 t n A b). simpl in H1.
           rewrite Heqrho. unfold rho_def. nra.
         } destruct H1.
         (** case when rho = 0 **)
         rewrite H1. 
         assert ((0 ^ (k_min A b acc).+1 * (1 + 0) *
                  (e_0 - d_mag / (1 - 0)))%Re = 0%Re).
         { rewrite pow_ne_zero; last by lia. nra. }
         rewrite H2. rewrite  Rplus_0_l.
         rewrite H1 in HG. rewrite HeqGamma. unfold acc2.
         assert ((INR n.+1 *
                   ((vec_inf_norm (FT2R_mat (A1_J A)) *
                     (2 * d_mag / (1 - 0) *
                      (1 + default_rel t)) *
                     (1 + g t n.+1) +
                     g1 t n.+1 (n.+1 - 1)%coq_nat)² *
                    (1 + g t n.+1)) +
                   g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
                (g1 t n.+1 (n.+1 - 1)%coq_nat +
                  INR n.+1 * (1 + g t n.+1) *
                  (g1 t n.+1 (n.+1 - 1)%coq_nat +
                   2 * (1 + g t n.+1) *
                   (1 + default_rel t) *
                   vec_inf_norm (FT2R_mat (A1_J A)) *
                   d_mag * / (1 - 0))²)%Re). 
         { unfold Rsqr. nra. } rewrite H3. apply HG.
         (** 0 < rho **)
         apply Rcomplements.Rlt_minus_r.
         rewrite Rmult_comm. 
         apply Rcomplements.Rlt_div_r; 
         first by (apply lt_0_INR; lia).
         apply Rcomplements.Rlt_div_r;
         first  by (apply Rplus_lt_le_0_compat; try nra; try apply g_pos).
         assert (((Gamma - g1 t n.+1 (n.+1 - 1)%coq_nat) / INR n.+1 /
                    (1 + g t n.+1))%Re = 
                  Rsqr (sqrt ((Gamma - g1 t n.+1 (n.+1 - 1)%coq_nat) / INR n.+1 /
                                  (1 + g t n.+1))%Re)).
         { symmetry. apply Rsqr_sqrt. 
           repeat apply Rmult_le_pos.
           + apply Rle_0_minus.
             apply Rle_trans with 
             (g1 t n.+1 (n.+1 - 1)%coq_nat +
                INR n.+1 * (1 + g t n.+1) *
                (g1 t n.+1 (n.+1 - 1)%coq_nat +
                 2 * (1 + g t n.+1) *
                 (1 + default_rel t) *
                 vec_inf_norm (FT2R_mat (A1_J A)) *
                 d_mag * / (1 - rho))²)%Re.
             - assert (( 0 <= INR n.+1 * (1 + g t n.+1) *
                               (g1 t n.+1 (n.+1 - 1)%coq_nat +
                                2 * (1 + g t n.+1) * (1 + default_rel t) *
                                vec_inf_norm (FT2R_mat (A1_J A)) * d_mag *
                                / (1 - rho))²)%Re).
               { apply Rmult_le_pos; last by apply Rle_0_sqr.
                 apply Rmult_le_pos. apply pos_INR.
                 apply Rplus_le_le_0_compat. nra. apply g_pos.
               } nra.
             - apply Rlt_le. rewrite HeqGamma. by unfold acc2.
           + apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR; lia.
           + apply Rlt_le. apply Rinv_0_lt_compat. apply Rplus_lt_le_0_compat.
             nra. apply g_pos.
         } rewrite H2. 
         apply Rsqr_incrst_1.
         -- apply Rcomplements.Rlt_minus_r.
            apply Rcomplements.Rlt_div_r;
            first  by (apply Rplus_lt_le_0_compat; try nra; try apply g_pos).
            rewrite Rmult_comm. apply Rcomplements.Rlt_div_r.
            ** assert (Hneq: forall i, (FT2R (A i i) <> 0%Re)).
               { intros. by apply BDIV_FT2R_sep_zero. }
               apply vec_norm_strong_not_0. intros. 
               rewrite !mxE. apply Hneq.
            ** apply Rcomplements.Rlt_div_r;
               first  by (apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0).
               apply Rcomplements.Rlt_minus_r.
               apply Rcomplements.Rlt_div_r.
               +++ apply Rlt_gt. rewrite Heqe_0. apply He0.
               +++ apply Rcomplements.Rlt_div_r;
                   first by (apply Rplus_lt_le_0_compat; try nra; try rewrite Heqrho; by apply rho_ge_0).
                   assert ((rho ^ (k_min A b acc).+1)%Re = (/ / rho ^ (k_min A b acc).+1)%Re).
                   { by rewrite Rinv_inv. }
                   rewrite H3.
                   match goal with |-context[(_ < ?x / ?y / ?z)%Re]=>
                      replace (x / y / z)%Re with (/ ((y * z)  / x))%Re 
                   end. 
                   --- apply Rinv_lt_contravar.
                       *** repeat apply Rmult_lt_0_compat.
                           ++++ apply Rlt_gt.  rewrite Heqe_0. apply He0.
                           ++++ apply Rplus_lt_le_0_compat. nra. rewrite Heqrho. by apply rho_ge_0.
                           ++++ apply Rinv_0_lt_compat.
                                rewrite HeqGamma. unfold acc2. 
                                rewrite Heqd_mag Heqrho.
                                apply Gamma_constraint. auto.
                                rewrite Heqrho in Hrho. apply Hrho.
                                intros.
                                rewrite !mxE. by apply BDIV_FT2R_sep_zero.
                                rewrite Heqrho Heqd_mag in HG. apply HG.
                           ++++ apply Rinv_0_lt_compat.
                                apply pow_lt.  apply H1.
                       *** rewrite -pow_inv.
                           assert (((e_0 - d_mag / (1 - rho)) * (1 + rho) /
                                     ((sqrt
                                         ((Gamma - g1 t n.+1 (n.+1 - 1)%coq_nat) /
                                          INR n.+1 / (1 + g t n.+1)) -
                                       g1 t n.+1 (n.+1 - 1)%coq_nat) / 
                                      (1 + g t n.+1) /
                                      vec_inf_norm (FT2R_mat (A1_J A)) /
                                      (1 + default_rel t) - 2 * d_mag / (1 - rho)))%Re  =
                                   Rpower (/rho)%Re 
                                   ( Rlog (/rho)%Re 
                                     ((e_0 - d_mag / (1 - rho)) * (1 + rho) /
                                       ((sqrt
                                           ((Gamma - g1 t n.+1 (n.+1 - 1)%coq_nat) /
                                            INR n.+1 / (1 + g t n.+1)) -
                                         g1 t n.+1 (n.+1 - 1)%coq_nat) / 
                                        (1 + g t n.+1) /
                                        vec_inf_norm (FT2R_mat (A1_J A)) /
                                        (1 + default_rel t) - 2 * d_mag / (1 - rho)))%Re)).
                          { rewrite Rpower_Rlog. by []. 
                            + assert ( (1 < /rho)%Re -> (/ rho )%Re <> 1%Re). { nra. }
                              apply H4. replace 1%Re with (/1)%Re by nra.
                               apply Rinv_lt_contravar. rewrite Rmult_1_r.
                               apply H1.
                               apply Hrho.  
                            + apply Rinv_0_lt_compat. apply H1.
                            + repeat apply Rmult_lt_0_compat.
                              - apply Rlt_gt.  rewrite Heqe_0. apply He0.
                              - apply Rplus_lt_le_0_compat. nra. rewrite Heqrho. by apply rho_ge_0.
                              - apply Rinv_0_lt_compat.
                                rewrite HeqGamma. unfold acc2. 
                                rewrite Heqd_mag Heqrho.
                                apply Gamma_constraint. auto.
                                rewrite Heqrho in Hrho. apply Hrho.
                                intros.
                                rewrite !mxE. by apply BDIV_FT2R_sep_zero.
                                rewrite Heqrho Heqd_mag in HG. apply HG.
                          }
                          rewrite H4.
                          assert ( ((/ rho) ^ (k_min A b acc).+1)%Re = 
                                   Rpower (/rho)%Re (INR (k_min A b acc).+1)).
                          { rewrite Rpower_pow. nra.
                            apply Rinv_0_lt_compat. apply H1.
                          }
                          rewrite H5. apply Rpower_lt .
                          ++++ replace 1%Re with (/1)%Re by nra.
                               apply Rinv_lt_contravar. rewrite Rmult_1_r. apply H1. 
                               apply Hrho.
                          ++++ apply Rle_lt_trans with (INR (k_min A b acc)).
                               ---- unfold k_min.
                                    rewrite  Heqrho Heqd_mag Heqe_0 HeqGamma /x0 Heqx  /acc2.
                                     assert ((1 / rho_def A b)%Re = (/ rho_def A b)%Re). { nra. }
                                     rewrite H6.
                                    match goal with |-context[(?a <= INR (Z.to_nat (Zceil ?a )))%Re]=>
                                      remember a as p
                                    end. apply IZR_ceil_rel .
                               ---- apply lt_INR. lia.
                   --- rewrite Rinv_div. 
                       match goal with |-context[( _ = ?a / ?b / ?c)%Re]=>
                        replace (a / b / c)%Re with (a * (/b * /c))%Re by nra
                       end. rewrite -Rinv_mult_distr.
                       nra.  
                       assert (forall x:R, (0 < x)%Re -> x <> 0%Re).
                       { intros. nra. } apply H4. 
                       rewrite Heqe_0. apply He0.
                       assert (forall x:R, (0 <= x)%Re -> (1 + x)%Re <> 0%Re).
                       { intros. nra. } apply H4. rewrite Heqrho. by apply rho_ge_0.
          -- apply Rplus_le_le_0_compat; last by apply g1_pos.
             repeat apply Rmult_le_pos.
             ** apply /RleP. apply vec_norm_pd.
             ** apply Rplus_le_le_0_compat.
                +++ repeat apply Rmult_le_pos.
                    --- rewrite Heqrho. by apply rho_ge_0.
                    --- apply pow_le. rewrite Heqrho. by apply rho_ge_0.
                    --- apply Rplus_le_le_0_compat. nra. rewrite Heqrho. by apply rho_ge_0.
                    --- apply Rlt_le. rewrite Heqe_0. apply He0.
                +++ repeat apply Rmult_le_pos ; try nra. rewrite Heqd_mag. apply d_mag_ge_0.
                    apply Rlt_le. apply Rinv_0_lt_compat. 
                    apply Rlt_Rminus. apply Hrho.
             ** apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
             ** apply Rplus_le_le_0_compat. nra. apply g_pos.
          -- apply sqrt_pos.
    * rewrite <- finite_is_finite. apply residual_finite.
      unfold forward_error_cond. repeat split; try (by intros); try by (intros; apply Hinp); try apply Hrho. 
      ++ apply size_cons.
      ++ apply size_cons.
      ++ apply He0.
    * rewrite <- finite_is_finite; auto.
Qed.

Lemma jacobi_iteration_bound_lowlevel' {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
   jacobi_preconditions_math A' b' acc k ->
   length A = length b ->
   (0 < length A)%coq_nat ->
   let acc2 := BMULT acc acc in
   let x0 := (repeat  (Zconst t 0) (length b)) in
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
   finite acc2 /\ 
   exists j,
    (j <= k)%nat /\
    let y :=  jacobi_n A b x0 j in
    let r2 := norm2 (resid y) in
    (forall i, (i <= j)%nat -> finite (norm2 (resid (jacobi_n A b x0 i)))) /\
    BCMP Lt false (norm2 (resid (jacobi_n A b x0 j))) acc2 = false.
Proof.
intros.
pose proof (@jacobi_iteration_bound t (length A).-1).
specialize (H2 A' b' acc k H).
destruct H2 as [Hacc H2].
unfold jacobi_preconditions_math in H.
destruct H as [HlA [Hlab H]]. 
split.
+ by unfold acc2.
+ destruct H2 as [j [Hjrel H2]].
  exists j. split; try by [].
  intros. destruct H2 as [Hf Hlt]. split.
  - intros.  specialize (Hf i H2).
    pose proof (@vector_residual_equiv t A b x0 i).
    assert (length b = length A) by (symmetry; apply  H0).
    assert (length x0 = length A).
    { unfold x0. by rewrite !repeat_length. }
    assert ((0 < length A)%coq_nat) by apply H1.
    specialize (H3 H4 H5 H6).
    pose proof (@v_equiv t).
    specialize (H7 (resid (jacobi_n A b x0 i)) n).
    assert (length (resid (jacobi_n A b x0 i)) = n.+1).
    { repeat rewrite /matrix_vector_mult !map_length combine_length.
      rewrite !map_length. unfold jacobi_n. rewrite iter_length.
      rewrite !seq_length /matrix_rows_nat H4 !Nat.min_id.
      rewrite /n prednK. by []. by apply /ssrnat.ltP.
      by []. by []. 
    }
    specialize (H7 H8).
    rewrite H7. 
    assert ((\col_j0 vector_inj
                      (resid (jacobi_n A b x0 i))
                      n.+1 j0 ord0) = 
            vector_inj (resid (jacobi_n A b x0 i)) n.+1).
    { apply /matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H9. rewrite -/n in Hf.
    rewrite vector_residual_equiv; try by [].
    unfold A' , b' in Hf. rewrite -/n.
    assert (vector_inj x0 n.+1 = \col_(j < n.+1) (Zconst t 0)).
    { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
      by rewrite nth_repeat.
    } rewrite H10. apply Hf.
  - pose proof (@vector_residual_equiv t A b x0 j).
    assert (length b = length A) by (symmetry; apply H0).
    assert (length x0 = length A).
    { unfold x0. by rewrite !repeat_length. }
    assert ((0 < length A)%coq_nat) by apply H1.
    specialize (H2 H3 H4 H5).
    pose proof (@v_equiv t).
    specialize (H6 (resid (jacobi_n A b x0 j)) n).
    assert (length (resid (jacobi_n A b x0 j)) = n.+1).
    { repeat rewrite /matrix_vector_mult !map_length combine_length.
      rewrite !map_length. unfold jacobi_n. rewrite iter_length.
      rewrite !seq_length H3 !Nat.min_id.
      rewrite -/n prednK. by []. by apply /ssrnat.ltP.
      by []. by [].
    }
    specialize (H6 H7).
    rewrite H6. 
    assert ((\col_j0 vector_inj
                      (resid (jacobi_n A b x0 j))
                      n.+1 j0 ord0) = 
            vector_inj (resid (jacobi_n A b x0 j)) n.+1).
    { apply /matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H8. rewrite -/n in Hlt. 
    rewrite vector_residual_equiv; try by [].
    unfold A' , b' in Hlt. rewrite -/n.
    assert (vector_inj x0 n.+1 = \col_(j < n.+1) (Zconst t 0)).
    { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
      by rewrite nth_repeat.
    } by rewrite H9. 
Qed.

Definition input_bound_at_N_0 {t: type} 
  (A: matrix t) (x0 b: vector t) :=
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  (forall i j, 
    (Rabs (FT2R (A2_J A' i j)) <
          sqrt (fun_bnd t n.+1))%Re) /\
  (forall i,
    (Rabs (FT2R (x0' i ord0)) <
            sqrt (fun_bnd t n.+1))%Re) /\
  (forall i,
    ((Rabs (FT2R (b' i ord0)) +
        ((\sum_j
             (Rabs
                (FT2R (A2_J A' i j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
         (1 + g t n.+1) +
         g1 t n.+1 (n.+1 - 1)%coq_nat)) *
       (1 + default_rel t) <
       bpow Zaux.radix2 (femax t) -
       default_abs t)%Re) /\
  (forall i,
      (Rabs (FT2R (A1_inv_J A' i ord0)) *
         ((Rabs (FT2R (b' i ord0)) +
           ((\sum_j
                (Rabs
                   (FT2R (A2_J A' i j)) *
                 Rabs (FT2R (x0' j ord0)))%Re) *
            (1 + g t n.+1) +
            g1 t n.+1 (n.+1 - 1)%coq_nat)) *
          (1 + default_rel t)) <
         (bpow Zaux.radix2 (femax t) -
          default_abs t) / (1 + default_rel t))%Re) /\
  (forall i,
    (Rabs (FT2R (A1_inv_J A' i ord0)) *
       ((Rabs (FT2R (b' i ord0)) +
         ((\sum_j
              (Rabs
                 (FT2R (A2_J A' i j)) *
               Rabs (FT2R (x0' j ord0)))%Re) *
          (1 + g t n.+1) +
          g1 t n.+1 (n.+1 - 1)%coq_nat)) *
        (1 + default_rel t)) *
       (1 + default_rel t) + default_abs t +
       Rabs (FT2R (x0' i ord0)) <
       (bpow Zaux.radix2 (femax t) -
        default_abs t) / (1 + default_rel t))%Re) /\
  (forall i,
      (Rabs (FT2R (A' i i)) *
       (Rabs
          (FT2R (A1_inv_J A' i ord0)) *
        ((Rabs (FT2R (b' i ord0)) +
          ((\sum_j
               (Rabs
                  (FT2R (A2_J A' i j)) *
                Rabs (FT2R (x0' j ord0)))%Re) *
           (1 + g t n.+1) +
           g1 t n.+1 (n.+1 - 1)%coq_nat)) *
         (1 + default_rel t)) *
        (1 + default_rel t) + default_abs t +
        Rabs (FT2R (x0' i ord0))) <
        (sqrt (fun_bnd t n.+1) - default_abs t) /
            (1 + default_rel t) / (1 + default_rel t))%Re).



Lemma input_bound_at_N_0_equiv {t: type} 
  (A: matrix t) (x0 b: vector t) :
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  input_bound_at_N_0_Rcompute A' x0' b' ->
  input_bound_at_N_0 A x0 b. 
Proof.
intros. apply H.
Qed.

  

Lemma bound_each_elem_A2_x0 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat -> 
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  (forall x : ftype t * ftype t,
      In x
        (combine
           (vec_to_list_float n.+1
              (\row_j A2_J A' (inord k) j)^T)
           (vec_to_list_float n.+1
              (\col_j x0' j ord0))) ->
      finite x.1 /\
      finite x.2 /\
      (Rabs (FT2R x.1) < sqrt (fun_bnd t n.+1))%Re /\
      (Rabs (FT2R x.2) < sqrt (fun_bnd t n.+1))%Re).
Proof.
intros. apply in_rev in H5.
pose proof (@In_nth _ (rev (combine
          (vec_to_list_float n.+1
             (\row_j A2_J A' (inord k) j)^T)
          (vec_to_list_float n.+1
             (\col_j x0' j ord0)))) x (Zconst t 0, Zconst t 0) H5).
destruct H6 as [p [Hlenp Hnth]].
rewrite rev_length combine_length !length_veclist Nat.min_id in Hlenp.
rewrite rev_nth in Hnth.
rewrite combine_length !length_veclist Nat.min_id in Hnth.
assert ((n.+1 - p.+1)%coq_nat = (n.+1.-1 - p)%coq_nat) by lia.
rewrite H6 in Hnth. rewrite combine_nth in Hnth.
rewrite !nth_vec_to_list_float in Hnth.
rewrite mxE in Hnth. rewrite mxE in Hnth.
rewrite mxE in Hnth.
destruct x.
apply inject_pair_iff in Hnth.
destruct Hnth as [Hnth1 Hnth2].
simpl. rewrite -Hnth1 -Hnth2.
repeat split; try apply H2; try apply H3; try apply H4.
by apply /ssrnat.ltP.
by apply /ssrnat.ltP.
by rewrite !length_veclist.
by rewrite combine_length !length_veclist Nat.min_id.
Qed.


Lemma finite_residual_0_aux1 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat -> 
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  is_finite (fprec t) (femax t)
    (let l1 :=
       vec_to_list_float n.+1
         (\row_j A2_J A' (inord k) j)^T in
     let l2 :=
       vec_to_list_float n.+1
         (\col_j x0' j ord0) in
     dotprod_r l1 l2) = true.
Proof.
intros.
pose proof (@finite_fma_from_bounded _ t).
specialize (H6 (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                    (vec_to_list_float n.+1
                            (\col_j x0' j ord0))).
specialize (H6 (dotprod_r 
                      (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                      (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
pose proof (@fma_dot_prod_rel_holds _ n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)).
specialize (H6 H7). clear H7.
rewrite combine_length !length_veclist Nat.min_id in H6.
apply finite_is_finite.
apply H6.
+ by apply g1_constraint_Sn. 
+ by apply bound_each_elem_A2_x0 .
Qed.

Lemma no_overflow_0_aux1 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  Bplus_no_overflow t
  (FT2R (b' (@inord n k) ord0))
  (FT2R
     (BOPP
        ((A2_J A' *f x0')
           (@inord n k) ord0))).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? ? size_cons HfA2 Hfx0 Hinp. 
unfold Bplus_no_overflow.
pose proof (@generic_round_property t).
specialize (H2 (FT2R (b' (inord k) ord0) +
                   FT2R
                     (BOPP
                        ((A2_J A' *f x0') 
                           (inord k) ord0)))%Re ).
destruct H2 as [d [e [Hde [Hd [He H2]]]]].
rewrite H2.
eapply Rle_lt_trans. apply Rabs_triang.
eapply Rle_lt_trans. apply Rplus_le_compat_l.
apply He. 
apply Rcomplements.Rlt_minus_r. rewrite Rabs_mult.
eapply Rle_lt_trans. 
apply Rmult_le_compat; try apply Rabs_pos.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat_l.
assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
{ intros. by rewrite /FT2R B2R_Bopp. } rewrite H3.
rewrite Rabs_Ropp. rewrite mxE.
pose proof (@fma_dotprod_forward_error _ t).
specialize (H4 (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                    (vec_to_list_float n.+1
                            (\col_j x0' j ord0))).
rewrite !length_veclist in H4.
assert (n.+1 = n.+1) by lia.
specialize (H4 H5). clear H5.
specialize (H4 (dotprod_r 
                      (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                      (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
specialize (H4 (\sum_j (FT2R (A2_J A' (inord k) j) * FT2R (x0' j ord0))%Re)).
specialize (H4 (\sum_j (Rabs (FT2R (A2_J A' (inord k) j)) * Rabs (FT2R (x0' j ord0)))%Re)).
pose proof (@fma_dot_prod_rel_holds _ n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)). 
specialize (H4 H5). clear H5.
pose proof (@R_dot_prod_rel_holds n t n.+1 k (leqnn n.+1) (A2_J A')
                    (\col_j x0' j ord0)).
assert (\sum_j
            (FT2R (A2_J A' (inord k) j) *
             FT2R (x0' j ord0))%Re = 
           \sum_(j < n.+1)
            (FT2R_mat (A2_J A') 
              (inord k)
              (widen_ord (m:=n.+1)
                 (leqnn n.+1) j) *
              FT2R_mat (\col_j0 x0' j0 ord0)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re).
{ apply eq_big. by []. intros. 
  assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
  { unfold widen_ord. 
    apply val_inj. by simpl.
  } rewrite H7. by rewrite !mxE.
} rewrite -H6 in H5. specialize (H4 H5).
clear H5 H6.
pose proof (@R_dot_prod_rel_abs_holds n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)).
rewrite -sum_fold_mathcomp_equiv in H5.
assert (\sum_(j < n.+1)
              (FT2R_abs (FT2R_mat (A2_J A'))
                (inord k)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) *
              FT2R_abs
                (FT2R_mat
                   (\col_j0 x0' j0 ord0))
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re = 
            \sum_j
              (Rabs
                 (FT2R (A2_J A' (inord k) j)) *
               Rabs (FT2R (x0' j ord0)))%Re).
{ apply eq_big. by []. intros. 
  assert (widen_ord (m:=n.+1) (leqnn n.+1) i = i).
  { unfold widen_ord. 
    apply val_inj. by simpl.
  } rewrite H7. by rewrite !mxE.
} rewrite H6 in H5. specialize (H4 H5).
clear H5 H6.
rewrite finite_is_finite in H4.
pose proof (@finite_residual_0_aux1 t A b H H0 k H1 size_cons HfA2 Hfx0 Hinp).
specialize (H4 H5). clear H5.
apply Rle_trans with 
    (Rabs
         (\sum_j
             (Rabs
                (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
     (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
apply Rle_trans with 
    (Rabs
         (\sum_j
             ((FT2R (A2_J A' (inord k) j)) *
               (FT2R (x0' j ord0)))%Re) +
       Rabs
         (\sum_j
             (Rabs (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
{ intros. nra. } apply H5.
eapply Rle_trans. apply Rabs_triang_inv.
nra. repeat apply Rplus_le_compat_r.
rewrite [in X in (_ <= X)%Re]sum_abs_eq.
rewrite Rabs_sum_in. apply /RleP. apply Rabs_ineq.
intros. apply Rmult_le_pos; apply Rabs_pos.
rewrite sum_abs_eq. apply Rle_refl.
intros. apply Rmult_le_pos; apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l.
apply Hd.
apply Hinp.
Qed.

Lemma finite_residual_0_aux2 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  finite (b' (inord k) ord0) ->
  finite
    (nth (n.+1.-1 - @inord n k)
       (vec_to_list_float n.+1
          (b' -f A2_J A' *f x0'))
        (Zconst t 0)).
Proof.
intros.
rewrite  nth_vec_to_list_float; last (rewrite inordK; by apply /ssrnat.ltP).
rewrite mxE.
apply Bplus_bminus_opp_implies.
apply Bplus_no_ov_finite.
+ by rewrite inord_val. 
+ rewrite inord_val.
  apply finite_is_finite. rewrite is_finite_Bopp.
  rewrite mxE. by apply finite_residual_0_aux1.
+ apply no_overflow_0_aux1; try by [].
  rewrite -/n. rewrite inordK; try by apply /ssrnat.ltP.
  by apply H1. 
Qed.
    
Lemma no_overflow_Bmult_A1_inv_b_minus {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  finite (b' (inord k) ord0) ->
  Bmult_no_overflow t
  (FT2R
     (nth (n.+1.-1 - @inord n k)
        (vec_to_list_float n.+1
           (A1_inv_J A')) (Zconst t 0)))
  (FT2R
     (nth (n.+1.-1 - @inord n k)
        (vec_to_list_float n.+1
           (b' -f A2_J A' *f x0'))
        (Zconst t 0))).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? ? ? HfA2 Hfx0 ? ?.
unfold Bmult_no_overflow. unfold rounded.
pose proof (@generic_round_property t).
specialize (H5 (FT2R
                 (nth (n.+1.-1 - @inord n k)
                    (vec_to_list_float n.+1
                       (A1_inv_J A')) 
                    (Zconst t 0)) *
               FT2R
                 (nth (n.+1.-1 - @inord n k)
                    (vec_to_list_float n.+1
                       (b' -f A2_J A' *f x0'))
                    (Zconst t 0)))%Re ).
destruct H5 as [d [e [Hde [Hd [He H5]]]]].
rewrite H5.
eapply Rle_lt_trans. apply Rabs_triang.
eapply Rle_lt_trans. apply Rplus_le_compat_l.
apply He.
apply Rcomplements.Rlt_minus_r.
rewrite Rabs_mult. eapply Rle_lt_trans.
apply Rmult_le_compat_l. apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd.
apply Rcomplements.Rlt_div_r.
apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
rewrite Rabs_mult.
rewrite !nth_vec_to_list_float. rewrite inord_val.
eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
rewrite mxE.
pose proof (@finite_residual_0_aux2 t).
specialize (H6 A b H H0 k H1 H2 HfA2 Hfx0 H3 H4).
rewrite -/n -/A' -/b' -/x0' in H6.
rewrite nth_vec_to_list_float in H6. rewrite inord_val mxE in H6.
apply Bminus_bplus_opp_implies in H6.
rewrite Bminus_bplus_opp_equiv; last by apply H6.
pose proof (@BPLUS_accurate' _ t).
specialize (H7 (b' (inord k) ord0) (BOPP
            ((A2_J A' *f x0') 
               (inord k) ord0))).
specialize (H7 H6).
destruct H7 as [d2 [Hd2 H7]].
rewrite H7. rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
apply Rplus_le_compat_l.
assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
    { intros. by rewrite /FT2R B2R_Bopp. } rewrite H8.
    rewrite Rabs_Ropp. rewrite mxE.
    apply BPLUS_finite_e in H6.
    destruct H6 as [_ H6].
    apply finite_is_finite in H6. rewrite is_finite_Bopp in H6.
    rewrite mxE in H6.
    pose proof (@fma_dotprod_forward_error _ t).
    specialize (H9 (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                    (vec_to_list_float n.+1
                            (\col_j x0' j ord0))).
    rewrite !length_veclist in H9.
    assert (n.+1 = n.+1) by lia.
    specialize (H9 H10). clear H10.
    specialize (H9 (dotprod_r 
                      (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                      (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
    specialize (H9 (\sum_j (FT2R (A2_J A' (inord k) j) * FT2R (x0' j ord0))%Re)).
    specialize (H9 (\sum_j (Rabs (FT2R (A2_J A' (inord k) j)) * Rabs (FT2R (x0' j ord0)))%Re)).
    pose proof (@fma_dot_prod_rel_holds _ n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)). 
    specialize (H9 H10). clear H10.
    pose proof (@R_dot_prod_rel_holds n t n.+1 k (leqnn n.+1) (A2_J A')
                    (\col_j x0' j ord0)).
    assert (\sum_j
            (FT2R (A2_J A' (inord k) j) *
             FT2R (x0' j ord0))%Re = 
           \sum_(j < n.+1)
            (FT2R_mat (A2_J A') 
              (inord k)
              (widen_ord (m:=n.+1)
                 (leqnn n.+1) j) *
              FT2R_mat (\col_j0 x0' j0 ord0)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re).
    { apply eq_big. by []. intros. 
      assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H12. by rewrite !mxE.
    } rewrite -H11 in H10. specialize (H9 H10).
    clear H10 H11.
    pose proof (@R_dot_prod_rel_abs_holds n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)).
    rewrite -sum_fold_mathcomp_equiv in H10.
    assert (\sum_(j < n.+1)
              (FT2R_abs (FT2R_mat (A2_J A'))
                (inord k)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) *
              FT2R_abs
                (FT2R_mat
                   (\col_j0 x0' j0 ord0))
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re = 
            \sum_j
              (Rabs
                 (FT2R (A2_J A' (inord k) j)) *
               Rabs (FT2R (x0' j ord0)))%Re).
    { apply eq_big. by []. intros. 
      assert (widen_ord (m:=n.+1) (leqnn n.+1) i = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H12. by rewrite !mxE.
    } rewrite H11 in H10. specialize (H9 H10).
    clear H10 H11.
    rewrite finite_is_finite in H9.
    specialize (H9 H6).
    apply Rle_trans with 
    (Rabs
         (\sum_j
             (Rabs
                (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
     (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
    rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
    apply Rle_trans with 
    (Rabs
         (\sum_j
             ((FT2R (A2_J A' (inord k) j)) *
               (FT2R (x0' j ord0)))%Re) +
       Rabs
         (\sum_j
             (Rabs (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
     assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
     { intros. nra. } apply H10.
     eapply Rle_trans. apply Rabs_triang_inv.
     nra. repeat apply Rplus_le_compat_r.
     rewrite [in X in (_ <= X)%Re]sum_abs_eq.
     rewrite Rabs_sum_in. apply /RleP. apply Rabs_ineq.
     intros. apply Rmult_le_pos; apply Rabs_pos.
     rewrite sum_abs_eq. apply Rle_refl.
     intros. apply Rmult_le_pos; apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd2.
rewrite inordK; (by apply /ssrnat.ltP).
apply H3.
rewrite inordK; (by apply /ssrnat.ltP).
rewrite inordK; (by apply /ssrnat.ltP).
Qed.


Lemma finite_residual_0_aux3 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  finite (A1_inv_J A' (inord k) ord0) ->
  finite (b' (inord k) ord0) ->
  finite
    (BMULT
       (nth (n.+1.-1 - @inord n k)
          (vec_to_list_float n.+1
             (A1_inv_J A')) (Zconst t 0))
       (nth (n.+1.-1 - @inord n k)
          (vec_to_list_float n.+1
             (b' -f A2_J A' *f x0'))
          (Zconst t 0))).
Proof.
intros.
apply BMULT_no_overflow_is_finite.
+ rewrite  nth_vec_to_list_float; last (rewrite inordK; by apply /ssrnat.ltP).
  by rewrite inord_val.
+ apply finite_residual_0_aux2; try by [].
+ by apply no_overflow_Bmult_A1_inv_b_minus.
Qed.


Lemma no_overflow_x1_minus_x0 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  finite (A1_inv_J A' (inord k) ord0) ->
  finite (b' (inord k) ord0) ->
  Bplus_no_overflow t
  (FT2R
     (X_m_jacobi 1 x0' b' A' 
        (inord k) ord0))
  (FT2R
     (BOPP
        (X_m_jacobi 0 x0' b' A' 
           (inord k) ord0))).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? ? size_cons HfA2 Hfx0 Hinp HfA1_inv Hfb.
unfold Bplus_no_overflow.
pose proof (@generic_round_property t 
            (FT2R
                 (X_m_jacobi 1 x0' b' A' 
                    (inord k) ord0) +
               FT2R
                 (BOPP
                    (X_m_jacobi 0 x0' b' A'
                       (inord k) ord0)))%Re ).
destruct H2 as [d [e [Hde [Hd [He H2]]]]].
rewrite H2.
eapply Rle_lt_trans. apply Rabs_triang.
eapply Rle_lt_trans. apply Rplus_le_compat_l.
apply He.
apply Rcomplements.Rlt_minus_r.
eapply Rle_lt_trans. rewrite Rabs_mult.
apply Rmult_le_compat_l. apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l.
apply Hd. 
apply Rcomplements.Rlt_div_r.
apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
eapply Rle_lt_trans. eapply Rle_trans.
apply Rabs_triang. apply Rplus_le_compat. rewrite mxE.
pose proof (@BMULT_accurate' _ t).
specialize (H3 (nth (n.+1.-1 - @inord n k)
                    (vec_to_list_float n.+1
                       (A1_inv_J A')) 
                    (Zconst t 0))
              (nth (n.+1.-1 - @inord n k)
                (vec_to_list_float n.+1
                   (b' -f A2_J A' *f x0'))
                (Zconst t 0))).
pose proof (@finite_residual_0_aux3 t A b H H0 k H1 size_cons HfA2 Hfx0 Hinp HfA1_inv Hfb). 
specialize (H3 H4). rewrite -/n -/A' -/b' -/x0' in H4.
destruct H3 as [d1 [e1 [Hde1 [Hd1 [He1 H3]]]]].
rewrite H3.
rewrite !nth_vec_to_list_float.
rewrite inord_val.
eapply Rle_trans. apply Rabs_triang.
apply Rplus_le_compat.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
rewrite Rabs_mult. apply Rmult_le_compat_l. apply Rabs_pos.
rewrite mxE.
apply BMULT_finite_e in H4.
destruct H4 as [_ H4].
rewrite nth_vec_to_list_float in H4. rewrite inord_val in H4.
rewrite mxE in H4.
apply Bminus_bplus_opp_implies in H4.
rewrite Bminus_bplus_opp_equiv; last by apply H4.
pose proof (@BPLUS_accurate' _ t).
specialize (H5 (b' (inord k) ord0) (BOPP
            ((A2_J A' *f x0') 
               (inord k) ord0))).
specialize (H5 H4).
destruct H5 as [d2 [Hd2 H5]].
rewrite H5. rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
apply Rplus_le_compat_l.
assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
    { intros. by rewrite /FT2R B2R_Bopp. } rewrite H6.
    rewrite Rabs_Ropp. rewrite mxE.
    apply BPLUS_finite_e in H4.
    destruct H4 as [_ H4].
    apply finite_is_finite in H4. rewrite is_finite_Bopp in H4.
    rewrite mxE in H4.
    pose proof (@fma_dotprod_forward_error _ t).
    specialize (H7 (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                    (vec_to_list_float n.+1
                            (\col_j x0' j ord0))).
    rewrite !length_veclist in H7.
    assert (n.+1 = n.+1) by lia.
    specialize (H7 H8). clear H8.
    specialize (H7 (dotprod_r 
                      (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                      (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
    specialize (H7 (\sum_j (FT2R (A2_J A' (inord k) j) * FT2R (x0' j ord0))%Re)).
    specialize (H7 (\sum_j (Rabs (FT2R (A2_J A' (inord k) j)) * Rabs (FT2R (x0' j ord0)))%Re)).
    pose proof (@fma_dot_prod_rel_holds _ n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)). 
    specialize (H7 H8). clear H8.
    pose proof (@R_dot_prod_rel_holds n t n.+1 k (leqnn n.+1) (A2_J A')
                    (\col_j x0' j ord0)).
    assert (\sum_j
            (FT2R (A2_J A' (inord k) j) *
             FT2R (x0' j ord0))%Re = 
           \sum_(j < n.+1)
            (FT2R_mat (A2_J A') 
              (inord k)
              (widen_ord (m:=n.+1)
                 (leqnn n.+1) j) *
              FT2R_mat (\col_j0 x0' j0 ord0)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re).
    { apply eq_big. by []. intros. 
      assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H10. by rewrite !mxE.
    } rewrite -H9 in H8. specialize (H7 H8).
    clear H8 H9.
    pose proof (@R_dot_prod_rel_abs_holds n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)).
    rewrite -sum_fold_mathcomp_equiv in H8.
    assert (\sum_(j < n.+1)
              (FT2R_abs (FT2R_mat (A2_J A'))
                (inord k)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) *
              FT2R_abs
                (FT2R_mat
                   (\col_j0 x0' j0 ord0))
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re = 
            \sum_j
              (Rabs
                 (FT2R (A2_J A' (inord k) j)) *
               Rabs (FT2R (x0' j ord0)))%Re).
    { apply eq_big. by []. intros. 
      assert (widen_ord (m:=n.+1) (leqnn n.+1) i = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H10. by rewrite !mxE.
    } rewrite H9 in H8. specialize (H7 H8).
    clear H8 H9.
    rewrite finite_is_finite in H7.
    specialize (H7 H4).
    apply Rle_trans with 
    (Rabs
         (\sum_j
             (Rabs
                (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
     (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
    rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
    apply Rle_trans with 
    (Rabs
         (\sum_j
             ((FT2R (A2_J A' (inord k) j)) *
               (FT2R (x0' j ord0)))%Re) +
       Rabs
         (\sum_j
             (Rabs (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
     assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
     { intros. nra. } apply H8.
     eapply Rle_trans. apply Rabs_triang_inv.
     nra. repeat apply Rplus_le_compat_r.
     rewrite [in X in (_ <= X)%Re]sum_abs_eq.
     rewrite Rabs_sum_in. apply /RleP. apply Rabs_ineq.
     intros. apply Rmult_le_pos; apply Rabs_pos.
     rewrite sum_abs_eq. apply Rle_refl.
     intros. apply Rmult_le_pos; apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd2.
rewrite inordK; (by apply /ssrnat.ltP).
eapply Rle_trans.
apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1.
apply He1.
rewrite inordK; (by apply /ssrnat.ltP).
rewrite inordK; (by apply /ssrnat.ltP).
simpl.
assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
{ intros. unfold FT2R. by rewrite B2R_Bopp. }
rewrite H3. rewrite Rabs_Ropp. apply Rle_refl.
apply Hinp.
Qed.


Lemma finite_residual_0_aux4 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  finite (A1_inv_J A' (inord k) ord0) ->
  finite (b' (inord k) ord0) ->
  finite
  (nth (n.+1.-1 - k)
     (vec_to_list_float n.+1
        (X_m_jacobi 1 x0' b' A' -f
         X_m_jacobi 0 x0' b' A'))
     (Zconst t 0)).
Proof.
intros.
rewrite  nth_vec_to_list_float; last by apply /ssrnat.ltP.
rewrite mxE.
apply Bplus_bminus_opp_implies.
apply Bplus_no_ov_finite.
+ rewrite mxE.
  by apply finite_residual_0_aux3.
+ apply finite_is_finite. rewrite is_finite_Bopp.
  simpl. by apply finite_is_finite.
+ by apply no_overflow_x1_minus_x0.
Qed.

Lemma finite_residual_0_mult {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  forall k,
  (k < n.+1)%coq_nat ->
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  finite (A' (inord k) (inord k)) ->
  finite (A1_inv_J A' (inord k) ord0) ->
  finite (b' (inord k) ord0) ->
  finite (BMULT
                (nth (n.+1.-1 - k)
                   (vec_to_list_float n.+1
                      (A1_J A')) (Zconst t 0))
                (nth (n.+1.-1 - k)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0))).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? ? size_cons HfA2 Hfx0 fbnd HfA HdivA Hfb.
apply BMULT_no_overflow_is_finite.
+ rewrite  nth_vec_to_list_float; last by apply /ssrnat.ltP.
  by rewrite mxE.
+ by apply finite_residual_0_aux4.
+ unfold Bmult_no_overflow.
  pose proof (@generic_round_property t (FT2R
         (nth (n.+1.-1 - k)
            (vec_to_list_float n.+1
               (A1_J A')) (Zconst t 0)) *
       FT2R
         (nth (n.+1.-1 - k)
            (vec_to_list_float n.+1
               (X_m_jacobi 1 x0' b' A' -f
                X_m_jacobi 0 x0' b' A'))
            (Zconst t 0)))).
  destruct H2 as [d [e [Hde [Hd [He H2]]]]].
  unfold rounded.
  rewrite H2.
  eapply Rle_lt_trans. apply Rabs_triang.
  eapply Rle_lt_trans. apply Rplus_le_compat_l. apply He.
  apply Rcomplements.Rlt_minus_r.
  rewrite Rabs_mult.
  rewrite  nth_vec_to_list_float; last by apply /ssrnat.ltP.
  eapply Rle_lt_trans. apply Rmult_le_compat_l.
  apply Rabs_pos. 
  eapply Rle_trans. apply Rabs_triang.
  rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd.
  apply Rcomplements.Rlt_div_r.
  apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
  rewrite Rabs_mult.
  rewrite  nth_vec_to_list_float; last by apply /ssrnat.ltP.
  rewrite mxE. 
  rewrite [in X in (_ * X < _)%Re]mxE.
  rewrite Bminus_bplus_opp_equiv.
  - pose proof (@BPLUS_accurate' _ t).
    specialize (H3 (X_m_jacobi 1 x0' b' A'
                        (inord k) ord0)
                    (BOPP
                        (X_m_jacobi 0 x0' b' A'
                           (inord k) ord0))).
    assert (finite
             (BPLUS
                (X_m_jacobi 1 x0' b' A'
                   (inord k) ord0)
                (BOPP
                   (X_m_jacobi 0 x0' b' A'
                      (inord k) ord0)))).
    { apply Bplus_no_ov_finite.
      + rewrite mxE.
        by apply finite_residual_0_aux3.
      + simpl. apply finite_is_finite. rewrite is_finite_Bopp.
        by apply finite_is_finite.
      + by apply no_overflow_x1_minus_x0.
    }
    specialize (H3 H4).
    destruct H3 as [d1 [Hd1 H3]].
    rewrite H3. clear H3. rewrite Rabs_mult.
    rewrite -Rmult_assoc.
    eapply Rle_lt_trans.
    apply Rmult_le_compat_l.
    apply Rmult_le_pos; apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1.
    apply Rcomplements.Rlt_div_r.
    apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
    eapply Rle_lt_trans. apply Rmult_le_compat_l.
    apply Rabs_pos. eapply Rle_trans.
    apply Rabs_triang. apply Rplus_le_compat_l.
    assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
    { intros. by rewrite /FT2R B2R_Bopp. } rewrite H3.
    rewrite Rabs_Ropp. simpl. apply Rle_refl.
    eapply Rle_lt_trans. apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Rplus_le_compat_r.
    rewrite mxE.
    apply BPLUS_finite_e in H4.
    destruct H4 as [H4 _].
    rewrite mxE in H4.
    pose proof(@BMULT_accurate' _ t). 
    specialize (H3 (nth (n.+1.-1 - @inord n k)
                      (vec_to_list_float n.+1
                         (A1_inv_J A'))
                      (Zconst t 0))
                    (nth (n.+1.-1 - @inord n k)
                        (vec_to_list_float n.+1
                           (b' -f A2_J A' *f x0'))
                        (Zconst t 0)) H4).
    destruct H3 as [d2 [e2 [Hde2 [Hd2 [He2 H3]]]]].
    rewrite H3.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; last by apply He2. 
    rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
    rewrite Rabs_mult. rewrite nth_vec_to_list_float.
    rewrite inord_val. apply Rmult_le_compat_l; try apply Rabs_pos.
    rewrite nth_vec_to_list_float.
    rewrite inord_val. rewrite mxE.
    clear H3. apply BMULT_finite_e in H4.
    destruct H4 as [_ H4].  rewrite nth_vec_to_list_float in H4.
    rewrite inord_val in H4. rewrite mxE in H4.
    apply Bminus_bplus_opp_implies in H4.
    rewrite Bminus_bplus_opp_equiv; try apply H4.
    pose proof (@BPLUS_accurate' _ t).
    specialize (H3 (b' (inord k) ord0) 
                   (BOPP
                      ((A2_J A' *f x0')
                         (inord k) ord0)) H4).
    destruct H3 as [d3 [Hd3 H3]].
    rewrite H3. rewrite Rabs_mult.
    apply Rmult_le_compat; try apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat_l.
    assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
    { intros. by rewrite /FT2R B2R_Bopp. } rewrite H5.
    rewrite Rabs_Ropp. rewrite mxE.
    apply BPLUS_finite_e in H4.
    destruct H4 as [_ H4].
    apply finite_is_finite in H4. rewrite is_finite_Bopp in H4.
    rewrite mxE in H4.
    pose proof (@fma_dotprod_forward_error _ t).
    specialize (H6 (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                    (vec_to_list_float n.+1
                            (\col_j x0' j ord0))).
    rewrite !length_veclist in H6.
    assert (n.+1 = n.+1) by lia.
    specialize (H6 H7). clear H7.
    specialize (H6 (dotprod_r 
                      (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                      (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
    specialize (H6 (\sum_j (FT2R (A2_J A' (inord k) j) * FT2R (x0' j ord0))%Re)).
    specialize (H6 (\sum_j (Rabs (FT2R (A2_J A' (inord k) j)) * Rabs (FT2R (x0' j ord0)))%Re)).
    pose proof (@fma_dot_prod_rel_holds _ n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)). 
    specialize (H6 H7). clear H7.
    pose proof (@R_dot_prod_rel_holds n t n.+1 k (leqnn n.+1) (A2_J A')
                    (\col_j x0' j ord0)).
    assert (\sum_j
            (FT2R (A2_J A' (inord k) j) *
             FT2R (x0' j ord0))%Re = 
           \sum_(j < n.+1)
            (FT2R_mat (A2_J A') 
              (inord k)
              (widen_ord (m:=n.+1)
                 (leqnn n.+1) j) *
              FT2R_mat (\col_j0 x0' j0 ord0)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re).
    { apply eq_big. by []. intros. 
      assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H9. by rewrite !mxE.
    } rewrite -H8 in H7. specialize (H6 H7).
    clear H7 H8.
    pose proof (@R_dot_prod_rel_abs_holds n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)).
    rewrite -sum_fold_mathcomp_equiv in H7.
    assert (\sum_(j < n.+1)
              (FT2R_abs (FT2R_mat (A2_J A'))
                (inord k)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) *
              FT2R_abs
                (FT2R_mat
                   (\col_j0 x0' j0 ord0))
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re = 
            \sum_j
              (Rabs
                 (FT2R (A2_J A' (inord k) j)) *
               Rabs (FT2R (x0' j ord0)))%Re).
    { apply eq_big. by []. intros. 
      assert (widen_ord (m:=n.+1) (leqnn n.+1) i = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H9. by rewrite !mxE.
    } rewrite H8 in H7. specialize (H6 H7).
    clear H7 H8.
    rewrite finite_is_finite in H6.
    specialize (H6 H4).
    apply Rle_trans with 
    (Rabs
         (\sum_j
             (Rabs
                (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
     (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
    rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
    apply Rle_trans with 
    (Rabs
         (\sum_j
             ((FT2R (A2_J A' (inord k) j)) *
               (FT2R (x0' j ord0)))%Re) +
       Rabs
         (\sum_j
             (Rabs (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
     assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
     { intros. nra. } apply H7.
     eapply Rle_trans. apply Rabs_triang_inv.
     nra. repeat apply Rplus_le_compat_r.
     rewrite [in X in (_ <= X)%Re]sum_abs_eq.
     rewrite Rabs_sum_in. apply /RleP. apply Rabs_ineq.
     intros. apply Rmult_le_pos; apply Rabs_pos.
     rewrite sum_abs_eq. apply Rle_refl.
     intros. apply Rmult_le_pos; apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd3.
    rewrite inordK; (by apply /ssrnat.ltP).
    rewrite inordK; (by apply /ssrnat.ltP).
    rewrite inordK; (by apply /ssrnat.ltP).
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd2.
    apply Rlt_trans with
    ((sqrt (fun_bnd t n.+1) - default_abs t) /
            (1 + default_rel t) / (1 + default_rel t))%Re.
    apply fbnd.
    apply Rmult_lt_compat_r.
    apply Rinv_0_lt_compat.
    apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
    apply Rmult_lt_compat_r.
    apply Rinv_0_lt_compat.
    apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
    apply Rplus_lt_compat_r. by apply sqrt_fun_bnd_lt_fmax.
  - apply Bplus_no_ov_finite.
    * rewrite mxE.
      by apply finite_residual_0_aux3.
    * simpl. apply finite_is_finite. rewrite is_finite_Bopp.
      by apply finite_is_finite.
    * by apply no_overflow_x1_minus_x0.
Qed.


Lemma finite_in{t: type}  :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  @size_constraint t n ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  (forall i, finite (A' i i)) ->
  (forall i, finite (A1_inv_J A' i ord0)) ->
  (forall i, finite (b' i ord0)) ->
  forall xy, 
  In xy
       (combine
          (vec_to_list_float n.+1
             (vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1))
          (vec_to_list_float n.+1
             (vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1))) ->
  finite xy.1 /\ finite xy.2.
Proof.
intros ? ? ? ? ? ? ? ? ? ? size_cons HfA2 Hfx0 Hinp HfA HfA1_inv Hfb ? ?. 
apply in_rev in H1.
pose proof (@In_nth _ (rev (combine
                        (vec_to_list_float n.+1
                           (vector_inj
                              (resid
                                 (jacobi_n A b x0 0))
                              n.+1))
                        (vec_to_list_float n.+1
                           (vector_inj
                              (resid
                                 (jacobi_n A b x0 0))
                              n.+1)))) xy (Zconst t 0, Zconst t 0)).
specialize (H2 H1).
destruct H2 as [k [Hlen Hnth]].
rewrite rev_length combine_length !length_veclist Nat.min_id in Hlen.
rewrite rev_nth in Hnth.
rewrite combine_length !length_veclist Nat.min_id in Hnth.
assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
rewrite combine_nth in Hnth.
destruct xy . simpl. 
apply inject_pair_iff in Hnth.
destruct Hnth as [Hnth1 Hnth2].
rewrite -Hnth1 -Hnth2.
pose proof (@vector_residual_equiv t A b x0 0%nat).
assert (length b = length A). { by []. }
assert (length x0 = length A).
{ by rewrite repeat_length. }
specialize (H3 H4 H5 H). clear H4 H5.
rewrite H3. rewrite -/n.
rewrite H2.
rewrite !nth_vec_to_list_float.
rewrite mxE. 
split;
(apply  finite_residual_0_mult; try by [];
  rewrite -/n;rewrite inordK; try by apply /ssrnat.ltP; try apply Hlen;
  try apply Hlen).
apply Hlen.
apply Hlen.
by apply /ssrnat.ltP.
by rewrite !length_veclist.
by rewrite combine_length !length_veclist Nat.min_id.
Qed.


Lemma finite_residual_0 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  @size_constraint t (length A).-1 ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  (forall i, finite (A' i i)) ->
  (forall i, finite (A1_inv_J A' i ord0)) ->
  (forall i, finite (b' i ord0)) ->
  finite (norm2 (resid (jacobi_n A b x0 0))).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? HfA2 Hfx0 Hinp HfA HfA1_inv Hfb.
unfold norm2. 
assert ( length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite -/n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
apply dotprod_finite.
+ rewrite H2. apply g1_constraint_Sn. apply H1.
+ intros. apply in_rev in H3.
  pose proof (@In_nth _ (resid (jacobi_n A b x0 0)) xy (Zconst t 0) H3 ).
  destruct H4 as [k [Hlen Hnth]].
  pose proof (@v_equiv  t (resid (jacobi_n A b x0 0)) n H2).
  assert ((\col_j0 vector_inj
                     (resid (jacobi_n A b x0 0)) n.+1 j0  ord0) = 
           vector_inj (resid (jacobi_n A b x0 0)) n.+1).
  { apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
  rewrite H5 in H4. clear H5.
  rewrite H4 in Hnth. rewrite rev_nth in Hnth.
  rewrite length_veclist in Hnth.
  assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
  rewrite H5 in Hnth.
  pose proof (@vector_residual_equiv t A b x0 0%nat).
  assert (length b = length A). { by rewrite -H0. }
  specialize (H6 H7). clear H7.
  assert ( length x0 = length A ).
  { by rewrite repeat_length. } specialize (H6 H7). clear H7.
  specialize (H6 H). unfold resid in Hnth. rewrite -/n in H6.
  rewrite H6 in Hnth.
  rewrite nth_vec_to_list_float in Hnth.
  rewrite mxE in Hnth. rewrite -Hnth.
  split.
  - apply  finite_residual_0_mult; try by [].
    rewrite -/n. rewrite H2 in Hlen.
    rewrite inordK; try by apply /ssrnat.ltP.
    apply Hlen.
  - intros. unfold n0. rewrite rev_length. rewrite H2.
    pose proof (@BMULT_accurate' _ t).
    rewrite inordK.
    specialize (H7 (nth (n.+1.-1 - k)
                    (vec_to_list_float n.+1
                       (A1_J A')) (Zconst t 0))
                   (nth (n.+1.-1 - k)
                      (vec_to_list_float n.+1
                         (X_m_jacobi 1 x0' b' A' -f
                          X_m_jacobi 0 x0' b' A'))
                      (Zconst t 0))).
    assert (finite
             (BMULT
                (nth (n.+1.-1 - k)
                   (vec_to_list_float n.+1
                      (A1_J A')) (Zconst t 0))
                (nth (n.+1.-1 - k)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0)))).
    { apply  finite_residual_0_mult; try by [].
      rewrite -/n. by rewrite H2 in Hlen.
    }
    specialize (H7 H8).
    destruct H7 as [d [e [Hde [Hd [He H7]]]]].
    rewrite H7.
    rewrite !nth_vec_to_list_float.
    eapply Rle_lt_trans. apply Rabs_triang.
    eapply Rle_lt_trans. apply Rplus_le_compat_l. 
    apply He. rewrite Rabs_mult.
    eapply Rle_lt_trans. apply Rplus_le_compat_r.
    apply Rmult_le_compat_l. apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l.
    apply Hd. rewrite Rabs_mult.
    rewrite mxE. rewrite [in X in ( _ * X * _ + _ < _)%Re]mxE.
    apply BMULT_finite_e in H8.
    destruct H8 as [_ H8].
    rewrite nth_vec_to_list_float in H8.
    rewrite mxE in H8. 
    rewrite Bminus_bplus_opp_equiv.
    apply Bminus_bplus_opp_implies in H8.
    pose proof (@BPLUS_accurate' _ t).
    specialize (H9 (X_m_jacobi 1 x0' b' A' 
                      (inord k) ord0)
                  (BOPP
                    (X_m_jacobi 0 x0' b' A'
                       (inord k) ord0)) H8).
    destruct H9 as [d1 [Hd1 H9]].
    rewrite H9.
    rewrite [in X in (_ * Rabs ((_ + X) * _) * _ + _ < _)%Re]/FT2R B2R_Bopp.
    fold (@FT2R t). apply Rcomplements.Rlt_minus_r.
    apply Rcomplements.Rlt_div_r.
    apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
    rewrite Rabs_mult.  
    eapply Rle_lt_trans.   apply Rmult_le_compat_l.
    apply Rabs_pos. apply Rmult_le_compat_l.
    apply Rabs_pos. eapply Rle_trans.
    apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
    apply Hd1. rewrite -Rmult_assoc.
    apply Rcomplements.Rlt_div_r.
    apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
    assert (X_m_jacobi 0 x0' b' A' 
                  (inord k) ord0 = x0' (inord k) ord0).
    { by simpl. } rewrite H10. clear H10.
    eapply Rle_lt_trans. apply Rmult_le_compat_l.
    apply Rabs_pos. apply Rabs_triang.
    rewrite Rabs_Ropp. rewrite [in X in (_ * (X  + _) < _)%Re]mxE.
    rewrite !nth_vec_to_list_float. rewrite inord_val.
    clear H9.
    apply BPLUS_finite_e in H8.
    destruct H8 as [H8 _].
    rewrite mxE in H8.
    rewrite !nth_vec_to_list_float in H8.
    pose proof (@BMULT_accurate' _ t). rewrite inord_val in H8.
    specialize (H9 (A1_inv_J A' (inord k) ord0)
                    ((b' -f A2_J A' *f x0') 
                          (inord k) ord0) H8).
    destruct H9 as [d2 [e2 [Hde2 [Hd2 [He2 H9]]]]].
    rewrite H9.
    eapply Rle_lt_trans. apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Rplus_le_compat_r.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; last by apply He2.
    rewrite Rabs_mult. 
    apply Rmult_le_compat. apply Rabs_pos.
    apply Rabs_pos. 
    rewrite Rabs_mult.
    apply Rmult_le_compat_l. apply Rabs_pos.
    apply BMULT_finite_e in H8.
    destruct H8 as [_ H8].
    rewrite mxE in H8. rewrite mxE.
    apply Bminus_bplus_opp_implies in H8.
    rewrite Bminus_bplus_opp_equiv; last by apply H8.
    pose proof (@BPLUS_accurate' _ t).
    specialize (H10 (b' (inord k) ord0)
                    (BOPP
                      ((A2_J A' *f x0') 
                         (inord k) ord0)) H8).
    destruct H10 as [d3 [Hd3 H10]].
    rewrite H10. clear H10. rewrite Rabs_mult.
    apply Rmult_le_compat; try apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    assert (forall x: ftype t, FT2R (BOPP x) = (- FT2R x)%Re).
    { intros. unfold FT2R. by rewrite B2R_Bopp. }
    rewrite H10. rewrite Rabs_Ropp.
    apply Rplus_le_compat_l. rewrite mxE.
    pose proof (@fma_dotprod_forward_error _ t).
    specialize (H11 (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                    (vec_to_list_float n.+1
                            (\col_j x0' j ord0))).
    rewrite !length_veclist in H11.
    assert (n.+1 = n.+1) by lia.
    specialize (H11 H12). clear H12.
    specialize (H11 (dotprod_r 
                      (vec_to_list_float n.+1
                        (\row_j A2_J A' (inord k) j)^T)
                      (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
    specialize (H11 (\sum_j (FT2R (A2_J A' (inord k) j) * FT2R (x0' j ord0))%Re)).
    specialize (H11 (\sum_j (Rabs (FT2R (A2_J A' (inord k) j)) * Rabs (FT2R (x0' j ord0)))%Re)).
    pose proof (@fma_dot_prod_rel_holds _ n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)). 
    specialize (H11 H12). clear H12.
    pose proof (@R_dot_prod_rel_holds n t n.+1 k (leqnn n.+1) (A2_J A')
                    (\col_j x0' j ord0)).
    assert (\sum_j
            (FT2R (A2_J A' (inord k) j) *
             FT2R (x0' j ord0))%Re = 
           \sum_(j < n.+1)
            (FT2R_mat (A2_J A') 
              (inord k)
              (widen_ord (m:=n.+1)
                 (leqnn n.+1) j) *
              FT2R_mat (\col_j0 x0' j0 ord0)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re).
    { apply eq_big. by []. intros. 
      assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H14. by rewrite !mxE.
    } rewrite -H13 in H12. specialize (H11 H12).
    clear H12 H13.
    pose proof (@R_dot_prod_rel_abs_holds n t n.+1 k (A2_J A')
                    (\col_j x0' j ord0)).
    rewrite -sum_fold_mathcomp_equiv in H12.
    assert (\sum_(j < n.+1)
              (FT2R_abs (FT2R_mat (A2_J A'))
                (inord k)
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) *
              FT2R_abs
                (FT2R_mat
                   (\col_j0 x0' j0 ord0))
                (widen_ord (m:=n.+1)
                   (leqnn n.+1) j) ord0)%Re = 
            \sum_j
              (Rabs
                 (FT2R (A2_J A' (inord k) j)) *
               Rabs (FT2R (x0' j ord0)))%Re).
    { apply eq_big. by []. intros. 
      assert (widen_ord (m:=n.+1) (leqnn n.+1) i = i).
      { unfold widen_ord. 
        apply val_inj. by simpl.
      } rewrite H14. by rewrite !mxE.
    } rewrite H13 in H12. specialize (H11 H12).
    clear H12 H13.
    apply BPLUS_finite_e in H8.
    destruct H8 as [_ H8].
    apply finite_is_finite in H8.
    rewrite is_finite_Bopp in H8.
    rewrite finite_is_finite in H11.
    rewrite mxE in H8. specialize (H11 H8).
    apply Rle_trans with 
    (Rabs
         (\sum_j
             (Rabs
                (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
     (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
    rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
    apply Rle_trans with 
    (Rabs
         (\sum_j
             ((FT2R (A2_J A' (inord k) j)) *
               (FT2R (x0' j ord0)))%Re) +
       Rabs
         (\sum_j
             (Rabs (FT2R (A2_J A' (inord k) j)) *
              Rabs (FT2R (x0' j ord0)))%Re) *
       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
     assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
     { intros. nra. } apply H12.
     eapply Rle_trans. apply Rabs_triang_inv.
     nra. repeat apply Rplus_le_compat_r.
     rewrite [in X in (_ <= X)%Re]sum_abs_eq.
     rewrite Rabs_sum_in. apply /RleP. apply Rabs_ineq.
     intros. apply Rmult_le_pos; apply Rabs_pos.
     rewrite sum_abs_eq. apply Rle_refl.
     intros. apply Rmult_le_pos; apply Rabs_pos.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd3.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd2.
    apply Hinp.
    rewrite H2 in Hlen.
    rewrite inordK; (try by apply /ssrnat.ltP) .
    rewrite H2 in Hlen.
    rewrite inordK; (try by apply /ssrnat.ltP) .
    rewrite H2 in Hlen.
    rewrite inordK; (try by apply /ssrnat.ltP) .
    rewrite H2 in Hlen.
    rewrite inordK; (try by apply /ssrnat.ltP) .
    by apply Bminus_bplus_opp_implies.
    rewrite H2 in Hlen. by apply /ssrnat.ltP .
    rewrite H2 in Hlen. by apply /ssrnat.ltP .
    rewrite H2 in Hlen. by apply /ssrnat.ltP .
    rewrite H2 in Hlen. by apply /ssrnat.ltP .
  - rewrite H2 in Hlen. by apply /ssrnat.ltP.
  - rewrite H2 in Hlen. by rewrite length_veclist.
Qed.



Lemma finite_implies_1 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A':= (@matrix_inj _ A n.+1 n.+1) in
  let b' := (@vector_inj _ b n.+1) in
  let x0' := (@vector_inj _ x0 n.+1) in
  finite (norm2 (resid (jacobi_n A b x0 0)))->
(forall xy : ftype t * ftype t,
             In xy (combine
                        (vec_to_list_float n.+1
                                  (A1_J A'))
                        (vec_to_list_float n.+1
                                  (X_m_jacobi 1 x0' b' A' -f
                                   X_m_jacobi 0 x0' b' A'))) ->
   finite xy.1 /\
   finite xy.2 /\
   finite (BMULT xy.1 xy.2)).
Proof.
intros.
unfold norm2 in H1.
pose proof (@dotprod_finite_implies t).
specialize (H3 (rev (resid (jacobi_n A b x0 0)))).
rewrite rev_involutive in H3.
specialize (H3 H1).
assert (Hrlen: length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite /n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
specialize (H3 (BMULT xy.1 xy.2)).
assert (finite (BMULT xy.1 xy.2)).
{ apply H3. apply in_rev in H2.
  pose proof (@In_nth _ (rev (combine
                        (vec_to_list_float n.+1
                           (A1_J A'))
                        (vec_to_list_float n.+1
                           (X_m_jacobi 1 x0' b' A' -f
                            X_m_jacobi 0 x0' b' A')))) xy (Zconst t 0, Zconst t 0)).
  specialize (H4 H2).
  destruct H4 as [k [Hlen Hnth]].
  rewrite rev_length combine_length !length_veclist Nat.min_id in Hlen.
  assert (BMULT xy.1 xy.2 = 
          nth k (resid (jacobi_n A b x0 0)) (Zconst t 0)).
  { assert (resid (jacobi_n A b x0 0) = 
             rev (vec_to_list_float n.+1
                (\col_j0 vector_inj (resid (jacobi_n A b x0 0)) n.+1 j0 ord0))).
    { apply v_equiv. by rewrite Hrlen.  
    } rewrite H4. 
    rewrite rev_nth. rewrite length_veclist.
    assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
    rewrite H5.
    assert ( (\col_j0 vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1 j0 ord0) = 
                @vector_inj _  (resid (jacobi_n A b x0 0)) n.+1).
    {  apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H6. rewrite vector_residual_equiv; try by [].
    rewrite -/n. rewrite nth_vec_to_list_float.
    rewrite mxE. rewrite -/A' -/b' -/x0'.
    destruct xy. rewrite rev_combine in Hnth.
    rewrite combine_nth in Hnth.
    rewrite [in LHS]/=. rewrite !rev_nth !length_veclist in Hnth.
    rewrite !H5 in Hnth. apply inject_pair_iff in Hnth.
    destruct Hnth as [Hnth1 Hnth2]. 
    rewrite -Hnth1 -Hnth2.
    rewrite inordK; try by apply Hlen.  by [].
    apply /ssrnat.ltP. apply Hlen.
    apply Hlen.
    apply Hlen.
    by rewrite !rev_length !length_veclist.
    by rewrite !length_veclist.
    apply /ssrnat.ltP. apply Hlen.
    unfold x0. by rewrite repeat_length.
    by rewrite length_veclist.
  }rewrite H4.
  rewrite in_rev. rewrite rev_involutive.
  apply nth_In. rewrite Hrlen. apply Hlen.
}
repeat split; try apply H4; try (apply BMULT_finite_e in H4; apply H4).
Qed.

Lemma finite_implies_2 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A':= (@matrix_inj _ A n.+1 n.+1) in
  let b' := (@vector_inj _ b n.+1) in
  let x0' := (@vector_inj _ x0 n.+1) in
  finite (norm2 (resid (jacobi_n A b x0 0))) ->
  (forall xy : ftype t * ftype t,
            In xy
                (combine
                    (vec_to_list_float n.+1
                        (diag_vector_mult
                            (A1_inv_J A')
                                 (b' -f A2_J A' *f x0')))
                                  (vec_to_list_float n.+1 x0')) ->
             finite xy.1 /\
             finite xy.2 /\
             finite (BPLUS xy.1 (BOPP xy.2)) ).
Proof.
intros.
unfold norm2 in H1.
pose proof (@dotprod_finite_implies t).
specialize (H3 (rev (resid (jacobi_n A b x0 0)))).
rewrite rev_involutive in H3.
specialize (H3 H1). apply in_rev in H2.
pose proof (@In_nth _ (rev
                        (combine
                           (vec_to_list_float n.+1
                              (diag_vector_mult
                                 (A1_inv_J A')
                                 (b' -f
                                  A2_J A' *f x0')))
                           (vec_to_list_float n.+1
                              x0'))) xy (Zconst t 0, Zconst t 0)).
specialize (H4 H2).
destruct H4 as [k [Hlen Hnth]].
assert (Hrlen: length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite /n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
rewrite rev_length combine_length !length_veclist Nat.min_id in Hlen.
specialize (H3 (BMULT
                  (nth (n.+1.-1 - @inord n k)
                     (vec_to_list_float n.+1 (A1_J A'))
                     (Zconst t 0))
                  (nth (n.+1.-1 - @inord n k)
                     (vec_to_list_float n.+1
                        (X_m_jacobi 1 x0' b' A' -f
                         X_m_jacobi 0 x0' b' A'))
                     (Zconst t 0)))).
assert (In
             (BMULT
                (nth (n.+1.-1 - @inord n k)
                   (vec_to_list_float n.+1
                      (A1_J A')) 
                   (Zconst t 0))
                (nth (n.+1.-1 - @inord n k)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0)))
             (rev (resid (jacobi_n A b x0 0)))).
{ rewrite inordK.
  assert ((BMULT
           (nth (n.+1.-1 - k)
              (vec_to_list_float n.+1
                 (A1_J A')) (Zconst t 0))
           (nth (n.+1.-1 - k)
              (vec_to_list_float n.+1
                 (X_m_jacobi 1 x0' b' A' -f
                  X_m_jacobi 0 x0' b' A'))
              (Zconst t 0))) = 
          nth k (resid (jacobi_n A b x0 0)) (Zconst t 0)).
  { assert (resid (jacobi_n A b x0 0) = 
             rev (vec_to_list_float n.+1
                (\col_j0 vector_inj (resid (jacobi_n A b x0 0)) n.+1 j0 ord0))).
    { apply v_equiv. by rewrite Hrlen.  
    } rewrite H4. 
    rewrite rev_nth. rewrite length_veclist.
    assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
    rewrite H5.
    assert ( (\col_j0 vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1 j0 ord0) = 
                @vector_inj _  (resid (jacobi_n A b x0 0)) n.+1).
    {  apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H6. rewrite vector_residual_equiv; try by [].
    rewrite -/n. rewrite -/A' -/b' -/x0'.
    unfold residual_math. rewrite [in RHS]nth_vec_to_list_float.
    rewrite mxE. rewrite inordK. by [].
    by apply /ssrnat.ltP.
    by apply /ssrnat.ltP.
    by rewrite repeat_length. 
    by rewrite length_veclist.
  } rewrite H4. rewrite in_rev.
  rewrite rev_involutive.
  apply nth_In. by rewrite Hrlen.
  by apply /ssrnat.ltP.
}
specialize (H3 H4).
apply BMULT_finite_e in H3.
destruct H3 as [H31 H32]. rewrite inordK in H32.
rewrite nth_vec_to_list_float in H32.
rewrite mxE in H32.
apply Bminus_bplus_opp_implies in H32.
destruct xy.
rewrite rev_nth combine_length !length_veclist Nat.min_id in Hnth.
assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
rewrite H3 in Hnth.
rewrite combine_nth in Hnth.
apply inject_pair_iff in Hnth.
simpl.
destruct Hnth as [Hnth1 Hnth2].
assert (X_m_jacobi 1 x0' b' A' (inord k) ord0 = 
        nth (n.+1.-1 - k)%coq_nat
          (vec_to_list_float n.+1
             (diag_vector_mult
                (A1_inv_J A')
                (b' -f A2_J A' *f x0')))
          (Zconst t 0)).
{ rewrite mxE. rewrite [in RHS]nth_vec_to_list_float.
  rewrite mxE. by [].
  by apply /ssrnat.ltP.
} rewrite -H5 in Hnth1.
assert (X_m_jacobi 0 x0' b' A' (inord k) ord0 = 
        nth (n.+1.-1 - k)%coq_nat
          (vec_to_list_float n.+1 x0')
          (Zconst t 0)).
{ rewrite mxE. rewrite [in RHS]nth_vec_to_list_float.
  rewrite mxE. by [].
  by apply /ssrnat.ltP.
} rewrite -H6 in Hnth2.
rewrite -Hnth1 -Hnth2.
repeat split; try apply H32.
apply BPLUS_finite_e in H32.
apply H32.
apply BPLUS_finite_e in H32.
destruct H32 as [_ H32].
apply finite_is_finite in H32.
rewrite is_finite_Bopp in H32.
by apply finite_is_finite.
by rewrite !length_veclist.
apply Hlen.
by apply /ssrnat.ltP.
by apply /ssrnat.ltP.
Qed.


Lemma finite_implies_3 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A':= (@matrix_inj _ A n.+1 n.+1) in
  let b' := (@vector_inj _ b n.+1) in
  let x0' := (@vector_inj _ x0 n.+1) in
  finite (norm2 (resid (jacobi_n A b x0 0))) ->
  (forall xy : ftype t * ftype t,
                         In xy
                           (combine
                              (vec_to_list_float n.+1
                                 (A1_inv_J A'))
                              (vec_to_list_float n.+1
                                 (b' -f A2_J A' *f x0'))) ->
                         finite xy.1 /\
                         finite xy.2 /\
                         finite (BMULT xy.1 xy.2)).
Proof.
intros.
intros.
unfold norm2 in H1.
pose proof (@dotprod_finite_implies t).
specialize (H3 (rev (resid (jacobi_n A b x0 0)))).
rewrite rev_involutive in H3.
specialize (H3 H1). apply in_rev in H2.
pose proof (@In_nth _ (rev
                      (combine
                         (vec_to_list_float n.+1
                            (A1_inv_J A'))
                         (vec_to_list_float n.+1
                            (b' -f A2_J A' *f x0')))) xy (Zconst t 0, Zconst t 0)).
specialize (H4 H2).
destruct H4 as [k [Hlen Hnth]].
assert (Hrlen: length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite /n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
rewrite rev_length combine_length !length_veclist Nat.min_id in Hlen.
specialize (H3 (BMULT
                  (nth (n.+1.-1 - @inord n k)
                     (vec_to_list_float n.+1 (A1_J A'))
                     (Zconst t 0))
                  (nth (n.+1.-1 - @inord n k)
                     (vec_to_list_float n.+1
                        (X_m_jacobi 1 x0' b' A' -f
                         X_m_jacobi 0 x0' b' A'))
                     (Zconst t 0)))).
assert (In
             (BMULT
                (nth (n.+1.-1 - @inord n k)
                   (vec_to_list_float n.+1
                      (A1_J A')) 
                   (Zconst t 0))
                (nth (n.+1.-1 - @inord n k)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0)))
             (rev (resid (jacobi_n A b x0 0)))).
{ rewrite inordK.
  assert ((BMULT
           (nth (n.+1.-1 - k)
              (vec_to_list_float n.+1
                 (A1_J A')) (Zconst t 0))
           (nth (n.+1.-1 - k)
              (vec_to_list_float n.+1
                 (X_m_jacobi 1 x0' b' A' -f
                  X_m_jacobi 0 x0' b' A'))
              (Zconst t 0))) = 
          nth k (resid (jacobi_n A b x0 0)) (Zconst t 0)).
  { assert (resid (jacobi_n A b x0 0) = 
             rev (vec_to_list_float n.+1
                (\col_j0 vector_inj (resid (jacobi_n A b x0 0)) n.+1 j0 ord0))).
    { apply v_equiv. by rewrite Hrlen.  
    } rewrite H4. 
    rewrite rev_nth. rewrite length_veclist.
    assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
    rewrite H5.
    assert ( (\col_j0 vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1 j0 ord0) = 
                @vector_inj _  (resid (jacobi_n A b x0 0)) n.+1).
    {  apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H6. rewrite vector_residual_equiv; try by [].
    rewrite -/n. rewrite -/A' -/b' -/x0'.
    unfold residual_math. rewrite [in RHS]nth_vec_to_list_float.
    rewrite mxE. rewrite inordK. by [].
    by apply /ssrnat.ltP.
    by apply /ssrnat.ltP.
    by rewrite repeat_length. 
    by rewrite length_veclist.
  } rewrite H4. rewrite in_rev.
  rewrite rev_involutive.
  apply nth_In. by rewrite Hrlen.
  by apply /ssrnat.ltP.
}
specialize (H3 H4).
apply BMULT_finite_e in H3.
destruct H3 as [_ H3].
rewrite inordK in H3.
rewrite nth_vec_to_list_float in H3.
rewrite mxE in H3.
apply Bminus_bplus_opp_implies in H3.
apply BPLUS_finite_e in H3.
destruct H3 as [H3 _]. rewrite mxE in H3.
rewrite inordK in H3.
destruct xy .
rewrite rev_nth combine_length !length_veclist Nat.min_id in Hnth.
assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
rewrite H5 in Hnth.
rewrite combine_nth in Hnth.
apply inject_pair_iff in Hnth.
simpl.
destruct Hnth as [Hnth1 Hnth2].
rewrite -Hnth1 -Hnth2.
repeat split; try apply H3.
apply BMULT_finite_e in H3.
apply H3.
apply BMULT_finite_e in H3.
apply H3.
by rewrite !length_veclist.
apply Hlen.
by apply /ssrnat.ltP.
by apply /ssrnat.ltP.
by apply /ssrnat.ltP.
Qed.


Lemma finite_implies_4 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A':= (@matrix_inj _ A n.+1 n.+1) in
  let b' := (@vector_inj _ b n.+1) in
  let x0' := (@vector_inj _ x0 n.+1) in
  finite (norm2 (resid (jacobi_n A b x0 0))) ->
(forall xy : ftype t * ftype t,
                           In xy
                             (combine
                                (vec_to_list_float n.+1 b')
                                (vec_to_list_float n.+1
                                   (A2_J A' *f x0'))) ->
                           finite xy.1 /\
                           finite xy.2 /\
                           finite (BPLUS xy.1 (BOPP xy.2)) ).
Proof.
intros.
intros.
unfold norm2 in H1.
pose proof (@dotprod_finite_implies t).
specialize (H3 (rev (resid (jacobi_n A b x0 0)))).
rewrite rev_involutive in H3.
specialize (H3 H1). apply in_rev in H2.
pose proof (@In_nth _ (rev
          (combine
             (vec_to_list_float n.+1 b')
             (vec_to_list_float n.+1
                (A2_J A' *f x0')))) xy (Zconst t 0, Zconst t 0)).
specialize (H4 H2).
destruct H4 as [k [Hlen Hnth]].
assert (Hrlen: length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite /n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
rewrite rev_length combine_length !length_veclist Nat.min_id in Hlen.
specialize (H3 (BMULT
                  (nth (n.+1.-1 - @inord n k)
                     (vec_to_list_float n.+1 (A1_J A'))
                     (Zconst t 0))
                  (nth (n.+1.-1 - @inord n k)
                     (vec_to_list_float n.+1
                        (X_m_jacobi 1 x0' b' A' -f
                         X_m_jacobi 0 x0' b' A'))
                     (Zconst t 0)))).
assert (In
             (BMULT
                (nth (n.+1.-1 - @inord n k)
                   (vec_to_list_float n.+1
                      (A1_J A')) 
                   (Zconst t 0))
                (nth (n.+1.-1 - @inord n k)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0)))
             (rev (resid (jacobi_n A b x0 0)))).
{ rewrite inordK.
  assert ((BMULT
           (nth (n.+1.-1 - k)
              (vec_to_list_float n.+1
                 (A1_J A')) (Zconst t 0))
           (nth (n.+1.-1 - k)
              (vec_to_list_float n.+1
                 (X_m_jacobi 1 x0' b' A' -f
                  X_m_jacobi 0 x0' b' A'))
              (Zconst t 0))) = 
          nth k (resid (jacobi_n A b x0 0)) (Zconst t 0)).
  { assert (resid (jacobi_n A b x0 0) = 
             rev (vec_to_list_float n.+1
                (\col_j0 vector_inj (resid (jacobi_n A b x0 0)) n.+1 j0 ord0))).
    { apply v_equiv. by rewrite Hrlen.  
    } rewrite H4. 
    rewrite rev_nth. rewrite length_veclist.
    assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
    rewrite H5.
    assert ( (\col_j0 vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1 j0 ord0) = 
                @vector_inj _  (resid (jacobi_n A b x0 0)) n.+1).
    {  apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H6. rewrite vector_residual_equiv; try by [].
    rewrite -/n. rewrite -/A' -/b' -/x0'.
    unfold residual_math. rewrite [in RHS]nth_vec_to_list_float.
    rewrite mxE. rewrite inordK. by [].
    by apply /ssrnat.ltP.
    by apply /ssrnat.ltP.
    by rewrite repeat_length. 
    by rewrite length_veclist.
  } rewrite H4. rewrite in_rev.
  rewrite rev_involutive.
  apply nth_In. by rewrite Hrlen.
  by apply /ssrnat.ltP.
}
specialize (H3 H4).
apply BMULT_finite_e in H3.
destruct H3 as [_ H3].
rewrite nth_vec_to_list_float in H3.
rewrite mxE in H3.
apply Bminus_bplus_opp_implies in H3.
apply BPLUS_finite_e in H3.
destruct H3 as [H3 _]. rewrite inord_val in H3.
rewrite mxE in H3.
apply BMULT_finite_e in H3.
destruct H3 as [_ H3].
rewrite inordK in H3.
rewrite nth_vec_to_list_float in H3.
rewrite mxE in H3.
apply Bminus_bplus_opp_implies in H3.
rewrite rev_nth in Hnth.
rewrite combine_length !length_veclist Nat.min_id in Hnth.
rewrite combine_nth in Hnth.
assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
rewrite H5 in Hnth.
destruct xy .
simpl.
apply inject_pair_iff in Hnth.
simpl.
destruct Hnth as [Hnth1 Hnth2].
rewrite -Hnth1 -Hnth2.
repeat split; try apply H3.
apply BPLUS_finite_e in H3.
destruct H3 as [H31 H32].
rewrite nth_vec_to_list_float.
apply H31.
by apply /ssrnat.ltP.
rewrite nth_vec_to_list_float.
apply BPLUS_finite_e in H3.
destruct H3 as [H31 H32].
apply finite_is_finite .
apply finite_is_finite in H32.
by rewrite is_finite_Bopp in H32.
by apply /ssrnat.ltP.
rewrite !nth_vec_to_list_float.
apply H3.
by apply /ssrnat.ltP.
by apply /ssrnat.ltP.
by rewrite !length_veclist.
by rewrite combine_length !length_veclist Nat.min_id.
by apply /ssrnat.ltP.
by apply /ssrnat.ltP.
rewrite inordK; by apply /ssrnat.ltP.
Qed.


Lemma finite_implies_5 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A':= (@matrix_inj _ A n.+1 n.+1) in
  let b' := (@vector_inj _ b n.+1) in
  let x0' := (@vector_inj _ x0 n.+1) in
  finite (norm2 (resid (jacobi_n A b x0 0))) ->
  (forall (xy : ftype t * ftype t)
                           (i : 'I_n.+1),
                         In xy
                           (combine
                              (vec_to_list_float n.+1
                                 (\row_j A2_J A'
                                          (inord i) j)^T)
                              (vec_to_list_float n.+1
                                 x0')) ->
                         finite xy.1 /\
                         finite xy.2).
Proof.
intros.
unfold norm2 in H1.
pose proof (@dotprod_finite_implies t).
specialize (H3 (rev (resid (jacobi_n A b x0 0)))).
rewrite rev_involutive in H3.
specialize (H3 H1). apply in_rev in H2.
pose proof (@In_nth _ (rev
                (combine
                   (vec_to_list_float n.+1
                      (\row_j A2_J A'
                               (inord i) j)^T)
                   (vec_to_list_float n.+1
                      x0'))) xy (Zconst t 0, Zconst t 0)).
specialize (H4 H2).
destruct H4 as [k [Hlen Hnth]].
assert (Hrlen: length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite /n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
rewrite rev_length combine_length !length_veclist Nat.min_id in Hlen.
specialize (H3 (BMULT
                  (nth (n.+1.-1 - i)
                     (vec_to_list_float n.+1 (A1_J A'))
                     (Zconst t 0))
                  (nth (n.+1.-1 - i)
                     (vec_to_list_float n.+1
                        (X_m_jacobi 1 x0' b' A' -f
                         X_m_jacobi 0 x0' b' A'))
                     (Zconst t 0)))).
assert (In
             (BMULT
                (nth (n.+1.-1 - i)
                   (vec_to_list_float n.+1
                      (A1_J A')) 
                   (Zconst t 0))
                (nth (n.+1.-1 - i)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0)))
             (rev (resid (jacobi_n A b x0 0)))).
{ assert ((BMULT
           (nth (n.+1.-1 - i)
              (vec_to_list_float n.+1
                 (A1_J A')) (Zconst t 0))
           (nth (n.+1.-1 - i)
              (vec_to_list_float n.+1
                 (X_m_jacobi 1 x0' b' A' -f
                  X_m_jacobi 0 x0' b' A'))
              (Zconst t 0))) = 
          nth i (resid (jacobi_n A b x0 0)) (Zconst t 0)).
  { assert (resid (jacobi_n A b x0 0) = 
             rev (vec_to_list_float n.+1
                (\col_j0 vector_inj (resid (jacobi_n A b x0 0)) n.+1 j0 ord0))).
    { apply v_equiv. by rewrite Hrlen.  
    } rewrite H4. 
    rewrite rev_nth. rewrite length_veclist.
    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat) by lia.
    rewrite H5.
    assert ( (\col_j0 vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1 j0 ord0) = 
                @vector_inj _  (resid (jacobi_n A b x0 0)) n.+1).
    {  apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H6. rewrite vector_residual_equiv; try by [].
    rewrite -/n. rewrite -/A' -/b' -/x0'.
    unfold residual_math. rewrite [in RHS]nth_vec_to_list_float.
    rewrite mxE. rewrite inordK. by []. apply ltn_ord.
    apply ltn_ord.
    by rewrite repeat_length. 
    rewrite length_veclist. apply /ssrnat.ltP. apply ltn_ord.
  } rewrite H4. rewrite in_rev.
  rewrite rev_involutive.
  apply nth_In. rewrite Hrlen.
  apply /ssrnat.ltP. apply ltn_ord.
}
specialize (H3 H4).
rewrite rev_nth in Hnth.
rewrite combine_length !length_veclist Nat.min_id in Hnth.
apply BMULT_finite_e in H3.
destruct H3 as [_ H3].
rewrite nth_vec_to_list_float in H3.
rewrite mxE in H3.
apply Bminus_bplus_opp_implies in H3.
apply BPLUS_finite_e  in H3.
destruct H3 as [H3 _].
rewrite mxE in H3.
apply BMULT_finite_e in H3.
destruct H3 as [_ H3].
rewrite inord_val in H3.
rewrite nth_vec_to_list_float in H3.
rewrite mxE in H3.
apply Bminus_bplus_opp_implies in H3.
apply BPLUS_finite_e  in H3.
destruct H3 as [_ H3].
apply finite_is_finite in H3.
rewrite is_finite_Bopp in H3.
rewrite mxE in H3.
pose proof (@fma_jacobi_forward_error.dotprod_finite_implies _ t).
specialize (H5 (combine (vec_to_list_float n.+1
                           (\row_j A2_J A' (inord i) j)^T)
                        (vec_to_list_float n.+1
                            (\col_j x0' j ord0)))).
rewrite finite_is_finite in H5.
rewrite combine_split  in H5.
assert ((vec_to_list_float n.+1
             (\row_j A2_J A' 
                       (inord i) j)^T,
           vec_to_list_float n.+1
             (\col_j x0' j ord0)).1 = 
        vec_to_list_float n.+1
             (\row_j A2_J A' 
                       (inord i) j)^T) by auto.
assert ((vec_to_list_float n.+1
             (\row_j A2_J A' 
                       (inord i) j)^T,
           vec_to_list_float n.+1
             (\col_j x0' j ord0)).2 = 
          vec_to_list_float n.+1
             (\col_j x0' j ord0)) by auto.
rewrite H6 H7 in H5. clear H6 H7.
specialize (H5 H3).
specialize (H5 xy).
assert ((\col_j x0' j ord0) = x0').
{ apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
rewrite H6 in H5. apply in_rev in H2.
specialize (H5 H2).
apply H5.
by rewrite !length_veclist.
apply ltn_ord.
apply ltn_ord.
by rewrite combine_length !length_veclist Nat.min_id.
Qed.


Lemma finite_implies_6 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A':= (@matrix_inj _ A n.+1 n.+1) in
  let b' := (@vector_inj _ b n.+1) in
  let x0' := (@vector_inj _ x0 n.+1) in
  finite (norm2 (resid (jacobi_n A b x0 0))) ->
  (forall i : 'I_n.+1,
                       finite 
                         (let l1 :=
                            vec_to_list_float n.+1
                              (\row_j A2_J A'
                                        (inord i) j)^T
                            in
                          let l2 :=
                            vec_to_list_float n.+1
                              (\col_j x0' j 0) in
                          dotprod_r l1 l2)) .
Proof.
intros.
unfold norm2 in H1.
pose proof (@dotprod_finite_implies t).
specialize (H2 (rev (resid (jacobi_n A b x0 0)))).
rewrite rev_involutive in H2.
specialize (H2 H1). 
assert (Hrlen: length (resid (jacobi_n A b x0 0)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. rewrite iter_length.
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite /n prednK. by []. by apply /ssrnat.ltP.
    by []. by rewrite /x0 repeat_length.
}
specialize (H2 (BMULT
                  (nth (n.+1.-1 - i)
                     (vec_to_list_float n.+1 (A1_J A'))
                     (Zconst t 0))
                  (nth (n.+1.-1 - i)
                     (vec_to_list_float n.+1
                        (X_m_jacobi 1 x0' b' A' -f
                         X_m_jacobi 0 x0' b' A'))
                     (Zconst t 0)))).
assert (In
             (BMULT
                (nth (n.+1.-1 - i)
                   (vec_to_list_float n.+1
                      (A1_J A')) 
                   (Zconst t 0))
                (nth (n.+1.-1 - i)
                   (vec_to_list_float n.+1
                      (X_m_jacobi 1 x0' b' A' -f
                       X_m_jacobi 0 x0' b' A'))
                   (Zconst t 0)))
             (rev (resid (jacobi_n A b x0 0)))).
{ assert ((BMULT
           (nth (n.+1.-1 - i)
              (vec_to_list_float n.+1
                 (A1_J A')) (Zconst t 0))
           (nth (n.+1.-1 - i)
              (vec_to_list_float n.+1
                 (X_m_jacobi 1 x0' b' A' -f
                  X_m_jacobi 0 x0' b' A'))
              (Zconst t 0))) = 
          nth i (resid (jacobi_n A b x0 0)) (Zconst t 0)).
  { assert (resid (jacobi_n A b x0 0) = 
             rev (vec_to_list_float n.+1
                (\col_j0 vector_inj (resid (jacobi_n A b x0 0)) n.+1 j0 ord0))).
    { apply v_equiv. by rewrite Hrlen.  
    } rewrite H3. 
    rewrite rev_nth. rewrite length_veclist.
    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat) by lia.
    rewrite H4.
    assert ( (\col_j0 vector_inj
                (resid
                   (jacobi_n A b x0 0))
                n.+1 j0 ord0) = 
                @vector_inj _  (resid (jacobi_n A b x0 0)) n.+1).
    {  apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H5. rewrite vector_residual_equiv; try by [].
    rewrite -/n. rewrite -/A' -/b' -/x0'.
    unfold residual_math. rewrite [in RHS]nth_vec_to_list_float.
    rewrite mxE. rewrite inordK. by []. apply ltn_ord.
    apply ltn_ord.
    by rewrite repeat_length. 
    rewrite length_veclist. apply /ssrnat.ltP. apply ltn_ord.
  } rewrite H3. rewrite in_rev.
  rewrite rev_involutive.
  apply nth_In. rewrite Hrlen.
  apply /ssrnat.ltP. apply ltn_ord.
}
specialize (H2 H3).
apply BMULT_finite_e in H2.
destruct H2 as [_ H2].
rewrite nth_vec_to_list_float in H2.
rewrite mxE in H2.
apply Bminus_bplus_opp_implies in H2.
apply BPLUS_finite_e in H2.
destruct H2 as [H2 _].
rewrite mxE in H2.
apply BMULT_finite_e in H2.
destruct H2 as [_ H2].
rewrite nth_vec_to_list_float in H2.
rewrite mxE in H2.
apply Bminus_bplus_opp_implies in H2.
apply BPLUS_finite_e in H2.
destruct H2 as [_ H2].
rewrite inord_val in H2.
rewrite mxE in H2.
apply finite_is_finite in H2. 
rewrite is_finite_Bopp in H2.
apply finite_is_finite.
apply H2.
rewrite inordK; apply ltn_ord.
apply ltn_ord.
Qed.


Lemma rho_0_implies_N_eq_0 {t} {n:nat} 
  (A: 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1):
  rho_def A b = 0%Re ->
  matrix_inf_norm (FT2R_mat (A2_J A)) = 0%Re.
Proof.
intros.
unfold rho_def in H.
apply Rplus_eq_R0 in H.
+ destruct H as [Hrho1 Hrho2].
  rewrite Hrho2 in Hrho1. rewrite Rmult_0_r in Hrho1.
  rewrite Rplus_0_l in Hrho1.
  assert (0%Re = ((((1 + g t n.+1) *
                   (1 + default_rel t) *
                   g t n.+1 +
                   default_rel t *
                   (1 + g t n.+1) + 
                   g t n.+1) * default_abs t +
                  default_abs t) * 0)%Re). 
  { nra. } rewrite H in Hrho1.
  apply Rmult_eq_reg_l in Hrho1.
  assert (FT2R_mat (A2_J A)= A2_J_real (FT2R_mat A)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE.
    case: (x == y :> nat); by simpl.
  } rewrite H0. apply Hrho1.
  assert (forall x:R, (0 < x)%Re -> x <> 0%Re).
  { intros. nra. } apply H0.
  apply Rplus_le_lt_0_compat; last by apply default_abs_gt_0.
  apply Rmult_le_pos; last by apply default_abs_ge_0.
  apply Rplus_le_le_0_compat; last by apply g_pos.
  apply Rplus_le_le_0_compat.
  repeat apply Rmult_le_pos; try by apply g_pos.
  apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  apply Rmult_le_pos; first by apply default_rel_ge_0.
  apply Rplus_le_le_0_compat; try nra; try apply g_pos.
+ repeat apply Rplus_le_le_0_compat.
  - repeat apply Rmult_le_pos; try (apply /RleP; apply vec_norm_pd);
    try (apply /RleP; apply matrix_norm_pd).
    apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
    repeat apply Rmult_le_pos; last by 
    (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
    apply Rplus_le_le_0_compat; try apply g_pos.
    apply Rplus_le_le_0_compat.
    repeat apply Rmult_le_pos; try by apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    apply Rmult_le_pos; first by apply default_rel_ge_0.
    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  - repeat apply Rmult_le_pos; 
    try (apply /RleP; apply matrix_norm_pd).
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply Rmult_le_pos; last by apply default_abs_ge_0.
    apply Rplus_le_le_0_compat; try apply g_pos.
    apply Rplus_le_le_0_compat.
    repeat apply Rmult_le_pos; try by apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    apply Rmult_le_pos; first by apply default_rel_ge_0.
    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
+ apply Rmult_le_pos.
  apply /RleP; apply vec_norm_pd.
  apply /RleP; apply matrix_norm_pd.
Qed.

Print nth.

Lemma Rmax_le_0 (x y :R):
  (0 <= x)%Re -> (0 <= y)%Re -> Rmax x y = 0%Re ->
  x = 0%Re /\ y = 0%Re.
Proof.
intros.
assert ((x <= y)%Re \/ (y <= x)%Re).
{ nra. } destruct H2.
+ rewrite Rmax_right in H1; last by nra.
  rewrite H1 in H2. nra.
+ rewrite Rmax_left in H1; last by nra.
  rewrite H1 in H2. nra.
Qed.


Lemma seq_nth_equiv i s:
  nth i s 0%Re = seq.nth 0%Re s i.
Proof.
elim: s i => [ |a s IHs] i.
+ simpl. by destruct i.
+ simpl. destruct i.
  by simpl. simpl. apply IHs.
Qed.

Lemma bigmaxr_cons_0 (a:R) s :
 (forall i : nat,
    (i < size (a :: s))%nat ->
    (0 <= nth i (a :: s) 0)%Re) ->
  bigmaxr 0%Re (a :: s) = 0%Re ->
  a = 0%Re /\ bigmaxr 0%Re s = 0%Re.
Proof.
intros.
assert (s = [::] \/ s != [::]).
{ destruct s.
  + by left.
  + by right.
} destruct H1.
+ rewrite H1 in H0. rewrite H1. 
  rewrite bigmaxr_un in H0. rewrite bigmaxr_nil .
  nra.
+ apply (s_destruct 0%Re) in H1.
  rewrite H1 in H0. rewrite bigmaxr_cons in H0.
  rewrite -H1 in H0. rewrite -RmaxE in H0.
  apply Rmax_le_0; last by [].
  - specialize (H 0%nat). simpl in H. apply H. by [].
  - apply /RleP. apply bigmax_le_0.
    apply /RleP. apply Rle_refl.
    intros. apply /RleP.
    assert (forall j, (j < size s)%nat -> (0 <= nth j s 0%Re)%Re).
    { intros. specialize (H j.+1).
      simpl in H. apply H. apply H3.
    } specialize (H3 i). rewrite -seq_nth_equiv.
    by apply H3.
Qed.
  

Lemma bigmaxr_eq_0 s:
  (forall i, (i < size s)%nat -> (0 <= nth i s 0%Re)%Re) -> 
  bigmaxr 0%Re s = 0%Re ->
  (forall i, (i < size s)%nat -> nth i s 0%Re = 0%Re).
Proof.
intros.
elim: s i H H0 H1 => [ |a s IHs] i H H0 H1.
+ rewrite /nth /=. by destruct i.
+ apply bigmaxr_cons_0 in H0. 
  - simpl. destruct i.
    * apply H0.
    * apply IHs. intros. specialize (H i0.+1). simpl in H.
      apply H. apply H2. apply H0. apply H1.
  - intros. by apply H.
Qed.


Lemma bigsum_eq_0 {n} (f : nat ->R):
  (forall i, (i < n)%nat -> (0 <= f i)%Re) -> 
  \sum_(j < n) (f j) = 0%Re ->
  (forall i, (i < n)%nat -> f i = 0%Re).
Proof.
intros.
induction n.
+ by rewrite ltn0 in H1.
+ rewrite big_ord_recr /= in H0.
  rewrite -RplusE in H0. apply Rplus_eq_R0 in H0.
  - assert (i = n \/ (i < n)%nat). 
    { rewrite leq_eqVlt in H1. 
      assert ((i.+1 == n.+1) \/ (i.+1 < n.+1)%nat).
      { by apply /orP. } destruct H2; try (right; apply H2).
      left. by apply /eqP.
    } destruct H2. 
    * rewrite H2. apply H0.
    * apply IHn. intros.
      apply H. apply ltn_trans with n. apply H3. apply ltnSn.
      apply H0. apply H2.
  - apply /RleP. apply big_ge_0_ex_abstract. intros.
    apply /RleP. apply H. apply ltn_trans with n.
    apply ltn_ord. apply ltnSn.
  - apply H. apply ltnSn.
Qed.

Lemma matrix_inf_norm_0_implies {n:nat}:
  forall (A : 'M[R]_n.+1),  
  matrix_inf_norm A = 0%Re ->
  (forall i j, A i j = 0%Re).
Proof.
intros.
unfold matrix_inf_norm in H.
pose proof bigmaxr_eq_0.
specialize (H0 [seq row_sum A i | i <- enum 'I_n.+1]).
assert (forall i : nat,
        (i <
        size
         [seq row_sum A i0
            | i0 <- enum
                    'I_n.+1])%nat ->
          (0 <=
           nth i
             [seq row_sum A i0
                | i0 <- enum
                        'I_n.+1] 0)%Re).
{ intros. rewrite seq_equiv seq_nth_equiv. rewrite nth_mkseq.
  unfold row_sum. apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. apply Rabs_pos.
  by rewrite size_map size_enum_ord in H1.
} specialize (H0 H1 H).
specialize (H0 i).
rewrite seq_nth_equiv seq_equiv in H0.
rewrite nth_mkseq in H0; last by apply ltn_ord.
unfold row_sum in H0.
pose proof (@bigsum_eq_0 n.+1). 
specialize (H2 (fun j => Rabs (A i (@inord n j)))).
assert (forall i0 : nat,
        (i0 < n.+1)%nat ->
        (0 <= (fun j : nat => Rabs (A i (@inord n j))) i0)%Re).
{ intros. apply Rabs_pos. } specialize (H2 H3).
assert (\sum_(j < n.+1)
        (fun j0 : nat => Rabs (A i (@inord n j))) j = 0%Re).
{ rewrite -H0. apply eq_big. by []. intros. 
  by rewrite !inord_val. 
  rewrite size_map. rewrite -val_enum_ord. rewrite size_map size_enum_ord.
  apply ltn_ord.
} specialize (H2 H4). clear H3 H4. 
specialize (H2 j).
assert ((j < n.+1)%nat). { by apply ltn_ord. }
specialize (H2 H3). simpl in H2.
rewrite inord_val in H2.
assert ((0 <= A i j)%Re \/ (A i j < 0)%Re). nra.
destruct H4. rewrite Rabs_right in H2; nra.
rewrite Rabs_left in H2; try nra.
Qed.

Local Open Scope R_scope.

Lemma bpow_femax_lb_strict t : 
4 < bpow Zaux.radix2 (femax t).
Proof. 
pose proof fprec_gt_one t.
pose proof fprec_lt_femax t.
assert (1 < femax t)%Z.
eapply Z.lt_trans with (fprec t); auto.
eapply Rle_lt_trans with (bpow Zaux.radix2 2).
unfold bpow; simpl; nra.
apply bpow_lt; lia.
Qed.


Lemma mult_d_e_g1_lt' t n m:
(1 <= n )%nat -> (1 <= m)%nat ->
g1 t n m * (1 + default_rel t)  + default_abs t < g1 t (S n) (S m).
Proof.
intros; replace (S n) with (n + 1)%coq_nat by lia.
replace (S m) with (m + 1)%coq_nat by lia.
unfold g1, g; field_simplify. rewrite plus_INR.
replace (INR 1) with 1 by (simpl; nra).
rewrite !Rmult_plus_distr_l.
rewrite !Rmult_1_r. replace
(INR n * default_abs t * (1 + default_rel t) ^ m * default_rel t +
INR n * default_abs t * (1 + default_rel t) ^ m) with
(INR n * default_abs t * (1 + default_rel t) ^ m * (1 + default_rel t)) by nra.
rewrite !Rmult_plus_distr_r.
apply Rplus_le_lt_compat.
rewrite !Rmult_assoc.
rewrite Rmult_comm.
rewrite !Rmult_assoc.
apply Rmult_le_compat_l. nra. 
apply Rmult_le_compat_l. apply bpow_ge_0.
rewrite <- !Rmult_assoc.
rewrite Rmult_comm. 
apply Rmult_le_compat_l; [apply pos_INR| ].
rewrite Rmult_comm.
rewrite tech_pow_Rmult.
replace (S m) with (m + 1)%coq_nat by lia; nra.
replace (default_abs t) with (default_abs t * 1) at 1 by nra.
apply Rmult_lt_compat_l; [apply  default_abs_gt_0 | ].
apply Rlt_pow_R1. apply default_rel_plus_1_gt_1.
lia.
Qed.

Lemma defualt_abs_lt_fmax t :
default_abs t < bpow Zaux.radix2 (femax t).
Proof.
replace (bpow Zaux.radix2 (femax t)) with (1 * bpow Zaux.radix2 (femax t)) by nra.
unfold default_abs; apply Rmult_lt_compat; try nra.
apply bpow_ge_0.
apply bpow_lt.
apply Z.lt_sub_lt_add_r.
apply Z.lt_sub_lt_add_r.
eapply Z.lt_trans with (fprec t + fprec t + femax t)%Z; 
  [ | repeat apply Zplus_lt_compat_r; apply fprec_lt_femax].
eapply Z.lt_trans with (fprec t + fprec t + fprec t)%Z;
[ |  repeat apply Zplus_lt_compat_l; apply fprec_lt_femax ].
eapply Z.lt_trans with (1 + fprec t + fprec t)%Z;
[ |  repeat apply Zplus_lt_compat_r; apply fprec_gt_one].
eapply Z.lt_trans with (1 + 1 + fprec t)%Z;
[ |  repeat apply Zplus_lt_compat_r; repeat apply Zplus_lt_compat_l; 
apply fprec_gt_one].
eapply Z.le_lt_trans with (1 + 1 + 1)%Z;
[ lia |  repeat apply Zplus_lt_compat_r; repeat apply Zplus_lt_compat_l; 
apply fprec_gt_one].
Qed.

Lemma fun_bound_gt_0 t n :
forall (Hn : g1 t (n + 1) n <= fmax t), 
0 < fun_bnd t n. 
Proof.
intros;
unfold fun_bnd. apply Rmult_lt_0_compat.
+ apply Rlt_Rminus. apply Generic_proof.Rdiv_lt_mult_pos.
  apply Rplus_lt_le_0_compat. nra. apply default_rel_ge_0.
  apply Rcomplements.Rlt_minus_r.
  assert (Hn': (n= 0%nat)%coq_nat \/ (1<=n)%coq_nat) by lia; destruct Hn'; subst.
  { simpl. unfold g1, g. simpl; field_simplify. apply defualt_abs_lt_fmax. }
  assert (Hn'': (n= 1%nat)%coq_nat \/ (1 < n)%coq_nat) by lia; destruct Hn''; subst.
  { simpl. unfold g1, g. simpl; field_simplify.
    eapply Rlt_trans.
    apply Rplus_lt_compat. 
    apply Rmult_lt_compat.
    apply default_abs_ge_0. 
    apply default_rel_ge_0.
    apply default_abs_ub_strict.
    apply default_rel_ub_strict.
    apply Rmult_lt_compat_l; try nra.
    apply default_abs_ub_strict. 
    eapply Rlt_trans; [| apply bpow_femax_lb_strict]; nra. }
    eapply Rlt_le_trans; last by apply Hn.  
    replace (n + 1)%coq_nat with (S n) by lia.
    assert (n = (S (n - 1))%coq_nat). rewrite subn1. rewrite prednK. by [].
    apply /ssrnat.ltP. lia.
    rewrite [in X in (_ < g1 t _ X)]H1. rewrite addn1.
    apply mult_d_e_g1_lt'. by apply /ssrnat.ltP.
    rewrite subn_gt0. by apply /ssrnat.ltP. 
+ assert (forall x:R, (1 / x)%Re = (/x)%Re). 
  { intros. nra. } rewrite H. apply Rinv_0_lt_compat.
  apply Rplus_lt_le_0_compat. nra.
  apply Rmult_le_pos. apply pos_INR.
  apply Rplus_le_le_0_compat. apply g_pos. nra.
Qed.

Close Scope R_scope.


(** entries zero in real ==> entries zero in float **)
Lemma A_real_to_float_zero {t} {n} (A : 'M[ftype t]_n.+1):
  forall i j,
  finite (A i j) ->
  FT2R (A i j) = 0%Re ->
  Bsign (fprec t) (femax t) (A i j) = false ->
  A i j = Zconst t 0.
Proof.
intros.
apply B2R_Bsign_inj.
+ by apply finite_is_finite.
+ by simpl.
+ unfold FT2R in H0. by rewrite H0;simpl.
+ by simpl. 
Qed.

Lemma A_entry_mult_0 {t} {n} (A : 'M[ftype t]_n.+1):
  forall i j,
  finite (A i j) ->
  BMULT (A i j)  (Zconst t 0) = Zconst t 0.
Proof.
intros. 
rewrite /BMULT /BINOP /Bmult /BSN2B /BinarySingleNaN.Bmult /=. 
apply finite_is_finite in H. rewrite -is_finite_B2BSN in H.
unfold BinarySingleNaN.is_finite in H.
destruct (B2BSN (fprec t) (femax t) (A i j)); simpl; try by [].
unfold Zconst, vcfloat.IEEE754_extra.BofZ, binary_normalize. simpl.
destruct s; simpl; try by []. admit.
unfold Zconst, vcfloat.IEEE754_extra.BofZ, binary_normalize. simpl.
destruct s; simpl; try by []. admit.
Admitted.


Lemma finite_residual_1 {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  (0 < length A)%coq_nat ->
  length A = length b ->
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let x0' := @vector_inj _ x0 n.+1 in
  @size_constraint t (length A).-1 ->
  (forall i j, finite (A2_J A' i j)) ->
  (forall i, finite (x0' i ord0)) ->
  input_bound_at_N_0 A x0 b ->
  (forall i, finite (A' i i)) ->
  (forall i, finite (A1_inv_J A' i ord0)) ->
  (forall i, finite (b' i ord0)) ->
  matrix_inf_norm (FT2R_mat (A2_J A')) = 0%Re ->
  finite (norm2 (resid (jacobi_n A b x0 1%nat))).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? HfA2 Hfx0 Hinp HfA HfA1_inv Hfb HN0.
unfold norm2. 
assert ( length (resid (jacobi_n A b x0 1%nat)) = n.+1).
{ repeat rewrite /matrix_vector_mult !map_length combine_length.
    rewrite !map_length. unfold jacobi_n. (*rewrite iter_length. *)
    rewrite !seq_length /matrix_rows_nat H0 !Nat.min_id.
    rewrite -/n prednK. by []. by apply /ssrnat.ltP.
    (*by []. by rewrite /x0 repeat_length. *)
}
apply dotprod_finite.
+ rewrite H2. apply g1_constraint_Sn. apply H1.
+ intros. apply in_rev in H3.
  pose proof (@In_nth _ (resid (jacobi_n A b x0 1%nat)) xy (Zconst t 0) H3 ).
  destruct H4 as [k [Hlen Hnth]].
  pose proof (@v_equiv  t (resid (jacobi_n A b x0 1%nat)) n H2).
  assert ((\col_j0 vector_inj
                     (resid (jacobi_n A b x0 1%nat)) n.+1 j0  ord0) = 
           vector_inj (resid (jacobi_n A b x0 1%nat)) n.+1).
  { apply matrixP. unfold eqrel. intros. by rewrite !mxE. }
  rewrite H5 in H4. clear H5.
  rewrite H4 in Hnth. rewrite rev_nth in Hnth.
  rewrite length_veclist in Hnth.
  assert ((n.+1 - k.+1)%coq_nat = (n.+1.-1 - k)%coq_nat) by lia.
  rewrite H5 in Hnth.
  pose proof (@vector_residual_equiv t A b x0 1%nat).
  assert (length b = length A). { by rewrite -H0. }
  specialize (H6 H7). clear H7.
  assert ( length x0 = length A ).
  { by rewrite repeat_length. } specialize (H6 H7). clear H7.
  specialize (H6 H). unfold resid in Hnth. rewrite -/n in H6.
  rewrite H6 in Hnth.
  rewrite nth_vec_to_list_float in Hnth.
  rewrite mxE in Hnth. rewrite -Hnth.
  rewrite -/n -/A' -/b' -/x0'.
  assert ((X_m_jacobi 2 x0' b' A' -f
              X_m_jacobi 1 x0' b' A') = \col_j (Zconst t 0)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE.
    repeat (rewrite nth_vec_to_list_float; last by apply ltn_ord).
    rewrite !mxE.
    pose proof (@matrix_inf_norm_0_implies n (FT2R_mat (A2_J A')) HN0).
    specialize (H7 x).
    assert (\row_j (A2_J A' (inord x) j) = \row_j (Zconst t 0)).
    { apply matrixP. unfold eqrel. intros. rewrite mxE. rewrite mxE.
    specialize (H7 y0). rewrite mxE in H7.
    apply A_real_to_float_zero; try by []. 
    rewrite inord_val. apply H7.
    admit. (** sign **)
    } rewrite H8.







admit.
  } rewrite H7.
  rewrite !nth_vec_to_list_float. 
  rewrite !inord_val. rewrite mxE.
  assert (BMULT (A1_J A' (inord k) ord0)  (Zconst t 0) = Zconst t 0).
  { rewrite /BMULT /BINOP /Bmult /BSN2B /BinarySingleNaN.Bmult /=. 


simpl.



admit. } rewrite H8. split.
  - admit.
  - rewrite rev_length H2. intros. simpl. rewrite Rabs_R0. apply sqrt_lt_R0.
    apply fun_bound_gt_0. unfold n0. by apply g1_constraint. 
  - rewrite H2 in Hlen.
    rewrite inordK; (by apply /ssrnat.ltP ).
  - rewrite H2 in Hlen.
    rewrite inordK; (by apply /ssrnat.ltP ).
  - rewrite H2 in Hlen. by apply /ssrnat.ltP.
  - rewrite length_veclist. by rewrite H2 in Hlen.


Admitted.

Lemma jacobi_iteration_bound_lowlevel {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
   let acc2 := BMULT acc acc in
   let x0 := (repeat  (Zconst t 0) (length b)) in
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
   finite acc2 /\ 
   exists j,
    (j <= k)%nat /\
    let y :=  jacobi_n A b x0 j in
    let r2 := norm2 (resid y) in
    (forall i, (i <= j)%nat -> finite (norm2 (resid (jacobi_n A b x0 i)))) /\
    BCMP Lt false (norm2 (resid (jacobi_n A b x0 j))) acc2 = false.
Proof.  
intros.
unfold jacobi_preconditions in H.
destruct H as [HAA [HlenA [HeqAb H]]].
assert (rho_def
           (matrix_inj A (length A).-1.+1
              (length A).-1.+1)
           (vector_inj b (length A).-1.+1) = 0%Re \/
        (0 < rho_def
           (matrix_inj A (length A).-1.+1
              (length A).-1.+1)
           (vector_inj b (length A).-1.+1))%Re).
{ pose proof (@rho_ge_0 t (length A).-1 
              (matrix_inj A (length A).-1.+1
              (length A).-1.+1)
              (vector_inj b (length A).-1.+1)).
  simpl in H0. unfold rho_def. nra.
}
destruct H0.
(*** || N || = 0 case. ***)
- split.
  + apply H.
  + (*** TODO: k = 1 : for k = 1, the residual should evaluate to 0 ***) 
    apply rho_0_implies_N_eq_0 in H0.
    exists 1%nat.
    split.
    * assert (k = 0%nat \/ (0 < k)%nat).
      { assert ((0 <= k)%nat). by [].
        rewrite leq_eqVlt in H1. 
        assert ((0%nat == k) \/ (0 < k)%nat). by apply /orP.
        destruct H2; try (right; by apply H2). rewrite eq_sym in H2. left. by apply /eqP.
      } destruct H1.
      ++ destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
         rewrite H1 in Hk. 
         assert ((k_min_alt
                    (matrix_inj A (length A).-1.+1
                       (length A).-1.+1)
                    (vector_inj b (length A).-1.+1)
                    acc < 0)%nat). by apply /ssrnat.ltP.
         by rewrite ltn0 in H.
      ++ apply H1.
    * intros. split.
      ++ intros.
         
















  exists 0%nat.
    split.
    * apply /ssrnat.leP. lia.
    * intros. split.
      ++ intros. rewrite leqn0 in H1.
         assert (i = 0)%nat. { by apply /eqP. }
         rewrite H2.
         apply finite_residual_0; try by apply H. apply HlenA.
         apply HeqAb. intros. 
         remember ((length A).-1) as n.
         assert (vector_inj
                   (repeat (Zconst t 0) (length b)) n.+1 =
                 \col_(j < n.+1) (Zconst t 0)).
         { apply matrixP. unfold eqrel. intros. rewrite !mxE.
           by rewrite nth_repeat.
         } rewrite H3. apply H.
         apply input_bound_at_N_0_equiv.
         remember ((length A).-1) as n.
         assert (vector_inj
                   (repeat (Zconst t 0) (length b)) n.+1 =
                 \col_(j < n.+1) (Zconst t 0)).
         { apply matrixP. unfold eqrel. intros. rewrite !mxE.
           by rewrite nth_repeat.
         } rewrite H3.
         apply H.
         intros. apply H. intros. rewrite mxE. apply H.
      ++ unfold BCMP.
         rewrite Bcompare_correct.
         -- rewrite Rcompare_Lt; first by [].
            change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
            remember (FT2R acc2) as Gamma.
            pose proof (@vector_residual_equiv t A b x0 0%nat).
            assert (length b = length A) by (symmetry; apply HeqAb).
            assert (length x0 = length A).
            { unfold x0. by rewrite !repeat_length. }
            assert ((0 < length A)%coq_nat) by apply HlenA.
            specialize (H1 H2 H3 H4).
            pose proof (@v_equiv t).
            remember (length A).-1 as n.
            specialize (H5 (resid (jacobi_n A b x0 0)) n).
            assert (length (resid (jacobi_n A b x0 0)) = n.+1).
            { repeat rewrite /matrix_vector_mult !map_length combine_length.
              rewrite !map_length. unfold jacobi_n. rewrite iter_length.
              rewrite !seq_length /matrix_rows_nat -HeqAb !Nat.min_id.
              rewrite Heqn prednK. by []. by apply /ssrnat.ltP.
              by []. by rewrite /x0 repeat_length.
            } specialize (H5 H6).
            rewrite H5.
            assert ((\col_j0 vector_inj
                      (resid (jacobi_n A b x0 0))
                      n.+1 j0 ord0) = 
                      vector_inj (resid (jacobi_n A b x0 0)) n.+1).
            { apply /matrixP. unfold eqrel. intros. by rewrite !mxE. } 
            rewrite H7. 
            assert ((FT2R
                     (norm2
                        (rev
                           (vec_to_list_float n.+1
                              (vector_inj (resid (jacobi_n A b x0 0)) n.+1)))) < 0)%Re \/
                    (0 <= FT2R
                           (norm2
                              (rev
                                 (vec_to_list_float n.+1
                                    (vector_inj (resid (jacobi_n A b x0 0)) n.+1)))))%Re).
            { nra. } destruct H8.
            destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
            apply Rlt_le_trans with 0%Re.
            nra.
            remember (@matrix_inj _ A n.+1 n.+1) as A'.
            remember (@vector_inj _ b n.+1) as b'.
            apply Rle_trans with 
            ( g1 t n.+1 (n.+1 - 1)%coq_nat +
              INR n.+1 * (1 + g t n.+1) *
              (g1 t n.+1 (n.+1 - 1)%coq_nat +
               2 * (1 + g t n.+1) *
               (1 + default_rel t) *
               vec_inf_norm (FT2R_mat (A1_J A')) *
               d_mag_def_alt A' b' *
               / (1 - rho_def_alt A' b'))²)%Re.
            apply Rplus_le_le_0_compat; first by apply g1_pos.
            apply Rmult_le_pos. apply Rmult_le_pos. apply pos_INR.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rle_0_sqr. 
            rewrite HeqGamma. unfold acc2. nra.
            assert (FT2R (norm2 (rev
                           (vec_to_list_float n.+1
                              (vector_inj
                                 (resid
                                    (jacobi_n A b x0 0)) n.+1)))) =
                     Rabs (FT2R (norm2 (rev
                           (vec_to_list_float n.+1
                              (vector_inj
                                 (resid
                                    (jacobi_n A b x0 0)) n.+1)))))).
             { rewrite Rabs_right. nra. by apply Rle_ge. }
             rewrite H9. clear H9.
             eapply Rle_lt_trans.
             apply norm2_vec_inf_norm_rel.
             ** intros. apply finite_in with A b. apply HlenA. apply HeqAb.
                unfold resid in H9. rewrite -Heqn. apply H. 
                rewrite -Heqn. apply H.
                rewrite -Heqn.
                 assert (vector_inj
                           (repeat (Zconst t 0) (length b)) n.+1 =
                         \col_(j < n.+1) (Zconst t 0)).
                 { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                   by rewrite nth_repeat.
                 } intros. rewrite H10. apply H.
                 apply input_bound_at_N_0_equiv.
                 rewrite -Heqn.
                 assert (vector_inj
                           (repeat (Zconst t 0) (length b)) n.+1 =
                         \col_(j < n.+1) (Zconst t 0)).
                 { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                   by rewrite nth_repeat.
                 } rewrite H10.
                 apply H.
                 rewrite -Heqn.
                 intros. apply H. rewrite -Heqn. intros. rewrite mxE. apply H.
                 rewrite -Heqn.
                 intros. apply H. rewrite -Heqn.
                 apply H9.
             ** rewrite  -H7 -H5. apply finite_residual_0.
                apply HlenA. apply HeqAb. unfold size_constraint. 
                destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                unfold size_constraint in size_cons. by rewrite Heqn in size_cons.
                rewrite -Heqn. apply H.
                rewrite -Heqn.
                 assert (vector_inj
                           (repeat (Zconst t 0) (length b)) n.+1 =
                         \col_(j < n.+1) (Zconst t 0)).
                 { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                   by rewrite nth_repeat.
                 } intros. rewrite H9. apply H.
                 apply input_bound_at_N_0_equiv.
                 rewrite -Heqn.
                 assert (vector_inj
                           (repeat (Zconst t 0) (length b)) n.+1 =
                         \col_(j < n.+1) (Zconst t 0)).
                 { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                   by rewrite nth_repeat.
                 } rewrite H9.
                 apply H.
                 rewrite -Heqn.
                 intros. apply H. rewrite -Heqn. intros. rewrite mxE. apply H.
                 rewrite -Heqn.
                 intros. apply H. 
             ** assert (HfA2l :  (forall i j : 'I_(length A).-1.+1,
                                     finite
                                       (A2_J
                                          (matrix_inj A (length A).-1.+1
                                             (length A).-1.+1) i j))).
                  { rewrite -Heqn. intros. apply H. }
                  assert (Hfx0l : (forall i : 'I_(length A).-1.+1,
                                   finite
                                     (vector_inj
                                        (repeat (Zconst t 0)
                                           (length b))
                                        (length A).-1.+1 i ord0))).
                  { rewrite -Heqn. intros. 
                    assert (vector_inj
                           (repeat (Zconst t 0) (length b)) n.+1 =
                         \col_(j < n.+1) (Zconst t 0)).
                     { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by rewrite nth_repeat.
                     } rewrite H9. apply H.
                  } 
                  assert (HfAl : (forall i : 'I_(length A).-1.+1,
                                   finite
                                     (matrix_inj A (length A).-1.+1
                                        (length A).-1.+1 i i))).
                  { rewrite -Heqn. intros. apply H. }
                  assert (HfA1_invl: (forall i : 'I_(length A).-1.+1,
                                       finite
                                         (A1_inv_J
                                            (matrix_inj A (length A).-1.+1
                                               (length A).-1.+1) i ord0))).
                  { rewrite -Heqn. intros. rewrite mxE. apply H. }
                  assert (Hfbl : (forall i : 'I_(length A).-1.+1,
                                   finite
                                     (vector_inj b (length A).-1.+1 i
                                        ord0))).
                  { rewrite -Heqn. intros. apply H. }
                  assert (Hinpl : input_bound_at_N_0 A x0 b).
                  { apply input_bound_at_N_0_equiv.
                     rewrite -Heqn.
                     assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                     { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by rewrite nth_repeat.
                     } rewrite H9.
                     apply H.
                  }
                rewrite H1. unfold residual_math.
                remember (vector_inj x0 n.+1) as x0'.
                remember (vector_inj b n.+1) as b'.
                remember (matrix_inj A n.+1 n.+1) as A'.
                pose proof (@vec_norm_diag _ t n  (A1_J A')
                            (X_m_jacobi 1 x0' b' A' -f
                                X_m_jacobi 0 x0' b' A')).
                assert (forall xy : ftype t * ftype t,
                          In xy
                            (combine
                               (vec_to_list_float n.+1
                                  (A1_J A'))
                               (vec_to_list_float n.+1
                                  (X_m_jacobi 1 x0' b' A' -f
                                   X_m_jacobi 0 x0' b' A'))) ->
                          finite xy.1 /\ finite xy.2 /\
                          finite (BMULT xy.1 xy.2)).
                { intros.
                  pose proof (@finite_implies_1 t A b HlenA HeqAb).
                  pose proof (@finite_residual_0 t A b HlenA HeqAb).
                  destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                  rewrite Heqn in size_cons.
                  specialize (H12 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                  specialize (H11 H12).
                  apply H11. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                  apply H10. 
                }
               specialize (H9 H10).
               assert ((vec_inf_norm
                        (FT2R_mat
                           (diag_vector_mult 
                              (A1_J A')
                              (X_m_jacobi 1 x0' b' A' -f
                               X_m_jacobi 0 x0' b' A')) -
                         diag_matrix_vec_mult_R
                           (FT2R_mat (A1_J A'))
                           (FT2R_mat
                              (X_m_jacobi 1 x0' b' A' -f
                               X_m_jacobi 0 x0' b' A'))) <=
                      vec_inf_norm (FT2R_mat (A1_J A')) *
                      vec_inf_norm
                        (FT2R_mat
                           (X_m_jacobi 1 x0' b' A' -f
                            X_m_jacobi 0 x0' b' A')) *
                      g t n.+1 + g1 t n.+1 (n.+1 - 1))). { by apply /RleP. }
               apply reverse_triang_ineq in H11.
               assert ((vec_inf_norm
                        (FT2R_mat
                           (diag_vector_mult (A1_J A')
                              (X_m_jacobi 1 x0' b' A' -f
                               X_m_jacobi 0 x0' b' A'))) <=
                        (vec_inf_norm (FT2R_mat (A1_J A')) *
                          vec_inf_norm
                            (FT2R_mat
                               (X_m_jacobi 1 x0' b' A' -f
                                X_m_jacobi 0 x0' b' A'))) * 
                         (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re).
               { rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                 assert (forall a b c d :R, (a - b <= c + d)%Re -> (a <= b + c+d)%Re).
                 { intros. nra. } apply H12. eapply Rle_trans; last by (apply /RleP; apply H11).
                 rewrite -RminusE. apply Rplus_le_compat_l.
                 apply Ropp_le_contravar.
                 apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
               } eapply Rle_lt_trans.
               apply Rplus_le_compat_r. apply Rmult_le_compat_r.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rmult_le_compat_l. apply pos_INR.
               apply Rle_trans with 
               (Rsqr (vec_inf_norm (FT2R_mat (A1_J A')) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi 1 x0' b' A' -f
                             X_m_jacobi 0 x0' b' A')) *
                       (1 + g t n.+1) +
                       g1 t n.+1 (n.+1 - 1)%coq_nat)).
               apply Rsqr_incr_1. apply H12. 
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat; last by apply g1_pos.
               repeat apply Rmult_le_pos.
               apply /RleP. apply vec_norm_pd.
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rle_refl.
               assert (X_m_jacobi 1 x0' b' A' = jacobi_iter x0' b' A'). { by simpl. }
               assert (X_m_jacobi 0 x0' b' A' = x0'). { by simpl. }
               rewrite H13 H14. unfold jacobi_iter.
               clear H9 H10 H11 H12 H13 H14.
               pose proof (@vec_float_sub _ t n 
                            (diag_vector_mult (A1_inv_J A')
                                (b' -f A2_J A' *f x0')) x0').
               assert (forall xy : ftype t * ftype t,
                          In xy
                            (combine
                               (vec_to_list_float n.+1
                                  (diag_vector_mult
                                     (A1_inv_J A')
                                     (b' -f A2_J A' *f x0')))
                               (vec_to_list_float n.+1 x0')) ->
                          finite xy.1 /\
                          finite xy.2 /\
                          finite (BPLUS xy.1 (BOPP xy.2))).
               { intros.
                  pose proof (@finite_implies_2 t A b HlenA HeqAb).
                  pose proof (@finite_residual_0 t A b HlenA HeqAb).
                  destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                  rewrite Heqn in size_cons.
                  specialize (H12 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                  specialize (H11 H12).
                  apply H11. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                  apply H10.
                }
               specialize (H9 H10).
               apply reverse_triang_ineq in H9.
               eapply Rle_lt_trans. apply Rplus_le_compat_r.
               apply Rmult_le_compat_r.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rmult_le_compat_l. apply pos_INR.
               apply Rle_trans with
               (Rsqr (vec_inf_norm (FT2R_mat (A1_J A')) *
                  ((vec_inf_norm
                      (FT2R_mat
                         (diag_vector_mult 
                            (A1_inv_J A')
                            (b' -f A2_J A' *f x0'))) +
                    vec_inf_norm (FT2R_mat x0')) *
                    (1 + default_rel t)) * 
                  (1 + g t n.+1) +
                  g1 t n.+1 (n.+1 - 1)%coq_nat)%Re).
               apply Rsqr_incr_1.
               apply Rplus_le_compat_r. apply Rmult_le_compat_r.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
               rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
               eapply Rle_trans. 
               assert (forall x y z :R, (x - y <= z)%Re -> (x <= y + z)%Re). { intros. nra. }
               apply H11. apply /RleP. apply H9. rewrite -RplusE -RmultE.
               apply Rplus_le_compat_r. eapply Rle_trans.
               apply /RleP. apply triang_ineq. rewrite -vec_inf_norm_opp.
               rewrite -RplusE. apply Rle_refl.
               apply Rplus_le_le_0_compat; last by apply g1_pos.
               apply Rmult_le_pos; last by 
               (apply Rplus_le_le_0_compat; try nra; try apply g_pos).
               apply Rmult_le_pos; try (apply /RleP; apply vec_norm_pd).
               apply Rplus_le_le_0_compat; last by apply g1_pos.
               apply Rmult_le_pos; last by 
               (apply Rplus_le_le_0_compat; try nra; try apply g_pos).
               apply Rmult_le_pos; try (apply /RleP;apply vec_norm_pd).
               apply Rmult_le_pos; last by 
               (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
               apply Rplus_le_le_0_compat; try (apply /RleP; apply vec_norm_pd).
               apply Rsqr_incr_1.
               apply Rplus_le_compat_r. apply Rmult_le_compat_r.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
               apply Rmult_le_compat_r. 
               apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
               apply Rplus_le_compat_r.
               pose proof (@vec_norm_diag _ t n (A1_inv_J A') (b' -f A2_J A' *f x0')).
               assert (forall xy : ftype t * ftype t,
                         In xy
                           (combine
                              (vec_to_list_float n.+1
                                 (A1_inv_J A'))
                              (vec_to_list_float n.+1
                                 (b' -f A2_J A' *f x0'))) ->
                         finite xy.1 /\
                         finite xy.2 /\
                         finite (BMULT xy.1 xy.2)).
               { intros.
                  pose proof (@finite_implies_3 t A b HlenA HeqAb).
                  pose proof (@finite_residual_0 t A b HlenA HeqAb).
                  destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                  rewrite Heqn in size_cons.
                  specialize (H14 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                  specialize (H13 H14).
                  apply H13. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                  apply H12. 
               }
               specialize (H11 H12).
               apply Rle_trans with
               (vec_inf_norm
                     (FT2R_mat (A1_inv_J A')) *
                   vec_inf_norm
                     (FT2R_mat (b' -f A2_J A' *f x0')) *
                   (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1))%Re.
               rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
               apply Rle_trans with 
               (vec_inf_norm 
                  (diag_matrix_vec_mult_R
                      (FT2R_mat (A1_inv_J A'))
                      (FT2R_mat
                         (b' -f A2_J A' *f x0'))) + 
                 vec_inf_norm (FT2R_mat (A1_inv_J A')) *
                   vec_inf_norm
                     (FT2R_mat (b' -f A2_J A' *f x0')) *
                   g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re.
               assert (vec_inf_norm
                           (FT2R_mat
                              (diag_vector_mult
                                 (A1_inv_J A')
                                 (b' -f A2_J A' *f x0')) -
                            diag_matrix_vec_mult_R
                              (FT2R_mat (A1_inv_J A'))
                              (FT2R_mat
                                 (b' -f A2_J A' *f x0'))) <=
                         vec_inf_norm
                           (FT2R_mat (A1_inv_J A')) *
                         vec_inf_norm
                           (FT2R_mat
                              (b' -f A2_J A' *f x0')) *
                         g t n.+1 + g1 t n.+1 (n.+1 - 1)). { by apply /RleP. }
               apply reverse_triang_ineq in H13.
               assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
               { intros. nra. } apply H14. apply /RleP. apply H13.
               repeat apply Rplus_le_compat_r. apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
               apply Rplus_le_compat_r.
               apply Rmult_le_compat_r.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
               pose proof (@vec_float_sub _ t n b' (A2_J A' *f x0')).
               assert (forall xy : ftype t * ftype t,
                           In xy
                             (combine
                                (vec_to_list_float n.+1 b')
                                (vec_to_list_float n.+1
                                   (A2_J A' *f x0'))) ->
                           finite xy.1 /\
                           finite xy.2 /\
                           finite (BPLUS xy.1 (BOPP xy.2))).
               { intros.
                  pose proof (@finite_implies_4 t A b HlenA HeqAb).
                  pose proof (@finite_residual_0 t A b HlenA HeqAb).
                  destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                  rewrite Heqn in size_cons.
                  specialize (H16 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                  specialize (H15 H16).
                  apply H15. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                  apply H14. 
               }
               specialize (H13 H14).
               apply Rle_trans with
               ((vec_inf_norm (FT2R_mat b') +
                     vec_inf_norm
                       (FT2R_mat (A2_J A' *f x0'))) *
                   (1 + default_rel t))%Re.
               rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
               apply reverse_triang_ineq in H13. eapply Rle_trans.
               assert ((vec_inf_norm
                          (FT2R_mat
                             (b' -f A2_J A' *f x0')) -
                        vec_inf_norm
                          (FT2R_mat b' -
                           FT2R_mat (A2_J A' *f x0')) <=
                        (vec_inf_norm (FT2R_mat b') +
                         vec_inf_norm
                           (FT2R_mat (A2_J A' *f x0'))) *
                        default_rel t)%Re). { by apply /RleP. }
               assert (forall a b c:R, (a - b <= c)%Re -> (a <= b +c)%Re). { intros. nra. }
               apply H16 in H15. apply H15.
               apply Rplus_le_compat_r. eapply Rle_trans.
               apply /RleP. apply triang_ineq. rewrite -vec_inf_norm_opp. rewrite -RplusE. nra.
               apply Rmult_le_compat_r.
               apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
               apply Rplus_le_compat_l.
               pose proof (@matrix_vec_mult_bound_corollary _ n t (A2_J A') x0').
               assert (forall (xy : ftype t * ftype t)
                           (i : 'I_n.+1),
                         In xy
                           (combine
                              (vec_to_list_float n.+1
                                 (\row_j A2_J A'
                                          (inord i) j)^T)
                              (vec_to_list_float n.+1
                                 x0')) ->
                         finite xy.1 /\ finite xy.2). 
               { intros.
                  pose proof (@finite_implies_5 t A b HlenA HeqAb).
                  pose proof (@finite_residual_0 t A b HlenA HeqAb).
                  destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                  rewrite Heqn in size_cons.
                  specialize (H18 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl). 
                  rewrite -Heqn in H17. specialize (H17 H18 xy i).
                  apply H17. rewrite HeqA' Heqx0' in H16.
                  apply H16.
              }
              assert (forall i : 'I_n.+1,
                       finite 
                         (let l1 :=
                            vec_to_list_float n.+1
                              (\row_j A2_J A'
                                        (inord i) j)^T
                            in
                          let l2 :=
                            vec_to_list_float n.+1
                              (\col_j x0' j 0) in
                          dotprod_r l1 l2)).
              { intros.
                  pose proof (@finite_implies_6 t A b HlenA HeqAb).
                  pose proof (@finite_residual_0 t A b HlenA HeqAb).
                  destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                  rewrite Heqn in size_cons.
                  specialize (H18 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl). 
                  rewrite -Heqn in H17.
                  specialize (H17 H18 i).
                  rewrite HeqA' Heqx0'.
                  apply H17.         
              }
              specialize (H15 H16 H17).
              apply reverse_triang_ineq in H15.
              apply Rle_trans with 
              (matrix_inf_norm
                    (FT2R_mat (A2_J A')) *
                  vec_inf_norm (FT2R_mat x0') +
                  matrix_inf_norm
                    (FT2R_mat (A2_J A')) *
                  vec_inf_norm (FT2R_mat x0') *
                  g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re.
               apply Rle_trans with
               ( vec_inf_norm
                        (FT2R_mat (A2_J A') *m 
                         FT2R_mat x0') + 
                 matrix_inf_norm
                    (FT2R_mat (A2_J A')) *
                  vec_inf_norm (FT2R_mat x0') *
                  g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re.
               assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
               { intros. nra. } apply H18. apply /RleP. apply H15.
               repeat apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
               assert ((matrix_inf_norm (FT2R_mat (A2_J A')) *
                         vec_inf_norm (FT2R_mat x0') +
                         matrix_inf_norm (FT2R_mat (A2_J A')) *
                         vec_inf_norm (FT2R_mat x0') *
                         g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re =
                       ((matrix_inf_norm (FT2R_mat (A2_J A')) *
                         vec_inf_norm (FT2R_mat x0')) * (1 + g t n.+1 )+
                        g1 t n.+1 (n.+1 - 1))%Re). { nra. } rewrite H18.
               apply Rle_refl.
               apply Rplus_le_le_0_compat;last by apply g1_pos.
               repeat apply Rmult_le_pos.
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat; try (apply /RleP; apply vec_norm_pd).
               apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rplus_le_le_0_compat; last by apply g1_pos.
               repeat apply Rmult_le_pos.
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat;last by (apply /RleP; apply vec_norm_pd).
               apply Rplus_le_le_0_compat;last by apply g1_pos.
               repeat apply Rmult_le_pos.
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat. 
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat; last by apply g1_pos.
               repeat apply Rmult_le_pos.
               apply /RleP. apply matrix_norm_pd.
               apply /RleP. apply vec_norm_pd.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
               apply Rplus_le_le_0_compat. nra. apply g_pos.
               destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
               destruct HG as [_ HG].
               assert (vector_inj
                           (repeat (Zconst t 0) (length b)) n.+1 =
                         \col_(j < n.+1) (Zconst t 0)).
                { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                  by rewrite nth_repeat.
                } rewrite Heqx0' /x0. rewrite H. rewrite HeqGamma. apply HG.
         -- rewrite <- finite_is_finite. apply finite_residual_0.
            apply HlenA. apply HeqAb. unfold size_constraint. 
            destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
            by unfold size_constraint in size_cons.
            intros. apply H.
            intros.
            assert (vector_inj
                           (repeat (Zconst t 0) (length b)) (length A).-1.+1 =
                         \col_(j < (length A).-1.+1) (Zconst t 0)).
            { apply matrixP. unfold eqrel. intros. rewrite !mxE.
              by rewrite nth_repeat.
            } rewrite H1. apply H.
            apply input_bound_at_N_0_equiv.
            assert (vector_inj
                           (repeat (Zconst t 0) (length b)) (length A).-1.+1 =
                         \col_(j < (length A).-1.+1) (Zconst t 0)).
            { apply matrixP. unfold eqrel. intros. rewrite !mxE.
              by rewrite nth_repeat.
            } rewrite H1.
            apply H.
            intros. apply H.
            intros. rewrite mxE. apply H.
            intros. apply H.
         -- rewrite <- finite_is_finite. apply H.
(** 0 < || N || **)
- remember (length A).-1 as n.
  remember (@matrix_inj _ A n.+1 n.+1) as A'.
  remember (@vector_inj _ b n.+1) as b'.  
  remember (FT2R_mat A') as A_real.
  remember (FT2R_mat b') as b_real.
  remember (A_real^-1 *m b_real) as x.
  assert ((d_mag_def_alt A' b' / (1 - rho_def_alt A' b') <
               vec_inf_norm (x_fix x b_real A_real))%Re \/
          (vec_inf_norm (x_fix x b_real A_real) <= 
            (d_mag_def_alt A' b' / (1 - rho_def_alt A' b')))%Re).
  { nra. } destruct H1.
  * apply jacobi_iteration_bound_lowlevel'.
    ++ apply jacobi_precond_compute_implies_math.
       rewrite HeqA' Heqb' Heqn in H0. apply H0.
       rewrite -Heqn -HeqA' -Heqb' -HeqA_real -Heqb_real -Heqx.
       apply H1. 
       rewrite -Heqn -HeqA' -Heqb'. apply H.
    ++ apply HeqAb. 
    ++ apply HlenA.
  * (** case when x is small **)
    (** k = 0: leverage the fact that x_0 = 0 **)
    repeat split.
    ++ apply H.
    ++ exists 0%nat.
        split.
        ** apply /ssrnat.leP. lia.
        ** intros. split.
          +++ intros. rewrite leqn0 in H2.
             assert (i = 0)%nat. { by apply /eqP. }
             rewrite H3.
             apply finite_residual_0; try rewrite -Heqn; try rewrite -HeqA'; try rewrite -Heqb'; try by apply H. apply HlenA.
             apply HeqAb. intros. 
             assert (vector_inj
                       (repeat (Zconst t 0) (length b)) n.+1 =
                     \col_(j < n.+1) (Zconst t 0)).
             { apply matrixP. unfold eqrel. intros. rewrite !mxE.
               by rewrite nth_repeat.
             } rewrite H4. apply H.
             apply input_bound_at_N_0_equiv.
             assert (vector_inj
                       (repeat (Zconst t 0) (length b)) n.+1 =
                     \col_(j < n.+1) (Zconst t 0)).
             { apply matrixP. unfold eqrel. intros. rewrite !mxE.
               by rewrite nth_repeat.
             } rewrite -Heqn. rewrite H4. rewrite -HeqA' -Heqb'.
             apply H.
             intros. apply H. intros. rewrite mxE. apply H.
          +++ unfold BCMP.
             rewrite Bcompare_correct.
             -- rewrite Rcompare_Lt; first by [].
                change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
                remember (FT2R acc2) as Gamma.
                pose proof (@vector_residual_equiv t A b x0 0%nat).
                assert (length b = length A) by (symmetry; apply HeqAb).
                assert (length x0 = length A).
                { unfold x0. by rewrite !repeat_length. }
                assert ((0 < length A)%coq_nat) by apply HlenA.
                specialize (H2 H3 H4 H5).
                pose proof (@v_equiv t).
                specialize (H6 (resid (jacobi_n A b x0 0)) n).
                assert (length (resid (jacobi_n A b x0 0)) = n.+1).
                { repeat rewrite /matrix_vector_mult !map_length combine_length.
                  rewrite !map_length. unfold jacobi_n. rewrite iter_length.
                  rewrite !seq_length /matrix_rows_nat -HeqAb !Nat.min_id.
                  rewrite Heqn prednK. by []. by apply /ssrnat.ltP.
                  by []. by rewrite /x0 repeat_length.
                } specialize (H6 H7).
                rewrite H6.
                assert ((\col_j0 vector_inj
                          (resid (jacobi_n A b x0 0))
                          n.+1 j0 ord0) = 
                          vector_inj (resid (jacobi_n A b x0 0)) n.+1).
                { apply /matrixP. unfold eqrel. intros. by rewrite !mxE. } 
                rewrite H8. 
                assert ((FT2R
                         (norm2
                            (rev
                               (vec_to_list_float n.+1
                                  (vector_inj (resid (jacobi_n A b x0 0)) n.+1)))) < 0)%Re \/
                        (0 <= FT2R
                               (norm2
                                  (rev
                                     (vec_to_list_float n.+1
                                        (vector_inj (resid (jacobi_n A b x0 0)) n.+1)))))%Re).
                { nra. } destruct H9.
                destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                apply Rlt_le_trans with 0%Re.
                nra.
                apply Rle_trans with 
                ( g1 t n.+1 (n.+1 - 1)%coq_nat +
                  INR n.+1 * (1 + g t n.+1) *
                  (g1 t n.+1 (n.+1 - 1)%coq_nat +
                   2 * (1 + g t n.+1) *
                   (1 + default_rel t) *
                   vec_inf_norm (FT2R_mat (A1_J A')) *
                   d_mag_def_alt A' b' *
                   / (1 - rho_def_alt A' b'))²)%Re.
                apply Rplus_le_le_0_compat; first by apply g1_pos.
                apply Rmult_le_pos. apply Rmult_le_pos. apply pos_INR.
                apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                apply Rle_0_sqr. 
                rewrite HeqGamma. unfold acc2. nra.
                assert (FT2R (norm2 (rev
                               (vec_to_list_float n.+1
                                  (vector_inj
                                     (resid
                                        (jacobi_n A b x0 0)) n.+1)))) =
                         Rabs (FT2R (norm2 (rev
                               (vec_to_list_float n.+1
                                  (vector_inj
                                     (resid
                                        (jacobi_n A b x0 0)) n.+1)))))).
                 { rewrite Rabs_right. nra. by apply Rle_ge. }
                 rewrite H10. clear H10.
                 eapply Rle_lt_trans.
                 apply norm2_vec_inf_norm_rel.
                 *** intros. apply finite_in with A b. apply HlenA. apply HeqAb.
                    unfold resid in H10. rewrite -Heqn. apply H. 
                    rewrite -Heqn. rewrite -HeqA'. apply H.
                    rewrite -Heqn.
                     assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                     { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by rewrite nth_repeat.
                     } intros. rewrite H11. apply H.
                     apply input_bound_at_N_0_equiv.
                     rewrite -Heqn.
                     assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                     { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by rewrite nth_repeat.
                     } rewrite H11.
                     rewrite -Heqb' -HeqA'. apply H.
                     rewrite -Heqn.
                     intros. rewrite -?Heqb' -HeqA'. apply H. rewrite -Heqn. intros. rewrite mxE. rewrite -?Heqb' -?HeqA'. apply H.
                     rewrite -Heqn.
                     intros. rewrite -?Heqb' -?HeqA'. apply H. rewrite -Heqn.
                     apply H10.
                 *** rewrite  -H8 -H6. apply finite_residual_0.
                    apply HlenA. apply HeqAb. unfold size_constraint. 
                    destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                    unfold size_constraint in size_cons. by rewrite Heqn in size_cons.
                    rewrite -Heqn. rewrite -?Heqb' -?HeqA'. apply H.
                    rewrite -Heqn.
                     assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                     { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by rewrite nth_repeat.
                     } intros. rewrite -?Heqb' -?HeqA'. rewrite H10. apply H.
                     apply input_bound_at_N_0_equiv.
                     rewrite -Heqn.
                     assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                     { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by rewrite nth_repeat.
                     } rewrite -?Heqb' -?HeqA'. rewrite H10.
                     apply H.
                     rewrite -Heqn.
                     intros. rewrite -?Heqb' -?HeqA'. apply H. rewrite -Heqn. intros. rewrite mxE. rewrite -?Heqb' -?HeqA'. apply H.
                     rewrite -Heqn.
                     intros. rewrite -?Heqb' -?HeqA'. apply H. 
                 *** assert (HfA2l :  (forall i j : 'I_(length A).-1.+1,
                                         finite
                                           (A2_J
                                              (matrix_inj A (length A).-1.+1
                                                 (length A).-1.+1) i j))).
                      { rewrite -Heqn. intros. rewrite -?Heqb' -?HeqA'. apply H. }
                      assert (Hfx0l : (forall i : 'I_(length A).-1.+1,
                                       finite
                                         (vector_inj
                                            (repeat (Zconst t 0)
                                               (length b))
                                            (length A).-1.+1 i ord0))).
                      { rewrite -Heqn. intros. 
                        assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                         { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                           by rewrite nth_repeat.
                         } rewrite H10. rewrite -?Heqb' -?HeqA'. apply H.
                      } 
                      assert (HfAl : (forall i : 'I_(length A).-1.+1,
                                       finite
                                         (matrix_inj A (length A).-1.+1
                                            (length A).-1.+1 i i))).
                      { rewrite -Heqn. intros. rewrite -?Heqb' -?HeqA'. apply H. }
                      assert (HfA1_invl: (forall i : 'I_(length A).-1.+1,
                                           finite
                                             (A1_inv_J
                                                (matrix_inj A (length A).-1.+1
                                                   (length A).-1.+1) i ord0))).
                      { rewrite -Heqn. intros. rewrite -?Heqb' -?HeqA'.  rewrite mxE. apply H. }
                      assert (Hfbl : (forall i : 'I_(length A).-1.+1,
                                       finite
                                         (vector_inj b (length A).-1.+1 i
                                            ord0))).
                      { rewrite -Heqn. intros. rewrite -?Heqb' -?HeqA'. apply H. }
                      assert (Hinpl : input_bound_at_N_0 A x0 b).
                      { apply input_bound_at_N_0_equiv.
                         rewrite -Heqn.
                         assert (vector_inj
                                   (repeat (Zconst t 0) (length b)) n.+1 =
                                 \col_(j < n.+1) (Zconst t 0)).
                         { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                           by rewrite nth_repeat.
                         } rewrite H10.
                         rewrite -?Heqb' -?HeqA'. apply H.
                      } unfold resid.  rewrite Heqn. 
                    rewrite H2. unfold residual_math.
                    remember (vector_inj x0 n.+1) as x0'.
                    pose proof (@vec_norm_diag _ t n  (A1_J A')
                                (X_m_jacobi 1 x0' b' A' -f
                                    X_m_jacobi 0 x0' b' A')).
                    assert (forall xy : ftype t * ftype t,
                              In xy
                                (combine
                                   (vec_to_list_float n.+1
                                      (A1_J A'))
                                   (vec_to_list_float n.+1
                                      (X_m_jacobi 1 x0' b' A' -f
                                       X_m_jacobi 0 x0' b' A'))) ->
                              finite xy.1 /\ finite xy.2 /\
                              finite (BMULT xy.1 xy.2)).
                    { intros.
                      pose proof (@finite_implies_1 t A b HlenA HeqAb).
                      pose proof (@finite_residual_0 t A b HlenA HeqAb).
                      destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                      rewrite Heqn in size_cons.
                      specialize (H13 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                      specialize (H12 H13).
                      apply H12. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                      apply H11. 
                    }
                   specialize (H10 H11).
                   assert ((vec_inf_norm
                            (FT2R_mat
                               (diag_vector_mult 
                                  (A1_J A')
                                  (X_m_jacobi 1 x0' b' A' -f
                                   X_m_jacobi 0 x0' b' A')) -
                             diag_matrix_vec_mult_R
                               (FT2R_mat (A1_J A'))
                               (FT2R_mat
                                  (X_m_jacobi 1 x0' b' A' -f
                                   X_m_jacobi 0 x0' b' A'))) <=
                          vec_inf_norm (FT2R_mat (A1_J A')) *
                          vec_inf_norm
                            (FT2R_mat
                               (X_m_jacobi 1 x0' b' A' -f
                                X_m_jacobi 0 x0' b' A')) *
                          g t n.+1 + g1 t n.+1 (n.+1 - 1))). { by apply /RleP. }
                   apply reverse_triang_ineq in H12.
                   assert ((vec_inf_norm
                            (FT2R_mat
                               (diag_vector_mult (A1_J A')
                                  (X_m_jacobi 1 x0' b' A' -f
                                   X_m_jacobi 0 x0' b' A'))) <=
                            (vec_inf_norm (FT2R_mat (A1_J A')) *
                              vec_inf_norm
                                (FT2R_mat
                                   (X_m_jacobi 1 x0' b' A' -f
                                    X_m_jacobi 0 x0' b' A'))) * 
                             (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re).
                   { rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                     assert (forall a b c d :R, (a - b <= c + d)%Re -> (a <= b + c+d)%Re).
                     { intros. nra. } apply H13. eapply Rle_trans; last by (apply /RleP; apply H12).
                     rewrite -RminusE. apply Rplus_le_compat_l.
                     apply Ropp_le_contravar.
                     apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
                   } eapply Rle_lt_trans.
                   apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rmult_le_compat_l. apply pos_INR.
                   apply Rle_trans with 
                   (Rsqr (vec_inf_norm (FT2R_mat (A1_J A')) *
                           vec_inf_norm
                             (FT2R_mat
                                (X_m_jacobi 1 x0' b' A' -f
                                 X_m_jacobi 0 x0' b' A')) *
                           (1 + g t n.+1) +
                           g1 t n.+1 (n.+1 - 1)%coq_nat)).
                   apply Rsqr_incr_1. rewrite -?Heqn -?Heqb' -?HeqA' -?Heqx0'. apply H13. 
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat; last by apply g1_pos.
                   repeat apply Rmult_le_pos.
                   apply /RleP. apply vec_norm_pd.
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rle_refl.
                   assert (X_m_jacobi 1 x0' b' A' = jacobi_iter x0' b' A'). { by simpl. }
                   assert (X_m_jacobi 0 x0' b' A' = x0'). { by simpl. }
                   rewrite H14 H15. unfold jacobi_iter.
                   clear H10 H11 H12 H13 H14 H15.
                   pose proof (@vec_float_sub _ t n 
                                (diag_vector_mult (A1_inv_J A')
                                    (b' -f A2_J A' *f x0')) x0').
                   assert (forall xy : ftype t * ftype t,
                              In xy
                                (combine
                                   (vec_to_list_float n.+1
                                      (diag_vector_mult
                                         (A1_inv_J A')
                                         (b' -f A2_J A' *f x0')))
                                   (vec_to_list_float n.+1 x0')) ->
                              finite xy.1 /\
                              finite xy.2 /\
                              finite (BPLUS xy.1 (BOPP xy.2))).
                   { intros.
                      pose proof (@finite_implies_2 t A b HlenA HeqAb).
                      pose proof (@finite_residual_0 t A b HlenA HeqAb).
                      destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                      rewrite Heqn in size_cons.
                      specialize (H13 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                      specialize (H12 H13).
                      apply H12. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                      apply H11.
                    }
                   specialize (H10 H11).
                   apply reverse_triang_ineq in H10.
                   eapply Rle_lt_trans. apply Rplus_le_compat_r.
                   apply Rmult_le_compat_r.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rmult_le_compat_l. apply pos_INR.
                   apply Rle_trans with
                   (Rsqr (vec_inf_norm (FT2R_mat (A1_J A')) *
                      ((vec_inf_norm
                          (FT2R_mat
                             (diag_vector_mult 
                                (A1_inv_J A')
                                (b' -f A2_J A' *f x0'))) +
                        vec_inf_norm (FT2R_mat x0')) *
                        (1 + default_rel t)) * 
                      (1 + g t n.+1) +
                      g1 t n.+1 (n.+1 - 1)%coq_nat)%Re).
                   apply Rsqr_incr_1.
                   apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                   eapply Rle_trans. 
                   assert (forall x y z :R, (x - y <= z)%Re -> (x <= y + z)%Re). { intros. nra. }
                   apply H12. apply /RleP. apply H10. rewrite -RplusE -RmultE.
                   apply Rplus_le_compat_r. eapply Rle_trans.
                   apply /RleP. apply triang_ineq. rewrite -vec_inf_norm_opp.
                   rewrite -RplusE. apply Rle_refl.
                   apply Rplus_le_le_0_compat; last by apply g1_pos.
                   apply Rmult_le_pos; last by 
                   (apply Rplus_le_le_0_compat; try nra; try apply g_pos).
                   apply Rmult_le_pos; try (apply /RleP; apply vec_norm_pd).
                   apply Rplus_le_le_0_compat; last by apply g1_pos.
                   apply Rmult_le_pos; last by 
                   (apply Rplus_le_le_0_compat; try nra; try apply g_pos).
                   apply Rmult_le_pos; try (apply /RleP;apply vec_norm_pd).
                   apply Rmult_le_pos; last by 
                   (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
                   apply Rplus_le_le_0_compat; try (apply /RleP; apply vec_norm_pd).
                   apply Rsqr_incr_1.
                   apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                   apply Rmult_le_compat_r. 
                   apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                   apply Rplus_le_compat_r.
                   pose proof (@vec_norm_diag _ t n (A1_inv_J A') (b' -f A2_J A' *f x0')).
                   assert (forall xy : ftype t * ftype t,
                             In xy
                               (combine
                                  (vec_to_list_float n.+1
                                     (A1_inv_J A'))
                                  (vec_to_list_float n.+1
                                     (b' -f A2_J A' *f x0'))) ->
                             finite xy.1 /\
                             finite xy.2 /\
                             finite (BMULT xy.1 xy.2)).
                   { intros.
                      pose proof (@finite_implies_3 t A b HlenA HeqAb).
                      pose proof (@finite_residual_0 t A b HlenA HeqAb).
                      destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                      rewrite Heqn in size_cons.
                      specialize (H15 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                      specialize (H14 H15).
                      apply H14. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                      apply H13. 
                   }
                   specialize (H12 H13).
                   apply Rle_trans with
                   (vec_inf_norm
                         (FT2R_mat (A1_inv_J A')) *
                       vec_inf_norm
                         (FT2R_mat (b' -f A2_J A' *f x0')) *
                       (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1))%Re.
                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                   apply Rle_trans with 
                   (vec_inf_norm 
                      (diag_matrix_vec_mult_R
                          (FT2R_mat (A1_inv_J A'))
                          (FT2R_mat
                             (b' -f A2_J A' *f x0'))) + 
                     vec_inf_norm (FT2R_mat (A1_inv_J A')) *
                       vec_inf_norm
                         (FT2R_mat (b' -f A2_J A' *f x0')) *
                       g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re.
                   assert (vec_inf_norm
                               (FT2R_mat
                                  (diag_vector_mult
                                     (A1_inv_J A')
                                     (b' -f A2_J A' *f x0')) -
                                diag_matrix_vec_mult_R
                                  (FT2R_mat (A1_inv_J A'))
                                  (FT2R_mat
                                     (b' -f A2_J A' *f x0'))) <=
                             vec_inf_norm
                               (FT2R_mat (A1_inv_J A')) *
                             vec_inf_norm
                               (FT2R_mat
                                  (b' -f A2_J A' *f x0')) *
                             g t n.+1 + g1 t n.+1 (n.+1 - 1)). { by apply /RleP. }
                   apply reverse_triang_ineq in H14.
                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                   { intros. nra. } apply H15. apply /RleP. apply H14.
                   repeat apply Rplus_le_compat_r. apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
                   apply Rplus_le_compat_r.
                   apply Rmult_le_compat_r.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                   pose proof (@vec_float_sub _ t n b' (A2_J A' *f x0')).
                   assert (forall xy : ftype t * ftype t,
                               In xy
                                 (combine
                                    (vec_to_list_float n.+1 b')
                                    (vec_to_list_float n.+1
                                       (A2_J A' *f x0'))) ->
                               finite xy.1 /\
                               finite xy.2 /\
                               finite (BPLUS xy.1 (BOPP xy.2))).
                   { intros.
                      pose proof (@finite_implies_4 t A b HlenA HeqAb).
                      pose proof (@finite_residual_0 t A b HlenA HeqAb).
                      destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                      rewrite Heqn in size_cons.
                      specialize (H17 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl).
                      specialize (H16 H17).
                      apply H16. rewrite -Heqn -HeqA' -Heqx0' -Heqb'.
                      apply H15. 
                   }
                   specialize (H14 H15).
                   apply Rle_trans with
                   ((vec_inf_norm (FT2R_mat b') +
                         vec_inf_norm
                           (FT2R_mat (A2_J A' *f x0'))) *
                       (1 + default_rel t))%Re.
                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                   apply reverse_triang_ineq in H14. eapply Rle_trans.
                   assert ((vec_inf_norm
                              (FT2R_mat
                                 (b' -f A2_J A' *f x0')) -
                            vec_inf_norm
                              (FT2R_mat b' -
                               FT2R_mat (A2_J A' *f x0')) <=
                            (vec_inf_norm (FT2R_mat b') +
                             vec_inf_norm
                               (FT2R_mat (A2_J A' *f x0'))) *
                            default_rel t)%Re). { by apply /RleP. }
                   assert (forall a b c:R, (a - b <= c)%Re -> (a <= b +c)%Re). { intros. nra. }
                   apply H17 in H16. apply H16.
                   apply Rplus_le_compat_r. eapply Rle_trans.
                   apply /RleP. apply triang_ineq. rewrite -vec_inf_norm_opp. rewrite -RplusE. nra.
                   apply Rmult_le_compat_r.
                   apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                   apply Rplus_le_compat_l.
                   pose proof (@matrix_vec_mult_bound_corollary _ n t (A2_J A') x0').
                   assert (forall (xy : ftype t * ftype t)
                               (i : 'I_n.+1),
                             In xy
                               (combine
                                  (vec_to_list_float n.+1
                                     (\row_j A2_J A'
                                              (inord i) j)^T)
                                  (vec_to_list_float n.+1
                                     x0')) ->
                             finite xy.1 /\ finite xy.2). 
                   { intros.
                      pose proof (@finite_implies_5 t A b HlenA HeqAb).
                      pose proof (@finite_residual_0 t A b HlenA HeqAb).
                      destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                      rewrite Heqn in size_cons.
                      specialize (H19 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl). 
                      rewrite -Heqn in H18. specialize (H18 H19 xy i).
                      apply H18. rewrite HeqA' Heqx0' in H17.
                      apply H17.
                  }
                  assert (forall i : 'I_n.+1,
                           finite 
                             (let l1 :=
                                vec_to_list_float n.+1
                                  (\row_j A2_J A'
                                            (inord i) j)^T
                                in
                              let l2 :=
                                vec_to_list_float n.+1
                                  (\col_j x0' j 0) in
                              dotprod_r l1 l2)).
                  { intros.
                      pose proof (@finite_implies_6 t A b HlenA HeqAb).
                      pose proof (@finite_residual_0 t A b HlenA HeqAb).
                      destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                      rewrite Heqn in size_cons.
                      specialize (H19 size_cons HfA2l Hfx0l Hinpl HfAl HfA1_invl Hfbl). 
                      rewrite -Heqn in H18.
                      specialize (H18 H19 i).
                      rewrite HeqA' Heqx0'.
                      apply H18.         
                  }
                  specialize (H16 H17 H18).
                  apply reverse_triang_ineq in H16.
                  apply Rle_trans with 
                  (matrix_inf_norm
                        (FT2R_mat (A2_J A')) *
                      vec_inf_norm (FT2R_mat x0') +
                      matrix_inf_norm
                        (FT2R_mat (A2_J A')) *
                      vec_inf_norm (FT2R_mat x0') *
                      g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re.
                   apply Rle_trans with
                   ( vec_inf_norm
                            (FT2R_mat (A2_J A') *m 
                             FT2R_mat x0') + 
                     matrix_inf_norm
                        (FT2R_mat (A2_J A')) *
                      vec_inf_norm (FT2R_mat x0') *
                      g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re.
                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                   { intros. nra. } apply H19. apply /RleP. apply H16.
                   repeat apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                   assert ((matrix_inf_norm (FT2R_mat (A2_J A')) *
                             vec_inf_norm (FT2R_mat x0') +
                             matrix_inf_norm (FT2R_mat (A2_J A')) *
                             vec_inf_norm (FT2R_mat x0') *
                             g t n.+1 + g1 t n.+1 (n.+1 - 1))%Re =
                           ((matrix_inf_norm (FT2R_mat (A2_J A')) *
                             vec_inf_norm (FT2R_mat x0')) * (1 + g t n.+1 )+
                            g1 t n.+1 (n.+1 - 1))%Re). { nra. } rewrite H19.
                   apply Rle_refl.
                   apply Rplus_le_le_0_compat;last by apply g1_pos.
                   repeat apply Rmult_le_pos.
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat; try (apply /RleP; apply vec_norm_pd).
                   apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rplus_le_le_0_compat; last by apply g1_pos.
                   repeat apply Rmult_le_pos.
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat;last by (apply /RleP; apply vec_norm_pd).
                   apply Rplus_le_le_0_compat;last by apply g1_pos.
                   repeat apply Rmult_le_pos.
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat. 
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat; last by apply g1_pos.
                   repeat apply Rmult_le_pos.
                   apply /RleP. apply matrix_norm_pd.
                   apply /RleP. apply vec_norm_pd.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                   apply Rplus_le_le_0_compat. nra. apply g_pos.
                   destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                   destruct HG as [_ HG].
                   assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                      by rewrite nth_repeat.
                    } rewrite Heqx0' /x0. rewrite H. rewrite HeqGamma. rewrite -Heqn. apply HG.
             -- rewrite <- finite_is_finite. apply finite_residual_0.
                apply HlenA. apply HeqAb. unfold size_constraint. 
                destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]. 
                rewrite -Heqn. by unfold size_constraint in size_cons.
                rewrite -?Heqn -?HeqA' -?Heqb'. intros.  apply H.
                rewrite -?Heqn -?HeqA' -?Heqb'. intros.
                assert (vector_inj
                               (repeat (Zconst t 0) (length b)) n.+1 =
                             \col_(j < n.+1) (Zconst t 0)).
                { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                  by rewrite nth_repeat.
                }  rewrite H2.  apply H.
                apply input_bound_at_N_0_equiv.
                assert (vector_inj
                               (repeat (Zconst t 0) (length b)) (length A).-1.+1 =
                             \col_(j < (length A).-1.+1) (Zconst t 0)).
                { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                  by rewrite nth_repeat.
                }  rewrite H2. rewrite -?Heqn -?HeqA' -?Heqb'.
                apply H.
                rewrite -?Heqn -?HeqA' -?Heqb'. intros. apply H.
                rewrite -?Heqn -?HeqA' -?Heqb'. intros. rewrite mxE. apply H.
                rewrite -?Heqn -?HeqA' -?Heqb'. intros. apply H.
             -- rewrite <- finite_is_finite. apply H.
Qed.
(** merge N= 0 and ||x|| <= ? case **)

End WITH_NANS.