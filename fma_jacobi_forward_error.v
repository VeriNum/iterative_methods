From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

Require Import floatlib inf_norm_properties.

Require Import common fma_dot_acc float_acc_lems dotprod_model.
Require Import fma_matrix_vec_mult vec_sum_inf_norm_rel.
Require Import fma_real_func_model fma_floating_point_model.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas fma_is_finite finite_lemmas_additional.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section WITHNANS.
Context {NANS: Nans}. 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).

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


Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A_real in
  vec_inf_norm (FT2R_mat x_k - x).



Lemma rho_ge_0 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel ty in
  let rho := ((((1 + g ty n.+1) * (1 + delta) *
                  g ty n.+1 + delta * (1 + g ty n.+1) +
                  g ty n.+1) * (1 + delta) + delta) * R +
                (((1 + g ty n.+1) * (1 + delta) *
                  g ty n.+1 + delta * (1 + g ty n.+1) +
                  g ty n.+1) * default_abs ty +
                 default_abs ty) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re in
 (0 <= rho)%Re.
Proof.
intros.
unfold rho.
repeat apply Rplus_le_le_0_compat.
+ apply Rmult_le_pos.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; last by apply g_pos.
         repeat apply Rplus_le_le_0_compat; apply Rmult_le_pos. 
         -- apply Rmult_le_pos; try apply Rplus_le_le_0_compat; 
            try nra; try apply g_pos. unfold delta. 
            apply default_rel_ge_0.
         -- apply g_pos.
         -- unfold delta. 
            apply default_rel_ge_0.
         -- apply Rplus_le_le_0_compat; last by apply g_pos. nra. 
      ++ apply Rplus_le_le_0_compat. nra.  
         unfold delta. 
         apply default_rel_ge_0.
    * unfold delta. 
      apply default_rel_ge_0.
  - unfold R2. apply Rmult_le_pos.
    * apply /RleP. apply vec_norm_pd.
    * apply /RleP. apply matrix_norm_pd.
+ apply Rmult_le_pos.
  - repeat apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply Rmult_le_pos; last by apply default_abs_ge_0.
    apply Rplus_le_le_0_compat; last by apply g_pos.
    apply Rplus_le_le_0_compat. 
    * repeat apply Rmult_le_pos.
      ++ apply Rplus_le_le_0_compat; last by apply g_pos. nra. 
      ++ apply Rplus_le_le_0_compat. nra.  
         unfold delta. 
         apply default_rel_ge_0.
      ++ apply g_pos.
    * apply Rmult_le_pos.
      ++ unfold delta. 
         apply default_rel_ge_0.
      ++ apply Rplus_le_le_0_compat; last by apply g_pos. nra.
  - apply /RleP. apply matrix_norm_pd.
+ unfold R2. apply Rmult_le_pos.
    * apply /RleP. apply vec_norm_pd.
    * apply /RleP. apply matrix_norm_pd.
Qed.


Lemma add_vec_distr {n:nat}:
  forall a b c: 'cV[R]_n,
  a - b + b - c = (a-b) + (b-c).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. by rewrite -addrA.
Qed.


Lemma add_vec_distr_1 {n:nat}:
  forall a b c: 'cV[R]_n,
  (a+b) - (b+c) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma add_vec_distr_2 {n:nat}:
  forall a b c: 'cV[R]_n,
  (a-b) + (b-c) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma add_vec_distr_3 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a+b) - (c+d) = (a-c) + (b-d).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma add_vec_distr_4 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a - b) - (a - d) = d - b.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.

Lemma sub_vec_comm_1 {n:nat}:
  forall a b: 'cV[R]_n,
  (a - b) = - (b-a).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.

Lemma sub_vec_2 {n:nat}:
  forall a b: 'cV[R]_n,
  (a - b) = (a + (-b)).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma sub_vec_3 {n:nat}:
  forall a b: 'cV[R]_n,
  (a - b) + b = a.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.



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


Lemma rel_le_1 {ty} {n:nat}:
  (/ INR n.+1 *
     ((1 + default_rel ty) *
      / (1 + default_rel ty) ^ n.+1) <= 1)%Re.
Proof.
assert (forall x y:R , (x * y <= 1 * 1)%Re -> (x * y <= 1)%Re).
{ intros. nra. } apply H.
apply Rmult_le_compat.
+ apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
+ apply Rmult_le_pos.
  - apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
  - apply Rlt_le. apply Rinv_0_lt_compat.
    apply pow_lt. apply Rplus_lt_0_compat. nra.
    apply default_rel_gt_0.
+ assert (1%Re = (/1)%Re). { nra. } rewrite H0.
  destruct n. simpl;nra.
  apply Rlt_le. apply Rinv_1_lt_contravar. nra.
  replace 1%Re with (INR 1) by (simpl;nra).
  apply lt_INR. lia.
+ simpl. rewrite Rinv_mult_distr.
  - assert (((1 + default_rel ty) *
               (/ (1 + default_rel ty) *
                / (1 + default_rel ty) ^ n))%Re = 
             ( ((1 + default_rel ty) * /(1 + default_rel ty)) *
              (/ (1 + default_rel ty) ^ n))%Re).
    { nra. } rewrite H0. rewrite Rinv_r.
    * destruct n. simpl;nra.
      assert ((/ (1 + default_rel ty) ^ n.+1 < /1)%Re -> 
              (1 * / (1 + default_rel ty) ^ n.+1 <= 1)%Re).
      { nra. } apply H1.
      apply Rinv_1_lt_contravar. nra. 
      apply Rlt_pow_R1.
      assert ((0 < default_rel ty)%Re ->  (1 < 1 + default_rel ty)%Re).
      { nra. } apply H2. apply default_rel_gt_0. lia.
    * assert ((0 < default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
      { nra. } apply H1. apply default_rel_gt_0.
  - assert ((0 < default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
    { nra. } apply H0. apply default_rel_gt_0.
  - apply pow_nonzero. 
    assert ((0 < default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
    { nra. } apply H0. apply default_rel_gt_0.
Qed.


Lemma delta_eps_lt_fmax {ty}:
  (0 < 2 * fmax ty * default_rel ty - default_abs ty)%Re.
Proof.
apply Rgt_lt. apply Rgt_minus. apply Rlt_gt.
unfold fmax, default_abs, default_rel.
apply Rlt_le_trans with
(1 * bpow Zaux.radix2 (3 - femax ty - fprec ty))%Re.
+ apply Rmult_lt_compat_r. apply bpow_gt_0. nra.
+ assert ((2 * bpow Zaux.radix2 (femax ty) *
            (/ 2 * bpow Zaux.radix2 (- fprec ty + 1)))%Re = 
           (bpow Zaux.radix2 (femax ty) * bpow Zaux.radix2 (- fprec ty + 1))%Re).
  { nra. } rewrite H.
  assert ((1 * bpow Zaux.radix2 (3 - femax ty - fprec ty))%Re = 
          bpow Zaux.radix2 (3 - femax ty - fprec ty)).
  { nra. } rewrite H0. apply Rlt_le.
  rewrite Z.add_comm. rewrite Rmult_comm.
  rewrite -bpow_plus. apply bpow_lt. rewrite Z.add_shuffle0.
  apply Z.add_lt_mono_r.
  apply Z.lt_sub_lt_add. simpl.
  unfold Z.sub. rewrite Z.opp_involutive. 
  assert (2%Z = (1+1)%Z). { by simpl. }
  rewrite H1. 
  apply Z.add_lt_mono;
  apply Z.lt_trans with (fprec ty); try apply fprec_gt_one;
  try apply fprec_lt_femax.
Qed.



Lemma vec_norm_diag {ty} {n:nat} (v1 v2 : 'cV[ftype ty]_n.+1):
  (forall (xy : ftype ty * ftype ty),
    In xy
      (combine
         (vec_to_list_float n.+1  v1)
         (vec_to_list_float n.+1 v2)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\
    is_finite (fprec ty) (femax ty) (BMULT ty xy.1 xy.2) = true) ->
  (vec_inf_norm (FT2R_mat (diag_vector_mult v1 v2) - 
                diag_matrix_vec_mult_R (FT2R_mat v1) (FT2R_mat v2)) <=
  (vec_inf_norm (FT2R_mat v1) * vec_inf_norm (FT2R_mat v2)) * 
  g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re.
Proof.
intros.
unfold diag_vector_mult, diag_matrix_vec_mult_R.
unfold vec_inf_norm.
apply bigmax_le.
+ by rewrite size_map size_enum_ord.
+ intros. rewrite seq_equiv. rewrite nth_mkseq;
  last by rewrite size_map size_enum_ord in H0.
  rewrite !mxE.
  pose proof (BMULT_accurate ty 
              (nth (n.+1.-1 - @inord n i) (vec_to_list_float n.+1 v1) (Zconst ty 0))
              (nth (n.+1.-1 - @inord n i) (vec_to_list_float n.+1 v2) (Zconst ty 0))).
  assert (Bmult_no_overflow ty
       (FT2R
          (nth (n.+1.-1 - @inord n i)
             (vec_to_list_float n.+1 v1)
             (Zconst ty 0)))
       (FT2R
          (nth (n.+1.-1 - @inord n i)
             (vec_to_list_float n.+1 v2)
             (Zconst ty 0)))). 
  { apply is_finite_BMULT_no_overflow.  rewrite !nth_vec_to_list_float.
    + rewrite inord_val.
      specialize (H ((v1 (inord i) ord0), (v2 (inord i) ord0))).
      assert (In
                (v1 (inord i) ord0, v2 (inord i) ord0)
                (combine (vec_to_list_float n.+1 v1)
                   (vec_to_list_float n.+1 v2))).
      { apply in_rev. rewrite -combine_rev; last by rewrite !length_veclist.
        assert ((v1 (inord i) ord0, v2 (inord i) ord0) = 
                           nth i (combine (rev (vec_to_list_float n.+1 v1))
                                    (rev (vec_to_list_float n.+1 v2))) (Zconst ty 0, Zconst ty 0)).
                  { rewrite combine_nth. rewrite !rev_nth !length_veclist.
                    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat).
                    { lia. } rewrite H2. rewrite !nth_vec_to_list_float; try by [].
                    by rewrite size_map size_enum_ord in H0.
                    by rewrite size_map size_enum_ord in H0.
                    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H0.
                    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H0.
                    by rewrite !rev_length !length_veclist.
                 } rewrite H2. apply nth_In. rewrite combine_length.
                 rewrite !rev_length !length_veclist Nat.min_id.
                 rewrite size_map size_enum_ord in H0. by apply /ssrnat.ltP.
     } specialize (H H2). apply H.
   + rewrite inordK; by rewrite size_map size_enum_ord in H0.
   + rewrite inordK; by rewrite size_map size_enum_ord in H0.
} specialize (H1 H2).
  destruct H1 as [d [e [Heq [Hd [He H1]]]]].
  rewrite H1. rewrite !nth_vec_to_list_float.
  - rewrite !nth_vec_to_list_real.
    * rewrite !inord_val. rewrite !mxE.
      rewrite -!RmultE -!RminusE. 
      assert ((FT2R (v1 (inord i) ord0) *
                FT2R (v2 (inord i) ord0) * (1 + d) + e -
                FT2R (v1 (inord i) ord0) *
                FT2R (v2 (inord i) ord0))%Re =
              ((FT2R (v1 (inord i) ord0) * FT2R (v2 (inord i) ord0)) * d + e)%Re).
      { nra. } rewrite H3.
      eapply Rle_trans.
      ++ apply Rabs_triang.
      ++ apply Rplus_le_compat.
         -- rewrite !Rabs_mult. apply Rmult_le_compat.
            ** apply Rmult_le_pos; apply Rabs_pos.
            ** apply Rabs_pos.
            ** apply Rmult_le_compat; try apply Rabs_pos.
                +++ apply Rle_trans with  
                    [seq Rabs (FT2R_mat v1 i0 0)
                          | i0 <- enum 'I_n.+1]`_i.
                    --- rewrite seq_equiv. rewrite nth_mkseq;
                        last by rewrite size_map size_enum_ord in H0.
                        rewrite !mxE. apply Rle_refl.
                    --- apply /RleP.
                        apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v1 i0 0)
                                                    | i0 <- enum 'I_n.+1] i).
                        rewrite size_map size_enum_ord .
                        by rewrite size_map size_enum_ord in H0.
                +++ apply Rle_trans with  
                    [seq Rabs (FT2R_mat v2 i0 0)
                          | i0 <- enum 'I_n.+1]`_i.
                    --- rewrite seq_equiv. rewrite nth_mkseq;
                        last by rewrite size_map size_enum_ord in H0.
                        rewrite !mxE. apply Rle_refl.
                    --- apply /RleP.
                        apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v2 i0 0)
                                                    | i0 <- enum 'I_n.+1] i).
                        rewrite size_map size_enum_ord .
                        by rewrite size_map size_enum_ord in H0.
           ** unfold g. 
              eapply Rle_trans. apply Hd.
              assert (((1 + default_rel ty) ^ 1 <= (1 + default_rel ty) ^ n.+1)%Re ->
                       (default_rel ty <= (1 + default_rel ty) ^ n.+1 - 1)%Re).
              { nra. } apply H4. apply Rle_pow .
              apply default_rel_plus_1_ge_1. lia.
       -- unfold g1. eapply Rle_trans. apply He.
          rewrite Rmult_assoc. 
          assert (forall x y z:R, (1 * x <= y * z)%Re -> (x <= y * z)%Re).
          { intros. nra. }  apply H4.
          apply Rmult_le_compat.
          ** nra.
          ** apply default_abs_ge_0. 
          ** replace 1%Re with (INR 1) by (simpl;auto).
             apply le_INR. lia.
          ** assert (forall x z:R, (x * 1 <= x * z)%Re -> (x <= x * z)%Re).
             { intros. nra. }  apply H5.
             apply Rmult_le_compat_l.
             +++ apply default_abs_ge_0.
             +++ assert (forall x:R, (0 <= x)%Re -> (1 <= 1 + x)%Re).
                 { intros. nra. } apply H6. apply g_pos.
  * rewrite inordK; by rewrite size_map size_enum_ord in H0.
  * rewrite inordK; by rewrite size_map size_enum_ord in H0.
 - rewrite inordK; by rewrite size_map size_enum_ord in H0.
 - rewrite inordK; by rewrite size_map size_enum_ord in H0.
Qed.

Lemma real_const_1 {ty}:
  FT2R (Zconst ty 1) = 1%Re.
Proof.
unfold FT2R. unfold Zconst.
pose proof IEEE754_extra.BofZ_exact.
specialize (H (fprec ty) (femax ty) (Pos2Z.is_pos (fprecp ty))
            (fprec_lt_femax ty) 1%Z).
assert ((- 2 ^ fprec ty <= 1 <= 2 ^ fprec ty)%Z).
{ apply in_fprec_bound1. }
specialize (H H0).
destruct H as [H H1].
by rewrite H.
Qed.


(*** Lemma for error bound on the inverse ***)
Lemma inverse_mat_norm_bound {ty} {n:nat} (A: 'M[ftype ty]_n.+1):
  (forall i, is_finite _ _ (BDIV ty (Zconst ty 1) (A i i )) = true) ->
  (forall i, is_finite _ _ (A i i) = true) ->
  let A_real := FT2R_mat A in
  (vec_inf_norm (FT2R_mat (A1_inv_J A) - A1_diag A_real) <=
    vec_inf_norm (A1_diag A_real) * (default_rel ty) + (default_abs ty))%Re.
Proof.
intros.
assert (Hneq: forall i, (FT2R (A i i) <> 0%Re)).
{ intros. by apply BDIV_FT2R_sep_zero. }
unfold vec_inf_norm. rewrite RmultE. rewrite mulrC.
rewrite -bigmaxr_mulr.
+ apply bigmax_le; first by rewrite size_map size_enum_ord.
  intros. rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H1.
  rewrite !mxE. 
  apply Rle_trans with 
  ([seq (default_rel ty *
         Rabs (A1_diag A_real i0 0))%Ri
      | i0 <- enum 'I_n.+1]`_i + (default_abs ty))%Re.
  - rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H1.
    rewrite -RmultE -RminusE. rewrite !mxE.
    specialize (H0 (@inord n i)). specialize (H (@inord n i)).
    pose proof (@Binv_accurate _ ty (A (inord i) (inord i))) .
    specialize (H2 H H0).
    destruct H2 as [d [e [Hpr [Hdf [Hde H2]]]]].
    rewrite H2 /=. rewrite real_const_1.
    assert ((1 / FT2R (A (inord  i) (inord i)) *
              (1 + d) + e -
              1 / FT2R (A (inord i) (inord i)))%Re = 
            ((1 / FT2R (A (inord i) (inord i))) * d + e)%Re).
    { nra. } rewrite H3.
    eapply Rle_trans.
    apply Rabs_triang.
    * apply Rplus_le_compat.
      ++ rewrite Rmult_comm. rewrite Rabs_mult. apply Rmult_le_compat_r.
         apply Rabs_pos. apply Hdf.
      ++ apply Hde.
  - apply Rplus_le_compat_r.
    apply /RleP.
    apply (@bigmaxr_ler _ 0%Re [seq default_rel ty *
                                     Rabs (A1_diag A_real i0 0)
                                   | i0 <- enum 'I_n.+1] i).
    rewrite size_map size_enum_ord.
    by rewrite size_map size_enum_ord in H1.
+ apply /RleP. apply default_rel_ge_0.
Qed.


Lemma list_split_l {T} (l : list (T * T)) (a:T * T):
  (List.split (a :: l)).1 = (a.1 :: (List.split l).1).
Proof.
induction l; simpl; intros; auto.
+ destruct a; auto.
+ destruct (List.split l); auto.
  destruct a0; simpl.
  destruct a; simpl; auto.
Qed.
  

Lemma list_split_r {T} (l : list (T * T)) (a:T * T):
  (List.split (a :: l)).2 = (a.2 :: (List.split l).2).
Proof.
induction l; simpl; intros; auto.
+ destruct a; auto.
+ destruct (List.split l); auto.
  destruct a0; simpl.
  destruct a; simpl; auto.
Qed.

Lemma dotprod_finite_implies {ty} (v: list (ftype ty * ftype ty)):
  is_finite _ _ (dotprod_r (fst (List.split v)) (snd (List.split v))) = true ->
  (forall a, In a v ->
             is_finite _ _ (fst a) = true /\
             is_finite _ _ (snd a) = true).
Proof.
intros.
induction v.
+ by simpl in H0.
+ assert ((List.split (a0 :: v)).1 = (a0.1 :: (List.split v).1)).
  { apply list_split_l. }
  assert ((List.split (a0 :: v)).2 = (a0.2 :: (List.split v).2)).
  { apply list_split_r. } rewrite H1 H2 in H.
  unfold dotprod_r in H.  simpl in H.
  apply bfma_overflow_implies in H.
  destruct H0.
  - rewrite -H0. split; try apply H.
  - unfold dotprod_r in IHv.
    destruct H as [Hf1 [Hf2 Hf3]].
    specialize (IHv Hf3 H0). apply IHv. 
Qed.

Definition x_fix_FT2R {ty} {n:nat} x b (A: 'M[ftype ty]_n.+1) : 
  'cV[R]_n.+1 :=
  let r := b - ((A2_J_real (FT2R_mat A)) *m x) in
  diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A)) r.

Lemma Rabs_sum_in {n:nat} (f1 f2 : 'I_n.+1 -> R):
  \sum_j (Rabs (f1 j) * Rabs (f2 j))%Re = 
   \sum_j (Rabs (f1 j * f2 j))%Re.
Proof.
apply eq_big. by [].
intros. by rewrite Rabs_mult.
Qed.


Definition size_constraint {t} {n:nat}:=
  (INR n.+1 <
 ((fmax t - default_abs t) /
  (1 + default_rel t) -
  g1 t n.+1 (n.+1 - 1)%coq_nat - 1) /
 (g t (n.+1 - 1)%coq_nat + 1))%Re /\
 (INR n.+2 <=
 fmax t / (1 + g t n.+2) / default_abs t - 1)%Re.


Lemma g1_constraint_Sn {t} {n:nat}:
@size_constraint t n ->
(g1 t (n.+2 + 1)%coq_nat n.+2 <= fmax t)%Re.
Proof.
intro size_cons.
unfold g1.
apply Rdiv_le_right_elim.
apply Rplus_lt_le_0_compat. nra. apply g_pos.
apply Rdiv_le_right_elim.
apply default_abs_gt_0.
rewrite plus_INR. 
replace (INR 1) with 1%Re by (simpl;nra).
apply Rcomplements.Rle_minus_r.
apply size_cons.
Qed.


Lemma g1_constraint {t} {n:nat}:
  @size_constraint t n ->
  (g1 t (n.+1 + 1)%coq_nat n.+1 <= fmax t)%Re.
Proof.
intros.
apply Rle_trans with (g1 t (n.+2 + 1)%coq_nat n.+2).
+ pose proof (g1n_le_g1Sn t).
  specialize (H0 (n.+1 + 1)%coq_nat).
  assert ((1 <= (n.+1 + 1)%coq_nat)%coq_nat) by lia.
  specialize (H0 H1). 
  assert (((n.+1 + 1)%coq_nat - 1)%coq_nat = n.+1) by lia.
  rewrite H2 in H0.
  assert ((n.+1 + 1)%coq_nat.+1 = (n.+2 + 1)%coq_nat) by lia.
  rewrite H3 in H0.
  nra.
+ by apply g1_constraint_Sn.
Qed.


Definition rho_def  {t: type} {n:nat} (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in  
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel t in
  ((((1 + g t n.+1) * (1 + delta) *
                  g t n.+1 + delta * (1 + g t n.+1) +
                  g t n.+1) * (1 + delta) + delta) * R +
                (((1 + g t n.+1) * (1 + delta) *
                  g t n.+1 + delta * (1 + g t n.+1) +
                  g t n.+1) * default_abs t +
                 default_abs t) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re.


Definition d_mag_def {t: type} {n:nat} (A: 'M[ftype t]_n.+1) 
  (b: 'cV[ftype t]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in  
  let x:= mulmx (A_real^-1) b_real in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel t in
  ((g t n.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_diag A_real) *
                      (1 + delta) + default_abs t) *
                     vec_inf_norm b_real) +
                    (1 + g t n.+1) * g1 t n.+1 (n.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_diag A_real) *
                     (1 + delta) + default_abs t) +
                    g1 t n.+1 (n.+1 - 1) +
                    (vec_inf_norm (A1_diag A_real) * delta +
                     default_abs t) * vec_inf_norm b_real +
                    ((((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * (1 + delta) + delta) * R +
                     (((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * default_abs t +
                      default_abs t) *
                     matrix_inf_norm (A2_J_real A_real)) *
                    vec_inf_norm (x_fix x b_real A_real))%Re.

Lemma d_mag_ge_0 {t: type} {n:nat} (A: 'M[ftype t]_n.+1) 
  (b: 'cV[ftype t]_n.+1):
  (0 <= d_mag_def A b)%Re.
Proof.
unfold d_mag_def.
repeat apply Rplus_le_le_0_compat.
+ repeat try apply Rmult_le_pos; try repeat apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; try apply g_pos.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  - apply default_rel_ge_0.
  - apply Rmult_le_pos. 
    apply /RleP. apply vec_norm_pd.
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
    apply /RleP. apply vec_norm_pd.
+ apply g1_pos.
+ apply Rmult_le_pos; last by (apply /RleP; try apply vec_norm_pd).
  apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
  apply Rmult_le_pos; last by apply default_rel_ge_0.
  apply /RleP. apply vec_norm_pd.
+ repeat apply Rmult_le_pos; last by (apply /RleP; try apply vec_norm_pd).
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
    * apply /RleP. apply vec_norm_pd.
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
Qed.
  

Lemma x_k_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) k i:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
   (f_error k b x0 x A <=
       rho ^ k * f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) * d_mag)%Re ->
    (Rabs (FT2R (X_m_jacobi k x0 b A i ord0)) <= 
      vec_inf_norm
         (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       rho ^ k * f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) * d_mag)%Re.
Proof.
intros.
rewrite [in X in (X <= _)%Re]/f_error in H.
apply Rle_trans with 
  (vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))).
  - unfold vec_inf_norm.
    apply Rle_trans with 
     [seq Rabs
          (FT2R_mat (X_m_jacobi k x0 b A)
             i0 0)
          | i0 <- enum 'I_n.+1]`_i.
    * rewrite seq_equiv. rewrite nth_mkseq; 
      last by apply ltn_ord.
      rewrite mxE. rewrite inord_val. apply Rle_refl.
    * apply /RleP.
      apply (@bigmaxr_ler  _ 0%Re [seq Rabs
                                   (FT2R_mat (X_m_jacobi k x0 b A) i0 0)
                               | i0 <- enum 'I_n.+1] i).
      rewrite size_map size_enum_ord.
      by apply ltn_ord.
  - assert (forall x y z d: R, (x - y <= z + d)%Re -> (x <= y + z + d)%Re).
    { intros. nra. } apply H0.
    apply /RleP. apply reverse_triang_ineq.
    by apply /RleP.
Qed.

Definition input_bound {t} {n:nat} 
  (A: 'M[ftype t]_n.+1) (x0 b: 'cV[ftype t]_n.+1) k:=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  (forall i,
    (Rabs (FT2R (A i i)) *
     (rho ^ k * (1 + rho) *
      (f_error 0 b x0 x A -
       d_mag * / (1 - rho)) +
      2 * d_mag * / (1 - rho) +
      2 *
      vec_inf_norm
        (x_fix x (FT2R_mat b) (FT2R_mat A))) <
     (sqrt (fun_bnd t n.+1) - default_abs t) /
     (1 + default_rel t) /
     (1 + default_rel t))%Re) /\ 
  (vec_inf_norm
   (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       rho ^ k *
       f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) *
       d_mag < sqrt (fun_bnd t n.+1))%Re /\
  (forall i j, 
      (Rabs (FT2R (A2_J A i j )) <
        sqrt (fun_bnd t n.+1))%Re) /\
  (forall i,
     (Rabs (FT2R (b i ord0)) +
     (1 + g t n.+1) *
     ((vec_inf_norm
         (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       rho ^ k * f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) * d_mag) *
      (\sum_j
          Rabs (FT2R (A2_J A i j)))) +
     g1 t n.+1 (n.+1 - 1)%coq_nat <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t))%Re) /\
  (forall i,
    (Rabs (FT2R (A1_inv_J A (inord i) ord0)) *
     (Rabs (FT2R (b (inord i) ord0)) +
      (1 + g t n.+1) *
      ((vec_inf_norm
          (x_fix x (FT2R_mat b) (FT2R_mat A)) +
        rho ^ k * f_error 0 b x0 x A +
        (1 - rho ^ k) / (1 - rho) * d_mag) *
       (\sum_j
           Rabs (FT2R (A2_J A (inord i) j)))) +
      g1 t n.+1 (n.+1 - 1)%coq_nat) <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t) /
     (1 + default_rel t))%Re).


Definition input_bound_alt {t} {n:nat} 
  (A: 'M[ftype t]_n.+1) (x0 b: 'cV[ftype t]_n.+1):=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  (forall i,
    (Rabs (FT2R (A i i)) *
     (1 * (1 + rho) *
      (f_error 0 b x0 x A -
       d_mag * / (1 - rho)) +
      2 * d_mag * / (1 - rho) +
      2 *
      vec_inf_norm
        (x_fix x (FT2R_mat b) (FT2R_mat A))) <
     (sqrt (fun_bnd t n.+1) - default_abs t) /
     (1 + default_rel t) /
     (1 + default_rel t))%Re) /\ 
  (vec_inf_norm
   (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       1 *
       f_error 0 b x0 x A +
       1 / (1 - rho) *
       d_mag < sqrt (fun_bnd t n.+1))%Re /\
  (forall i j, 
      (Rabs (FT2R (A2_J A i j )) <
        sqrt (fun_bnd t n.+1))%Re) /\
  (forall i,
     (Rabs (FT2R (b i ord0)) +
     (1 + g t n.+1) *
     ((vec_inf_norm
         (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       1 * f_error 0 b x0 x A +
       1 / (1 - rho) * d_mag) *
      (\sum_j
          Rabs (FT2R (A2_J A i j)))) +
     g1 t n.+1 (n.+1 - 1)%coq_nat <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t))%Re) /\
  (forall i,
    (Rabs (FT2R (A1_inv_J A (inord i) ord0)) *
     (Rabs (FT2R (b (inord i) ord0)) +
      (1 + g t n.+1) *
      ((vec_inf_norm
          (x_fix x (FT2R_mat b) (FT2R_mat A)) +
        1 * f_error 0 b x0 x A +
        1 / (1 - rho) * d_mag) *
       (\sum_j
           Rabs (FT2R (A2_J A (inord i) j)))) +
      g1 t n.+1 (n.+1 - 1)%coq_nat) <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t) /
     (1 + default_rel t))%Re).




Lemma bound_1  {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  input_bound_alt A x0 b ->
  (rho < 1)%Re ->
  (0 < f_error 0 b x0 x A -
         d_mag_def A b * / (1 - rho_def A b))%Re ->
  (Rabs (FT2R (A (inord m) (inord m))) *
   (rho ^ k * (1 + rho) *
    (f_error 0 b x0 x A -
     d_mag * / (1 - rho)) +
    2 * d_mag * / (1 - rho) +
    2 *
    vec_inf_norm
      (x_fix x (FT2R_mat b) (FT2R_mat A))) <
   (sqrt (fun_bnd t n.+1) - default_abs t) /
   (1 + default_rel t) /
   (1 + default_rel t))%Re.
Proof.
intros.
unfold input_bound_alt in H.
destruct H as [bnd1 H]. clear H.
apply Rle_lt_trans with 
(Rabs (FT2R (A (inord m) (inord m))) *
        (1 * (1 + rho_def A b) *
         (f_error 0 b x0
            ((FT2R_mat A)^-1 *m 
             FT2R_mat b) A -
          d_mag_def A b *
          / (1 - rho_def A b)) +
         2 * d_mag_def A b *
         / (1 - rho_def A b) +
         2 *
         vec_inf_norm
           (x_fix
              ((FT2R_mat A)^-1 *m FT2R_mat b)
              (FT2R_mat b) (FT2R_mat A))))%Re.
+ apply Rmult_le_compat_l. apply Rabs_pos.
  unfold d_mag, rho.
  repeat apply Rplus_le_compat_r.
  apply Rmult_le_compat_r. apply Rlt_le. apply H1.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat. nra. by apply rho_ge_0.
  assert ( 1%Re = (1 ^ k)%Re) by (rewrite pow1; nra).
  rewrite H. apply pow_incr.
  split. by apply rho_ge_0.
  apply Rlt_le. apply H0.
+ apply bnd1.
Qed.


Lemma  bound_2 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) k:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  input_bound_alt A x0 b ->
  (rho < 1)%Re ->
  (vec_inf_norm
   (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       rho ^ k *
       f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) *
       d_mag < sqrt (fun_bnd ty n.+1))%Re.
Proof. 
intros.
unfold input_bound_alt in H.
destruct H as [_ [bnd2 H]]. clear H.
apply Rle_lt_trans with
(vec_inf_norm
          (x_fix
             ((FT2R_mat A)^-1 *m 
              FT2R_mat b)
             (FT2R_mat b)
             (FT2R_mat A)) +
        1 * f_error 0 b x0
          ((FT2R_mat A)^-1 *m 
           FT2R_mat b) A +
        1 / (1 - rho_def A b) * d_mag_def A b)%Re.
+ unfold x. unfold A_real, b_real. rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l. unfold rho, d_mag.
  apply Rplus_le_compat.
  - apply Rmult_le_compat_r.
    * unfold f_error. apply /RleP.
      apply vec_norm_pd.
    * assert ( 1%Re = (1 ^ k)%Re) by (rewrite pow1; nra).
      rewrite H. apply pow_incr.
      split. by apply rho_ge_0.
      apply Rlt_le. apply H0.
  - apply Rmult_le_compat_r.
    apply d_mag_ge_0. apply Rmult_le_compat_r.
    apply Rlt_le. apply Rinv_0_lt_compat.
    apply Rlt_Rminus. apply H0.
    apply Rcomplements.Rle_minus_l.
    assert (forall a b:R, (0 <= b)%Re -> (a <= a + b)%Re).
    { intros. nra. } apply H.
    apply pow_le. by apply rho_ge_0.
+ apply bnd2.
Qed.



Lemma bound_3 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1):
  input_bound_alt A x0 b ->
  forall i j, 
  (Rabs (FT2R (A2_J A i j )) <
    sqrt (fun_bnd ty n.+1))%Re.
Proof.
intros. unfold input_bound_alt in H.
destruct H as [_ [_ [bnd3 H]]]. clear H.
apply bnd3. 
Qed.


Lemma bound_4 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) k i:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  input_bound_alt A x0 b ->
  (rho < 1)%Re ->
  (Rabs (FT2R (b i ord0)) +
   (1 + g ty n.+1) *
   ((vec_inf_norm
       (x_fix x (FT2R_mat b) (FT2R_mat A)) +
     rho ^ k * f_error 0 b x0 x A +
     (1 - rho ^ k) / (1 - rho) * d_mag) *
    (\sum_j
        Rabs (FT2R (A2_J A i j)))) +
   g1 ty n.+1 (n.+1 - 1)%coq_nat <
   (bpow Zaux.radix2 (femax ty) -
    default_abs ty) / (1 + default_rel ty))%Re.
Proof.
intros. unfold input_bound_alt in H.
destruct H as [_ [_ [_ [bnd4 H]]]]. clear H.
apply Rle_lt_trans with
(Rabs (FT2R (b i ord0)) +
        (1 + g ty n.+1) *
        ((vec_inf_norm
            (x_fix
               ((FT2R_mat A)^-1 *m 
                FT2R_mat b) 
               (FT2R_mat b) 
               (FT2R_mat A)) +
          1 *
          f_error 0 b x0
            ((FT2R_mat A)^-1 *m 
             FT2R_mat b) A +
          1 / (1 - rho_def A b) *
          d_mag_def A b) *
         (\sum_j Rabs (FT2R (A2_J A i j)))) +
        g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
+ apply Rplus_le_compat_r. apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat; try nra; try apply g_pos.
  apply Rmult_le_compat_r.
  - apply /RleP. apply big_ge_0_ex_abstract.
    intros. apply /RleP. apply Rabs_pos.
  - unfold x, A_real, b_real. 
    apply Rplus_le_compat.
    * apply Rplus_le_compat_l.
      apply Rmult_le_compat_r. unfold f_error.
      apply /RleP. apply vec_norm_pd.






 admit.
+ apply bnd4.




 intros. apply H. Qed.


Lemma bound_5 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) k i:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  input_bound A x0 b k ->
  (Rabs (FT2R (A1_inv_J A (inord i) ord0)) *
   (Rabs (FT2R (b (inord i) ord0)) +
    (1 + g ty n.+1) *
    ((vec_inf_norm
        (x_fix x (FT2R_mat b) (FT2R_mat A)) +
      rho ^ k * f_error 0 b x0 x A +
      (1 - rho ^ k) / (1 - rho) * d_mag) *
     (\sum_j
         Rabs (FT2R (A2_J A (inord i) j)))) +
    g1 ty n.+1 (n.+1 - 1)%coq_nat) <
   (bpow Zaux.radix2 (femax ty) -
    default_abs ty) / (1 + default_rel ty) /
   (1 + default_rel ty))%Re.
Proof. intros. apply H. Qed.


(** State the forward error theorem **)
Theorem jacobi_forward_error_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  (forall i, is_finite _ _ (A i i) = true) ->
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
   let delta := default_rel ty in
   let rho := ((((1 + g ty n.+1) * (1 + delta) *
                  g ty n.+1 + delta * (1 + g ty n.+1) +
                  g ty n.+1) * (1 + delta) + delta) * R +
                (((1 + g ty n.+1) * (1 + delta) *
                  g ty n.+1 + delta * (1 + g ty n.+1) +
                  g ty n.+1) * default_abs ty +
                 default_abs ty) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re in
   let d_mag := ((g ty n.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_diag A_real) *
                      (1 + delta) + default_abs ty) *
                     vec_inf_norm b_real) +
                    (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_diag A_real) *
                     (1 + delta) + default_abs ty) +
                    g1 ty n.+1 (n.+1 - 1) +
                    (vec_inf_norm (A1_diag A_real) * delta +
                     default_abs ty) * vec_inf_norm b_real +
                    ((((1 + g ty n.+1) * (1 + delta) *
                       g ty n.+1 + delta * (1 + g ty n.+1) +
                       g ty n.+1) * (1 + delta) + delta) * R +
                     (((1 + g ty n.+1) * (1 + delta) *
                       g ty n.+1 + delta * (1 + g ty n.+1) +
                       g ty n.+1) * default_abs ty +
                      default_abs ty) *
                     matrix_inf_norm (A2_J_real A_real)) *
                    vec_inf_norm (x_fix x b_real A_real))%Re in
  (rho < 1)%Re ->
  A_real \in unitmx ->
  (forall i : 'I_n.+1,
    is_finite (fprec ty) (femax ty)
      (BDIV ty (Zconst ty 1) (A i i)) = true) ->
  forall x0: 'cV[ftype ty]_n.+1, 
  (forall i : 'I_n.+1, is_finite (fprec ty) (femax ty)
                              (x0 i ord0) = true) ->
  (forall i, is_finite (fprec ty) (femax ty)
                        (A1_inv_J A i ord0) = true) ->
  (forall i j, is_finite (fprec ty) (femax ty)
                  (A2_J A i j) = true) -> 
  (forall i, is_finite (fprec ty) (femax ty)
                          (b i ord0) = true) ->
  @size_constraint ty n ->
  (forall k:nat, 
   (forall i, is_finite _ _ (X_m_jacobi k x0 b A i ord0) = true) /\
   (f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + ((1 - rho^k) / (1 - rho))* d_mag)%Re).
Proof.
intro HAf. 
intros ? ? ? ? ? ? ? ? ?   Hdivf ? Hx0 Ha1_inv HfA2 Hb size_cons k.
assert (forall i : 'I_n.+1, FT2R (A i i) <> 0%Re).
{ intros. by apply BDIV_FT2R_sep_zero. }
induction k.
+ split; simpl; try nra.
  intros. apply Hx0. 
+ assert (Hfin: (forall i : 'I_n.+1,
                 is_finite (fprec ty) (femax ty)
                   (X_m_jacobi k.+1 x0 b A i ord0) =  true)).
  { intros. simpl.
    unfold jacobi_iter.
    rewrite mxE.
    rewrite nth_vec_to_list_float; last by apply ltn_ord.
    assert (is_finite (fprec ty) (femax ty)
              (let l1 :=
                 vec_to_list_float n.+1
                   (\row_j A2_J A (inord i) j)^T in
               let l2 :=
                 vec_to_list_float n.+1
                   (\col_j X_m_jacobi k x0 b A j
                             ord0) in
               dotprod_r l1 l2) = true).
    { pose proof (@finite_fma_from_bounded _ ty).
      specialize (H2 (vec_to_list_float n.+1
                         (\row_j A2_J A (inord i) j)^T)
                      ( vec_to_list_float n.+1
                          (\col_j X_m_jacobi k x0 b A j ord0))).
      rewrite combine_length !length_veclist Nat.min_id in H2.
      specialize (H2 (dotprod_r 
                            (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                            (vec_to_list_float n.+1
                                 (\col_j X_m_jacobi k x0 b A j  ord0)))).
      specialize (H2 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                          (\col_j X_m_jacobi k x0 b A j ord0))).
      assert ((g1 ty (n.+2 + 1)%coq_nat n.+2 <=  fmax ty)%Re).
      { by apply g1_constraint_Sn. } specialize (H2 H3).
      apply H2. intros.
      repeat split.
      + destruct x1. simpl. apply in_combine_l in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev (vec_to_list_float n.+1
                                 (\row_j A2_J A (inord i) j)^T)) f (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite mxE in H52. rewrite -H52. apply HfA2.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_r in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev
                                (vec_to_list_float n.+1
                                   (\col_j X_m_jacobi k x0 b A j ord0))) f0 (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite -H52. apply IHk.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_l in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev (vec_to_list_float n.+1
                                 (\row_j A2_J A (inord i) j)^T)) f (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite mxE in H52. rewrite -H52. 
          apply bound_3.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_r in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev
                                (vec_to_list_float n.+1
                                   (\col_j X_m_jacobi k x0 b A j ord0))) f0 (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite -H52.
          destruct IHk as [IHk1 IHk2]. 
          apply (x_k_bound (@inord n m)) in IHk2.
          eapply Rle_lt_trans.
          apply IHk2. apply bound_2.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
    }
    assert (is_finite (fprec ty) (femax ty)
            (BMINUS ty (b (inord i) ord0)
               ((A2_J A *f X_m_jacobi k x0 b A)
                  (inord i) ord0)) = true).
    { apply Bplus_bminus_opp_implies.
      apply BPLUS_no_overflow_is_finite.
        + apply Hb.
        + rewrite is_finite_Bopp. rewrite mxE. apply H2.
        + unfold Bplus_no_overflow. 
          pose proof (@generic_round_property ty).
          specialize (H3 (FT2R (b (inord i) ord0) +
                             FT2R
                               (BOPP ty
                                  ((A2_J A *f
                                    X_m_jacobi k x0 b A)
                                     (inord i) ord0)))%Re).
          destruct H3 as [d1 [e1 [Hde1 [Hd1 [He1 H3]]]]].
          rewrite H3.
          eapply Rle_lt_trans. apply Rabs_triang.
          eapply Rle_lt_trans. apply Rplus_le_compat_l.
          apply He1. apply Rcomplements.Rlt_minus_r.
          rewrite Rabs_mult.
          eapply Rle_lt_trans.
          apply Rmult_le_compat_l. apply Rabs_pos.
          eapply Rle_trans. apply Rabs_triang.
          rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1.
          apply Rcomplements.Rlt_div_r.
          apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
          eapply Rle_lt_trans. apply Rabs_triang.
          rewrite [in X in (_ + X < _)%Re]/FT2R B2R_Bopp Rabs_Ropp.
          fold (@FT2R ty). rewrite mxE.
          pose proof (@fma_dotprod_forward_error _ ty).
          specialize (H4 (vec_to_list_float n.+1
                                  (\row_j A2_J A (inord i) j)^T)
                         (vec_to_list_float n.+1
                            (\col_j X_m_jacobi k x0 b A j  ord0))).
          rewrite !length_veclist in H4.
          assert (n.+1 = n.+1). { lia. } specialize (H4 H5). 
          clear H5.
          specialize (H4 (dotprod_r 
                            (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                            (vec_to_list_float n.+1
                                 (\col_j X_m_jacobi k x0 b A j  ord0)))).
          specialize (H4 
                     (\sum_j ( (FT2R (A2_J A (inord i) j)) * 
                               (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
          specialize (H4
                     (\sum_j (Rabs (FT2R (A2_J A (inord i) j)) * 
                              Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
          specialize (H4 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                          (\col_j X_m_jacobi k x0 b A j ord0))).
          assert (\sum_j
                     (FT2R
                        (A2_J A (inord i) j) *
                      FT2R
                        (X_m_jacobi k x0 b
                           A j ord0))%Re = 
                  \sum_(j < n.+1)
                          FT2R_mat (A2_J A) (inord i) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                          FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
          { apply eq_big. intros. by []. intros.
            assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
            { unfold widen_ord. 
              apply val_inj. by simpl. 
            } rewrite H6. by rewrite !mxE.
          } rewrite H5 in H4.
          specialize (H4 (@R_dot_prod_rel_holds _ _  n.+1 i (leqnn n.+1) (A2_J A)
                        (\col_j X_m_jacobi k x0 b A j ord0))). 
          assert (\sum_j
                     (Rabs
                        (FT2R
                           (A2_J A 
                              (inord i) j)) *
                      Rabs
                        (FT2R
                           (X_m_jacobi k
                              x0 b A j ord0))) =  
                  sum_fold
                    (map (uncurry Rmult)
                       (map Rabsp
                          (map FR2
                             (combine
                                (vec_to_list_float n.+1
                                   (\row_j (A2_J A) (inord i) j)^T)
                                (vec_to_list_float n.+1 
                                  (\col_j X_m_jacobi k x0 b A j ord0))))))).
          { rewrite -sum_fold_mathcomp_equiv.
            apply eq_big. by []. intros.
            assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
            { unfold widen_ord. 
              apply val_inj. by simpl. 
            } rewrite H7. by rewrite !mxE.
          } rewrite H6 in H4.
          specialize (H4 (R_dot_prod_rel_abs_holds    n.+1 i (A2_J A)
                        (\col_j X_m_jacobi k x0 b A j ord0))).
          rewrite -H6 in H4. rewrite -H5 in H4. clear H5 H6.
          specialize (H4 H2). 
          eapply Rle_lt_trans. apply Rplus_le_compat_l. 
          apply Rle_trans with 
          ((1 + g ty n.+1) * 
            Rabs  (\sum_j
                      Rabs (FT2R (A2_J A (inord i) j)) *
                      Rabs (FT2R (X_m_jacobi k x0 b A j ord0))) + 
            g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
          * apply Rle_trans with 
            (Rabs ( \sum_j
                      (FT2R (A2_J A (inord i) j) *
                       FT2R(X_m_jacobi k x0 b A j ord0)))  +
              (g ty n.+1 *
                  Rabs
                    (\sum_j
                        Rabs
                          (FT2R (A2_J A (inord i) j)) *
                        Rabs
                          (FT2R
                             (X_m_jacobi k x0 b A j
                                ord0))) +
                  g1 ty n.+1 (n.+1 - 1)%coq_nat))%Re.
            rewrite Rplus_comm.
            apply Rcomplements.Rle_minus_l.
            eapply Rle_trans. apply Rabs_triang_inv.
            apply H4. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
            rewrite Rmult_plus_distr_r. apply Rplus_le_compat_r.
            rewrite Rmult_1_l. rewrite Rabs_sum_in.
            rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
            apply /RleP. apply Rabs_ineq.
          * apply Rle_refl.
          * rewrite Rabs_sum_in. rewrite sum_abs_eq; last by (intros; apply Rabs_pos).
            eapply Rle_lt_trans. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
            apply Rplus_le_compat_l.
            apply Rmult_le_compat_l.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rle_trans with 
            ((vec_inf_norm
                 (x_fix x (FT2R_mat b) (FT2R_mat A)) +
                     rho ^ k * f_error 0 b x0 x A +
                     (1 - rho ^ k) / (1 - rho) * d_mag) * 
              \sum_j (Rabs ( FT2R (A2_J A (inord i) j))))%Re.
            ++ apply /RleP. rewrite RmultE.
               rewrite big_distrr /=.
               apply big_sum_ge_ex_abstract.
               intros. rewrite -RmultE.
               rewrite Rabs_mult. rewrite Rmult_comm.
               apply Rmult_le_compat_r. apply Rabs_pos.
               apply x_k_bound. apply IHk.
            ++ apply Rle_refl.
            ++ apply bound_4.
    }
    apply BMULT_no_overflow_is_finite.
    + apply Ha1_inv.
    + rewrite nth_vec_to_list_float; last by apply ltn_ord.
      rewrite mxE. apply H3.
    + rewrite nth_vec_to_list_float; last by apply ltn_ord.
      unfold Bmult_no_overflow.
      unfold rounded.
      pose proof (@generic_round_property ty 
                  (FT2R (A1_inv_J A (inord i) ord0) *
                     FT2R
                       ((b -f
                         A2_J A *f X_m_jacobi k x0 b A)
                          (inord i) ord0))).
      destruct H4 as [d [e [Hde [Hd [He H4]]]]].
      rewrite H4. 
      eapply Rle_lt_trans.
      apply Rabs_triang. eapply Rle_lt_trans.
      apply Rplus_le_compat_l. apply He.
      apply Rcomplements.Rlt_minus_r. rewrite Rabs_mult.
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rle_trans with (Rabs 1 + Rabs d)%Re.
      apply Rabs_triang. rewrite Rabs_R1.
      apply Rplus_le_compat_l. apply Hd. 
      apply Rcomplements.Rlt_div_r.
      apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
      rewrite Rabs_mult. rewrite [in X in (_ * X < _)%Re]mxE. 
      rewrite Bminus_bplus_opp_equiv.
      pose proof (@BPLUS_accurate' _ ty).
      specialize (H5 (b (inord i) ord0) (BOPP ty
            ((A2_J A *f X_m_jacobi k x0 b A)
                          (inord i) ord0))).
      assert (is_finite (fprec ty) (femax ty)
               (BPLUS ty (b (inord i) ord0)
                  (BOPP ty
                     ((A2_J A *f
                       X_m_jacobi k x0 b A)
                        (inord i) ord0))) = true).
      { by apply Bminus_bplus_opp_implies . }
      specialize (H5 H6).
      destruct H5 as [d1 [Hd1 H5]].
      rewrite H5.
      - rewrite Rabs_mult. eapply Rle_lt_trans.
        apply Rmult_le_compat_l. apply Rabs_pos.
        apply Rmult_le_compat_l. apply Rabs_pos.
        apply Rle_trans with (Rabs 1 + Rabs d1)%Re.
        apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
        apply Hd1. rewrite -Rmult_assoc.
        apply Rcomplements.Rlt_div_r.
        apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
        eapply Rle_lt_trans. apply Rmult_le_compat_l.
        apply Rabs_pos. apply Rabs_triang.
        rewrite [in X in (_ * (_ + X) < _)%Re]/FT2R B2R_Bopp.
        rewrite Rabs_Ropp. fold (@FT2R ty).
        rewrite [in X in (_ * (_ + X) < _)%Re]mxE.
        pose proof (@fma_dotprod_forward_error _ ty).
        specialize (H7 (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                       (vec_to_list_float n.+1
                          (\col_j X_m_jacobi k x0 b A j  ord0))).
        rewrite !length_veclist in H7.
        assert (n.+1 = n.+1). { lia. } specialize (H7 H8). 
        clear H8.
        specialize (H7 (dotprod_r 
                          (vec_to_list_float n.+1
                              (\row_j A2_J A (inord i) j)^T)
                          (vec_to_list_float n.+1
                               (\col_j X_m_jacobi k x0 b A j  ord0)))).
       specialize (H7 
                   (\sum_j ( (FT2R (A2_J A (inord i) j)) * 
                             (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
      specialize (H7 
                   (\sum_j (Rabs (FT2R (A2_J A (inord i) j)) * 
                            Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
      specialize (H7 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                        (\col_j X_m_jacobi k x0 b A j ord0))).
      assert (\sum_j
                 (FT2R
                    (A2_J A (inord i) j) *
                  FT2R
                    (X_m_jacobi k x0 b
                       A j ord0))%Re = 
              \sum_(j < n.+1)
                      FT2R_mat (A2_J A) (inord i) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                      FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
      { apply eq_big. intros. by []. intros.
        assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
        { unfold widen_ord. 
          apply val_inj. by simpl. 
        } rewrite H9. by rewrite !mxE.
      } rewrite H8 in H7.
      specialize (H7 (@R_dot_prod_rel_holds _ _  n.+1 i (leqnn n.+1) (A2_J A)
                    (\col_j X_m_jacobi k x0 b A j ord0))). 
      assert (\sum_j
                 (Rabs
                    (FT2R
                       (A2_J A 
                          (inord i) j)) *
                  Rabs
                    (FT2R
                       (X_m_jacobi k
                          x0 b A j ord0))) =  
              sum_fold
                (map (uncurry Rmult)
                   (map Rabsp
                      (map FR2
                         (combine
                            (vec_to_list_float n.+1
                               (\row_j (A2_J A) (inord i) j)^T)
                            (vec_to_list_float n.+1 
                              (\col_j X_m_jacobi k x0 b A j ord0))))))).
      { rewrite -sum_fold_mathcomp_equiv.
        apply eq_big. by []. intros.
        assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
        { unfold widen_ord. 
          apply val_inj. by simpl. 
        } rewrite H10. by rewrite !mxE.
      } rewrite H9 in H7.
      specialize (H7 (R_dot_prod_rel_abs_holds    n.+1 i (A2_J A)
                    (\col_j X_m_jacobi k x0 b A j ord0))).
      rewrite -H9 in H7. rewrite -H8 in H7. clear H8 H9.
      specialize (H7 H2). 
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rplus_le_compat_l.
      apply Rle_trans with 
      ((1 + g ty n.+1) * 
        Rabs  (\sum_j
                  Rabs (FT2R (A2_J A (inord i) j)) *
                  Rabs (FT2R (X_m_jacobi k x0 b A j ord0))) + 
        g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
      * apply Rle_trans with 
        (Rabs ( \sum_j
                  (FT2R (A2_J A (inord i) j) *
                   FT2R(X_m_jacobi k x0 b A j ord0)))  +
          (g ty n.+1 *
              Rabs
                (\sum_j
                    Rabs
                      (FT2R (A2_J A (inord i) j)) *
                    Rabs
                      (FT2R
                         (X_m_jacobi k x0 b A j
                            ord0))) +
              g1 ty n.+1 (n.+1 - 1)%coq_nat))%Re.
        rewrite Rplus_comm.
        apply Rcomplements.Rle_minus_l.
        eapply Rle_trans. apply Rabs_triang_inv.
        apply H7. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
        rewrite Rmult_plus_distr_r. apply Rplus_le_compat_r.
        rewrite Rmult_1_l. rewrite Rabs_sum_in.
        rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
        apply /RleP. apply Rabs_ineq.
      * apply Rle_refl.
      * rewrite  Rabs_sum_in.
        rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
        (** This gives us information about conditions in terms of 
            conditions on input
        **)
        eapply Rle_lt_trans. apply Rmult_le_compat_l.
        apply Rabs_pos. rewrite -Rplus_assoc.
        apply Rplus_le_compat_r. apply Rplus_le_compat_l.
        apply Rmult_le_compat_l.
        apply Rplus_le_le_0_compat; try nra; try apply g_pos.
        apply Rle_trans with 
            ((vec_inf_norm
                 (x_fix x (FT2R_mat b) (FT2R_mat A)) +
                     rho ^ k * f_error 0 b x0 x A +
                     (1 - rho ^ k) / (1 - rho) * d_mag) * 
              \sum_j (Rabs ( FT2R (A2_J A (inord i) j))))%Re.
            ++ apply /RleP. rewrite RmultE.
               rewrite big_distrr /=.
               apply big_sum_ge_ex_abstract.
               intros. rewrite -RmultE.
               rewrite Rabs_mult. rewrite Rmult_comm.
               apply Rmult_le_compat_r. apply Rabs_pos.
               apply x_k_bound. apply IHk.
            ++ apply Rle_refl.
            ++ apply bound_5.
   - apply Hb.
   - rewrite is_finite_Bopp. rewrite mxE. apply H2.
   - by apply Bminus_bplus_opp_implies .
 }
  split.
  (** finiteness of x_k+1 **)
  { apply Hfin. }
  destruct IHk as [Hfx_k IHk].
  simpl.
  assert (((1 - rho * rho ^ k) / (1 - rho))%Re = 
           (rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re).
  { assert ((rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re = 
            (rho * ((1 - rho ^ k) / (1 - rho)) + (1 - rho) * / (1 - rho))%Re).
    { rewrite Rinv_r; nra. } rewrite H2. clear H2.
    assert ((rho * ((1 - rho ^ k) / (1 - rho)) +
                  (1 - rho) * / (1 - rho))%Re = 
             (( (rho * (1 - rho ^ k)) * / (1 - rho))%Re + 
              (1 - rho) * / (1 - rho))%Re).
    { nra. } rewrite H2. clear H2.
    rewrite -Rmult_plus_distr_r. nra.
  } rewrite H2. 
  rewrite Rmult_plus_distr_r.
  assert ((rho * rho ^ k * f_error 0 b x0 x A +
            (rho * ((1 - rho ^ k) / (1 - rho)) * d_mag + 1 * d_mag))%Re = 
           (rho * (rho ^ k * f_error 0 b x0 x A +
                        (1 - rho ^ k) / (1 - rho) * d_mag) + d_mag)%Re).
  { nra. } rewrite H3.
  apply Rle_trans with (rho * f_error k b x0 x A + d_mag)%Re.
  - unfold f_error. 
    assert (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                 x_fix x (FT2R_mat b) (FT2R_mat A) = 
             (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
               x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A)) +
             (x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) -
              x_fix x (FT2R_mat b) (FT2R_mat A))).
    { by rewrite add_vec_distr_2. } rewrite H4. clear H4.
    apply Rle_trans with 
    (vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                       x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) ) +
     vec_inf_norm ((x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) -
                      x_fix x (FT2R_mat b) (FT2R_mat A))))%Re.
    * apply /RleP. apply triang_ineq.
    * apply Rle_trans with 
      (vec_inf_norm
         (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
          x_fix (FT2R_mat (X_m_jacobi k x0 b A)) 
            (FT2R_mat b) (FT2R_mat A)) +
        R2 * f_error k b x0 x A)%Re.
      ++ apply Rplus_le_compat_l.
         unfold x_fix. rewrite diag_matrix_vec_mult_diff.
         rewrite add_vec_distr_4. 
         rewrite -mulmxBr.
         apply Rle_trans with
         ( vec_inf_norm (A1_diag (FT2R_mat A)) * 
           vec_inf_norm (A2_J_real (FT2R_mat A) *m (x -
                                  FT2R_mat
                                   (X_m_jacobi k x0 b A))))%Re.
         -- apply /RleP.
            apply vec_inf_norm_diag_matrix_vec_mult_R.
         -- apply Rle_trans with 
            (vec_inf_norm (A1_diag (FT2R_mat A)) * 
              (matrix_inf_norm (A2_J_real (FT2R_mat A)) *
               vec_inf_norm (x - FT2R_mat (X_m_jacobi k x0 b A))))%Re.
            ** apply Rmult_le_compat_l.
               +++ apply /RleP. apply vec_norm_pd.
               +++ apply /RleP. apply submult_prop.
            ** assert ((vec_inf_norm (A1_diag (FT2R_mat A)) *
                         (matrix_inf_norm (A2_J_real (FT2R_mat A)) *
                          vec_inf_norm (x - FT2R_mat (X_m_jacobi k x0 b A))))%Re = 
                        ((vec_inf_norm (A1_diag (FT2R_mat A)) * matrix_inf_norm (A2_J_real (FT2R_mat A))) *
                        (vec_inf_norm (x - FT2R_mat (X_m_jacobi k x0 b A))))%Re).
               { nra. } rewrite H4. unfold R2. 
               rewrite sub_vec_comm_1.
               rewrite -vec_inf_norm_opp. unfold f_error. rewrite -x_fixpoint.
               +++ apply Rle_refl.
               +++ unfold x. rewrite mulmxA.
                  assert (FT2R_mat A *m A_real^-1 = 1).
                  { fold A_real. by rewrite mulmxV . }
                  rewrite H5. by rewrite mul1mx /b_real.
               +++ intros. rewrite !mxE. apply H1.
         -- auto.
      ++ eapply Rle_trans.
         -- apply Rplus_le_compat_r.
            apply Rle_trans with 
            (vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0 b A) -  
                           x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A) +
             vec_inf_norm (x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A - 
                              x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                                  (FT2R_mat b) (FT2R_mat A)))%Re.
            ** assert ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                         x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A)) = 
                       ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -  
                           x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A) +
                        (x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A - 
                              x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                                  (FT2R_mat b) (FT2R_mat A)))).
               { by rewrite add_vec_distr_2. } rewrite H4. 
               apply /RleP. apply triang_ineq.
            ** apply Rle_refl.
         -- remember (vec_inf_norm
                       (x_fix_FT2R
                          (FT2R_mat (X_m_jacobi k x0 b A))
                          (FT2R_mat b) A -
                        x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                          (FT2R_mat b) (FT2R_mat A))) as inv_bound.
            apply Rle_trans with 
            ((vec_inf_norm 
              (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
             vec_inf_norm 
              (diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
               x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A))
                    (FT2R_mat b) A)) + 
              inv_bound + R2 * f_error k b x0 x A)%Re.
             ** repeat apply Rplus_le_compat_r.
                assert ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                            x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) A) = 
                        (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                            diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
                        (diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
                          x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) A)).
               { by rewrite add_vec_distr_2. } rewrite H4.
               apply /RleP.
               apply triang_ineq.
             ** eapply Rle_trans. apply Rplus_le_compat_r. apply Rplus_le_compat_r.
                +++ apply Rplus_le_compat.
                    --- simpl. unfold jacobi_iter. 
                        apply Rle_trans with 
                          ((vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                            vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) * g ty n.+1 +
                               g1 ty n.+1 (n.+1 - 1))%Re.
                        *** pose proof (@vec_norm_diag ty n). 
                            apply H4. intros.
                            pose proof (@In_nth (ftype ty * ftype ty)
                                           (rev (combine
                                              (vec_to_list_float n.+1 (A1_inv_J A))
                                              (vec_to_list_float n.+1 (b -f A2_J A *f X_m_jacobi k x0 b A)))) xy 
                                            (Zconst ty 1, Zconst ty 0) ).
                            rewrite -in_rev in H6. specialize (H6 H5).
                            destruct H6 as [j [Hlength Hnth]].
                            rewrite rev_nth in Hnth.
                            ++++ rewrite combine_length !length_veclist Nat.min_id in Hnth.
                                 assert ((n.+1 - j.+1)%coq_nat = (n.+1.-1 - j)%coq_nat).
                                 { lia. } rewrite H6 in Hnth. rewrite combine_nth in Hnth.
                                 rewrite !nth_vec_to_list_float in Hnth.
                                 rewrite -Hnth /=.
                                 specialize (Hfin (@inord n j)).
                                 rewrite mxE in Hfin. rewrite !nth_vec_to_list_float in Hfin.
                                 rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                 apply bmult_overflow_implies in Hfin; try apply Hfin.
                                 apply bmult_overflow_implies in Hfin; try apply Hfin.
                                 by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 by apply /ssrnat.ltP.
                                 rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 by apply /ssrnat.ltP. by rewrite !length_veclist.
                           ++++ by rewrite rev_length in Hlength.
                        *** apply Rplus_le_compat_r.
                            apply Rmult_le_compat_r.
                            apply g_pos.
                            apply Rmult_le_compat_l.
                            apply /RleP. apply vec_norm_pd.
                            assert ((vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                                  (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) <=
                                    (vec_inf_norm (FT2R_mat b) + vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                    (default_rel ty))).
                            { apply vec_float_sub. intros.
                              pose proof (@In_nth (ftype ty * ftype ty)
                                           (rev (combine
                                              (vec_to_list_float n.+1 b)
                                              (vec_to_list_float n.+1 (A2_J A *f X_m_jacobi k x0 b A)))) xy 
                                            (Zconst ty 0, Zconst ty 0) ).
                              rewrite -in_rev in H5. specialize (H5 H4).
                              destruct H5 as [j [Hlength Hnth]].
                              rewrite rev_nth in Hnth.
                              ++++ rewrite combine_length !length_veclist Nat.min_id in Hnth.
                                   assert ((n.+1 - j.+1)%coq_nat = (n.+1.-1 - j)%coq_nat).
                                   { lia. } rewrite H5 in Hnth. rewrite combine_nth in Hnth.
                                   rewrite !nth_vec_to_list_float in Hnth.
                                   rewrite -Hnth /=.
                                   specialize (Hfin (@inord n j)).
                                   rewrite mxE in Hfin. rewrite !nth_vec_to_list_float in Hfin.
                                   rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2. rewrite is_finite_Bopp in Hfin2.  try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   try apply Hfin2.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP. by rewrite !length_veclist.
                             ++++ by rewrite rev_length in Hlength.
                            } apply reverse_triang_ineq in H4.
                            apply Rle_trans with 
                            ((vec_inf_norm (FT2R_mat b) +
                                    vec_inf_norm
                                      (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                   (1 + default_rel ty))%Re.
                            ++++ rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                                 apply Rle_trans with 
                                 (vec_inf_norm
                                   (FT2R_mat b -
                                    FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)) + 
                                   (vec_inf_norm (FT2R_mat b) +
                                      vec_inf_norm
                                        (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                     default_rel ty)%Re.
                                 ---- assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                      { intros. nra. } apply H5. by apply /RleP.
                                 ---- apply Rplus_le_compat_r.
                                      assert (vec_inf_norm
                                                  (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)) = 
                                              vec_inf_norm (- (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)))).
                                      { by rewrite vec_inf_norm_opp. } rewrite H5.
                                      apply /RleP. apply triang_ineq.
                            ++++ apply Rmult_le_compat_r.
                                 ---- apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                 ---- apply Rplus_le_compat_l.
                                      assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                                      { apply matrix_vec_mult_bound_corollary. intros.
                                        specialize (Hfin (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H6. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H7 in H6. clear H7.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H7 in H6. clear H7. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H7.
                                        } rewrite H7 in H6. 
                                        specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                                        specialize (H6 H5). apply H6.
                                        by rewrite !length_veclist.


                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H6. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H7 in H6. clear H7.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H7 in H6. clear H7. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H7.
                                        } rewrite H7 in H6. 
                                        specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                                        specialize (H6 H5). apply H6.
                                        by rewrite !length_veclist.
                                        
                                        intros.
                                        specialize (Hfin (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        by rewrite mxE in Hfin22.
                                       
                                      }
                                      apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                                      **** rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                                           apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                                           +++++ apply reverse_triang_ineq in H5.
                                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                                 { intros. nra. } apply H6. apply /RleP. apply H5.
                                           +++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                                  replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                                      **** apply Rle_refl.
                    --- unfold x_fix_FT2R. rewrite diag_matrix_vec_mult_diff .
                        apply Rle_trans with
                        (vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                         vec_inf_norm (FT2R_mat
                                         (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                       (FT2R_mat b -
                                        A2_J_real (FT2R_mat A) *m 
                                        FT2R_mat (X_m_jacobi k x0 b A))))%Re.
                        *** apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R .
                        *** apply Rmult_le_compat_l.
                            ++++ apply /RleP. apply vec_norm_pd.
                            ++++ assert ((FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                          (FT2R_mat b -
                                           A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A))) =
                                         (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) - 
                                          (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) +
                                         (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) - 
                                           (FT2R_mat b -
                                           A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A)))).
                                 { by rewrite add_vec_distr_2. } rewrite H4. clear H4.
                                 apply /RleP. apply triang_ineq.
         +++ assert (FT2R_mat b -
                         FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                         (FT2R_mat b -
                          A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A))  =
                     - (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                        A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A)) ).
             { rewrite add_vec_distr_4. by rewrite sub_vec_comm_1. auto. } rewrite H4. clear H4.
             rewrite -vec_inf_norm_opp. rewrite -RplusE.
             rewrite Rmult_plus_distr_l. eapply Rle_trans.
             *** apply Rplus_le_compat_r. apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                apply Rplus_le_compat.
                ++++ apply /RleP. apply vec_float_sub.
                    intros.
                     pose proof (@In_nth (ftype ty * ftype ty)
                                           (rev (combine
                                              (vec_to_list_float n.+1 b)
                                              (vec_to_list_float n.+1 (A2_J A *f X_m_jacobi k x0 b A)))) xy 
                                            (Zconst ty 0, Zconst ty 0) ).
                              rewrite -in_rev in H5. specialize (H5 H4).
                              destruct H5 as [j [Hlength Hnth]].
                              rewrite rev_nth in Hnth.
                              ---- rewrite combine_length !length_veclist Nat.min_id in Hnth.
                                   assert ((n.+1 - j.+1)%coq_nat = (n.+1.-1 - j)%coq_nat).
                                   { lia. } rewrite H5 in Hnth. rewrite combine_nth in Hnth.
                                   rewrite !nth_vec_to_list_float in Hnth.
                                   rewrite -Hnth /=.
                                   specialize (Hfin (@inord n j)).
                                   rewrite mxE in Hfin. rewrite !nth_vec_to_list_float in Hfin.
                                   rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2. rewrite is_finite_Bopp in Hfin2.  try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   try apply Hfin2.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP. by rewrite !length_veclist.
                             ---- by rewrite rev_length in Hlength.
               ++++ assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite H4. apply /RleP. apply matrix_vec_mult_bound_corollary.
                    intros.
                    specialize (Hfin (@inord n i)). 
                    rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                    rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                    rewrite inord_val in Hfin. repeat split; try apply Hfin.
                    apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                    rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                    apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                    destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                    rewrite mxE in Hfin22.  
                    pose proof (@dotprod_finite_implies ty).
                    specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                    rewrite !combine_split  in H6. 
                    assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                    { by simpl. } rewrite H7 in H6. clear H7.
                     assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                     { by simpl. } rewrite H7 in H6. clear H7. 
                     assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                     { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                       assert (y = ord0). { by apply ord1. } by rewrite H7.
                     } rewrite H7 in H6. 
                     specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                     specialize (H6 H5). apply H6.
                     by rewrite !length_veclist.


                     apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                     rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                     apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                     destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                     rewrite mxE in Hfin22.  
                     pose proof (@dotprod_finite_implies ty).
                     specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                     rewrite !combine_split  in H6. 
                     assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                     { by simpl. } rewrite H7 in H6. clear H7.
                     assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                     { by simpl. } rewrite H7 in H6. clear H7. 
                     assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                     { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                       assert (y = ord0). { by apply ord1. } by rewrite H7.
                     } rewrite H7 in H6. 
                     specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                     specialize (H6 H5). apply H6.
                     by rewrite !length_veclist.
                                        
                     intros.
                     specialize (Hfin (@inord n i)). 
                     rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                     rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                     rewrite inord_val in Hfin. repeat split; try apply Hfin.
                     apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                     rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                     apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                     destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                     by rewrite mxE in Hfin22.
            *** eapply Rle_trans.
                ++++ apply Rplus_le_compat_r. apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                    rewrite -!RmultE -!RplusE. apply Rmult_le_compat_l.
                    --- apply /RleP. apply vec_norm_pd.
                    --- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                        apply default_rel_ge_0. 
                        apply Rplus_le_compat_l.
                        apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                        ****  rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                            assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                           { apply matrix_vec_mult_bound_corollary. intros.

                             specialize (Hfin  (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H5 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H5. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H6 in H5. clear H6.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H6 in H5. clear H6. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H6.
                                        } rewrite H6 in H5. 
                                        specialize (H5 Hfin22 xy). rewrite -H6 in H5.
                                        specialize (H5 H4). apply H5.
                                        by rewrite !length_veclist.


                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H5 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H5. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H6 in H5. clear H6.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H6 in H5. clear H6. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H6.
                                        } rewrite H6 in H5. 
                                        specialize (H5 Hfin22 xy). rewrite -H6 in H5.
                                        specialize (H5 H4). apply H5.
                                        by rewrite !length_veclist.
                                        
                                        intros.
                                        specialize (Hfin (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        by rewrite mxE in Hfin22.
                           }
                            apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                            +++++ apply reverse_triang_ineq in H4.
                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                 { intros. nra. } apply H5. apply /RleP. apply H4.
                            +++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                    replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                        **** apply Rle_refl.
               ++++ (** This is where I collect terms to get rho and dmag **)
                    assert ((vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm
                                  (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              1 +
                              (vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm
                                  (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty) * g ty n.+1 +
                             g1 ty n.+1 (n.+1 - 1) +
                             vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm
                                  (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty +
                              (matrix_inf_norm (FT2R_mat (A2_J A)) *
                               vec_inf_norm
                                 (FT2R_mat (X_m_jacobi k x0 b A)) *
                               g ty n.+1 + g1 ty n.+1 (n.+1 - 1))) +
                             inv_bound + R2 * f_error k b x0 x A)%Re = 
                          ((( (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                              default_rel ty * (1 + g ty n.+1) + g ty n.+1) *
                              (vec_inf_norm (FT2R_mat (A1_inv_J A)) * matrix_inf_norm (FT2R_mat (A2_J A)))) *
                              vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))) +
                           ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                            (vec_inf_norm (FT2R_mat (A1_inv_J A)) * vec_inf_norm (FT2R_mat b)) +
                           ( (1+ g ty n.+1) * g1 ty n.+1 (n.+1 - 1) * (1 + default_rel ty)) *
                            (vec_inf_norm (FT2R_mat (A1_inv_J A))) + g1 ty n.+1 (n.+1 - 1))) + 
                           inv_bound + R2 * f_error k b x0 x A)%Re).
                   { nra. } rewrite H4. clear H4. 
                   eapply Rle_trans.
                   apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                   --- rewrite Heqinv_bound .
                       unfold x_fix_FT2R, x_fix. rewrite diag_matrix_vec_mult_diff_r.
                       apply Rle_trans with 
                       (vec_inf_norm (FT2R_mat (A1_inv_J A) - A1_diag (FT2R_mat A)) * 
                        vec_inf_norm (FT2R_mat b -
                             A2_J_real (FT2R_mat A) *m  FT2R_mat (X_m_jacobi k x0 b A)))%Re. 
                       ****  apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
                       **** apply Rle_trans with 
                            ((vec_inf_norm (A1_diag (FT2R_mat A)) * (default_rel ty) + (default_abs ty)) *
                            (vec_inf_norm (FT2R_mat b) + matrix_inf_norm (A2_J_real (FT2R_mat A)) *
                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))))%Re.
                             ---- apply Rmult_le_compat.
                                  +++++ apply /RleP. apply vec_norm_pd.
                                  +++++ apply /RleP. apply vec_norm_pd.
                                  +++++  pose proof (@inverse_mat_norm_bound ty n A ).
                                         assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                         assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                         by specialize (H4 H5 H6).
                                  +++++  apply Rle_trans with
                                        (vec_inf_norm (FT2R_mat b) + vec_inf_norm (-(A2_J_real (FT2R_mat A) *m 
                                                                          FT2R_mat (X_m_jacobi k x0 b A))))%Re.
                                         apply /RleP. apply triang_ineq. rewrite -vec_inf_norm_opp. 
                                         apply Rplus_le_compat_l. apply /RleP. apply submult_prop.
                             ---- apply Rle_refl. 
                   --- assert ((vec_inf_norm (FT2R_mat (A1_inv_J A)) <= 
                                vec_inf_norm (A1_diag (FT2R_mat A))* (1 + default_rel ty) +
                                default_abs ty)%Re).
                       { rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                         pose proof (@inverse_mat_norm_bound ty n A ).
                         assert (forall i : 'I_n.+1,
                                  is_finite (fprec ty) (femax ty)
                                    (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                         assert (forall i : 'I_n.+1,
                                    is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                         specialize (H4 H5 H6).
                         assert ((vec_inf_norm
                                      (FT2R_mat (A1_inv_J A) -
                                       A1_diag A_real) <=
                                    vec_inf_norm (A1_diag A_real) *
                                    default_rel ty + default_abs ty)). { by apply /RleP. }
                         apply reverse_triang_ineq in H7.
                         assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                         { intros. nra. } apply H8. by apply /RleP.
                       } eapply Rle_trans.
                       **** apply Rplus_le_compat_r.
                            apply Rplus_le_compat.
                            ---- apply Rplus_le_compat.
                                 +++++ apply Rmult_le_compat_r.
                                       ----- apply /RleP. apply vec_norm_pd.
                                       ----- apply Rmult_le_compat_l.
                                             ***** apply Rplus_le_le_0_compat; last by apply g_pos.
                                                   apply Rplus_le_le_0_compat.
                                                   repeat apply Rmult_le_pos.
                                                   apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                                                   apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
                                                   apply g_pos. apply Rmult_le_pos.
                                                   apply default_rel_ge_0. apply Rplus_le_le_0_compat.
                                                   nra. apply g_pos.
                                             ***** apply Rmult_le_compat_r. apply /RleP. apply matrix_norm_pd.
                                                   pose proof (@inverse_mat_norm_bound ty n A ).
                                                   assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                                   assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                                   specialize (H5 H6 H7).
                                                   assert ((vec_inf_norm
                                                                (FT2R_mat (A1_inv_J A) -
                                                                 A1_diag A_real) <=
                                                              vec_inf_norm (A1_diag A_real) *
                                                              default_rel ty + default_abs ty)). { by apply /RleP. }
                                                   apply reverse_triang_ineq in H8.
                                                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                                                   { intros. nra. } 
                                                   apply Rle_trans with 
                                                   (vec_inf_norm (A1_diag A_real) * (1+ default_rel ty) + default_abs ty)%Re.
                                                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.  apply H9. by apply /RleP.
                                                   apply Rle_refl.
                                  +++++ apply Rplus_le_compat_r. apply Rplus_le_compat.
                                         ----- apply Rmult_le_compat_l. apply Rplus_le_le_0_compat.
                                               apply Rmult_le_pos. apply g_pos. apply Rplus_le_le_0_compat; try nra.
                                               apply default_rel_ge_0. apply default_rel_ge_0.
                                               apply Rmult_le_compat_r. apply /RleP. apply vec_norm_pd.
                                               pose proof (@inverse_mat_norm_bound ty n A ).
                                                   assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                                   assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                                   specialize (H5 H6 H7).
                                                   assert ((vec_inf_norm
                                                                (FT2R_mat (A1_inv_J A) -
                                                                 A1_diag A_real) <=
                                                              vec_inf_norm (A1_diag A_real) *
                                                              default_rel ty + default_abs ty)). { by apply /RleP. }
                                                   apply reverse_triang_ineq in H8.
                                                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                                                   { intros. nra. }
                                                   apply Rle_trans with 
                                                   (vec_inf_norm (A1_diag A_real) * (1+ default_rel ty) + default_abs ty)%Re.
                                                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.  apply H9. by apply /RleP.
                                                   apply Rle_refl.
                                         ----- apply Rmult_le_compat_l.
                                               apply Rmult_le_pos. apply Rmult_le_pos; try apply g1_pos.  
                                               apply Rplus_le_le_0_compat. nra. apply g_pos.
                                               apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
                                               pose proof (@inverse_mat_norm_bound ty n A ).
                                                   assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                                   assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                                   specialize (H5 H6 H7).
                                                   assert ((vec_inf_norm
                                                                (FT2R_mat (A1_inv_J A) -
                                                                 A1_diag A_real) <=
                                                              vec_inf_norm (A1_diag A_real) *
                                                              default_rel ty + default_abs ty)). { by apply /RleP. }
                                                   apply reverse_triang_ineq in H8.
                                                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                                                   { intros. nra. }
                                                   apply Rle_trans with 
                                                   (vec_inf_norm (A1_diag A_real) * (1+ default_rel ty) + default_abs ty)%Re.
                                                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.  apply H9. by apply /RleP.
                                                   apply Rle_refl.
                             ---- apply Rle_refl.
                       **** assert ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                      g ty n.+1 +
                                      default_rel ty * (1 + g ty n.+1) +
                                      g ty n.+1) *
                                     ((vec_inf_norm (A1_diag A_real) *
                                       (1 + default_rel ty) + default_abs ty) *
                                      matrix_inf_norm (FT2R_mat (A2_J A))) *
                                     vec_inf_norm
                                       (FT2R_mat (X_m_jacobi k x0 b A)) +
                                     ((g ty n.+1 * (1 + default_rel ty) +
                                       default_rel ty) *
                                      ((vec_inf_norm (A1_diag A_real) *
                                        (1 + default_rel ty) + default_abs ty) *
                                       vec_inf_norm (FT2R_mat b)) +
                                      (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                      (1 + default_rel ty) *
                                      (vec_inf_norm (A1_diag A_real) *
                                       (1 + default_rel ty) + default_abs ty) +
                                      g1 ty n.+1 (n.+1 - 1)) +
                                     (vec_inf_norm (A1_diag (FT2R_mat A)) *
                                      default_rel ty + default_abs ty) *
                                     (vec_inf_norm (FT2R_mat b) +
                                      matrix_inf_norm (A2_J_real (FT2R_mat A)) *
                                      vec_inf_norm
                                        (FT2R_mat (X_m_jacobi k x0 b A))) +
                                     R2 * f_error k b x0 x A)%Re = 
                                     ( ((( ( ((1 + g ty n.+1) * (1 + default_rel ty) *
                                          g ty n.+1 + default_rel ty * (1 + g ty n.+1) +
                                          g ty n.+1) * (1 + default_rel ty) + default_rel ty ) *
                                        (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (FT2R_mat (A2_J A)))) +
                                         ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                          g ty n.+1 + default_rel ty * (1 + g ty n.+1) +
                                          g ty n.+1 ) * default_abs ty) + default_abs ty) * matrix_inf_norm (FT2R_mat (A2_J A))) *
                                        vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) ) +
                                        (((g ty n.+1 * (1 + default_rel ty) +
                                             default_rel ty) *
                                            ((vec_inf_norm (A1_diag A_real) *
                                              (1 + default_rel ty) + default_abs ty) *
                                             vec_inf_norm (FT2R_mat b)) +
                                            (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                            (1 + default_rel ty) *
                                            (vec_inf_norm (A1_diag A_real) *
                                             (1 + default_rel ty) + default_abs ty) +
                                            g1 ty n.+1 (n.+1 - 1)) +
                                            (vec_inf_norm (A1_diag (FT2R_mat A)) *
                                                    default_rel ty + default_abs ty) * vec_inf_norm (FT2R_mat b)) +
                                        R2 * f_error k b x0 x A )%Re).
                                 { assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                                       by case: (x1 == y :> nat).
                                    } rewrite -!H5. fold A_real. nra.
                                 } rewrite H5. clear H5. 
                    assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite -H5. fold A_real. fold R2. fold R2. fold b_real. 
                    assert ((vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) <= 
                             f_error k b x0 x A + 
                             vec_inf_norm (x_fix x b_real A_real))%Re).
                    { unfold f_error.
                      apply Rle_trans with 
                      (vec_inf_norm ((FT2R_mat (X_m_jacobi k x0 b A) -
                                        x_fix x (FT2R_mat b) (FT2R_mat A)) + 
                                      x_fix x b_real A_real)).
                      + rewrite sub_vec_3. apply Rle_refl.
                      + apply /RleP. apply triang_ineq.
                    } 
                    apply Rle_trans with
                    (((((1 + g ty n.+1) * (1 + default_rel ty) *
                          g ty n.+1 +
                          default_rel ty * (1 + g ty n.+1) +
                          g ty n.+1) * (1 + default_rel ty) +
                         default_rel ty) * R2 +
                        (((1 + g ty n.+1) * (1 + default_rel ty) *
                          g ty n.+1 +
                          default_rel ty * (1 + g ty n.+1) +
                          g ty n.+1) * default_abs ty +
                         default_abs ty) *
                        matrix_inf_norm (A2_J_real A_real)) *
                       (f_error k b x0 x A +
                            vec_inf_norm (x_fix x b_real A_real)) +
                       ((g ty n.+1 * (1 + default_rel ty) +
                         default_rel ty) *
                        ((vec_inf_norm (A1_diag A_real) *
                          (1 + default_rel ty) + default_abs ty) *
                         vec_inf_norm b_real) +
                        (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                        (1 + default_rel ty) *
                        (vec_inf_norm (A1_diag A_real) *
                         (1 + default_rel ty) + default_abs ty) +
                        g1 ty n.+1 (n.+1 - 1) +
                        (vec_inf_norm (A1_diag A_real) *
                         default_rel ty + default_abs ty) *
                        vec_inf_norm b_real) +
                       R2 * f_error k b x0 x A )%Re.
                    ---- repeat apply Rplus_le_compat_r.
                        repeat apply Rmult_le_compat_l.
                        ***** apply Rplus_le_le_0_compat.
                              apply Rmult_le_pos.
                              repeat apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
                              repeat apply Rmult_le_pos.
                              +++++ apply Rplus_le_le_0_compat; try apply g_pos.
                                    apply Rplus_le_le_0_compat.
                                    repeat apply Rmult_le_pos.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                                    apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                    apply g_pos. apply Rmult_le_pos. apply default_rel_ge_0.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                              +++++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                              +++++ unfold R2. apply Rmult_le_pos.
                                     ----- apply /RleP. apply vec_norm_pd.
                                     ----- apply /RleP. apply matrix_norm_pd.
                              +++++ apply Rmult_le_pos; last by (apply /RleP;apply matrix_norm_pd).
                                    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
                                    apply Rmult_le_pos; last by apply default_abs_ge_0.
                                    apply Rplus_le_le_0_compat; last by apply g_pos.
                                    apply Rplus_le_le_0_compat.
                                    repeat apply Rmult_le_pos.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                                    apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                    apply g_pos.
                                    apply Rmult_le_pos. apply default_rel_ge_0.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                        ***** apply H6.
                    ---- assert ( (((((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * (1 + default_rel ty) +
                                   default_rel ty) * R2 +
                                  (((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * default_abs ty +
                                   default_abs ty) *
                                  matrix_inf_norm (A2_J_real A_real)) *
                                 (f_error k b x0 x A +
                                  vec_inf_norm (x_fix x b_real A_real)) +
                                 ((g ty n.+1 * (1 + default_rel ty) +
                                   default_rel ty) *
                                  ((vec_inf_norm (A1_diag A_real) *
                                    (1 + default_rel ty) + default_abs ty) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   (1 + default_rel ty) + default_abs ty) +
                                  g1 ty n.+1 (n.+1 - 1) +
                                  (vec_inf_norm (A1_diag A_real) *
                                   default_rel ty + default_abs ty) *
                                  vec_inf_norm b_real) +
                                 R2 * f_error k b x0 x A)%Re = 
                                ((( ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * (1 + default_rel ty) +
                                   default_rel ty) * R2 +
                                  (((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * default_abs ty +
                                   default_abs ty) *
                                  matrix_inf_norm (A2_J_real A_real)) + R2) *
                                  f_error k b x0 x A) + 
                                (((g ty n.+1 * (1 + default_rel ty) +
                                   default_rel ty) *
                                  ((vec_inf_norm (A1_diag A_real) *
                                    (1 + default_rel ty) + default_abs ty) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   (1 + default_rel ty) + default_abs ty) +
                                  g1 ty n.+1 (n.+1 - 1) +
                                  (vec_inf_norm (A1_diag A_real) *
                                   default_rel ty + default_abs ty) *
                                  vec_inf_norm b_real) + 
                                  ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * (1 + default_rel ty) +
                                   default_rel ty) * R2 +
                                  (((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * default_abs ty +
                                   default_abs ty) *
                                  matrix_inf_norm (A2_J_real A_real)) * 
                                  vec_inf_norm (x_fix x b_real A_real)))%Re).
                              { nra. }  rewrite H7. clear H7. fold delta. fold rho. fold d_mag.
                              unfold f_error. fold b_real. fold A_real. apply Rle_refl.
 - apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * by apply rho_ge_0.
    * nra.
Admitted.
 
End WITHNANS.























(** State the forward error theorem **)
Theorem jacobi_forward_error_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  (forall i, is_finite _ _ (A i i) = true) ->
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
   let delta := default_rel ty in
   let rho := ((((1 + g ty n.+1) * (1 + delta) *
                  g ty n.+1 + delta * (1 + g ty n.+1) +
                  g ty n.+1) * (1 + delta) + delta) * R +
                (((1 + g ty n.+1) * (1 + delta) *
                  g ty n.+1 + delta * (1 + g ty n.+1) +
                  g ty n.+1) * default_abs ty +
                 default_abs ty) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re in
   let d_mag := ((g ty n.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_diag A_real) *
                      (1 + delta) + default_abs ty) *
                     vec_inf_norm b_real) +
                    (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_diag A_real) *
                     (1 + delta) + default_abs ty) +
                    g1 ty n.+1 (n.+1 - 1) +
                    (vec_inf_norm (A1_diag A_real) * delta +
                     default_abs ty) * vec_inf_norm b_real +
                    ((((1 + g ty n.+1) * (1 + delta) *
                       g ty n.+1 + delta * (1 + g ty n.+1) +
                       g ty n.+1) * (1 + delta) + delta) * R +
                     (((1 + g ty n.+1) * (1 + delta) *
                       g ty n.+1 + delta * (1 + g ty n.+1) +
                       g ty n.+1) * default_abs ty +
                      default_abs ty) *
                     matrix_inf_norm (A2_J_real A_real)) *
                    vec_inf_norm (x_fix x b_real A_real))%Re in
  (rho < 1)%Re ->
  A_real \in unitmx ->
  (forall i : 'I_n.+1,
    is_finite (fprec ty) (femax ty)
      (BDIV ty (Zconst ty 1) (A i i)) = true) ->
  forall x0: 'cV[ftype ty]_n.+1, 
  (forall i : 'I_n.+1, is_finite (fprec ty) (femax ty)
                              (x0 i ord0) = true) ->
  (forall i, is_finite (fprec ty) (femax ty)
                        (A1_inv_J A i ord0) = true) ->
  (forall i j, is_finite (fprec ty) (femax ty)
                  (A2_J A i j) = true) -> 
  (forall i, is_finite (fprec ty) (femax ty)
                          (b i ord0) = true) ->
  @size_constraint ty n ->
  (forall k:nat, 
   (forall i, is_finite _ _ (X_m_jacobi k x0 b A i ord0) = true) /\
   (f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + ((1 - rho^k) / (1 - rho))* d_mag)%Re).
Proof.
intro HAf. 
intros ? ? ? ? ? ? ? ? ?   Hdivf ? Hx0 Ha1_inv HfA2 Hb size_cons k.
assert (forall i : 'I_n.+1, FT2R (A i i) <> 0%Re).
{ intros. by apply BDIV_FT2R_sep_zero. }
induction k.
+ split; simpl; try nra.
  intros. apply Hx0. 
+ assert (Hfin: (forall i : 'I_n.+1,
                 is_finite (fprec ty) (femax ty)
                   (X_m_jacobi k.+1 x0 b A i ord0) =  true)).
  { intros. simpl.
    unfold jacobi_iter.
    rewrite mxE.
    rewrite nth_vec_to_list_float; last by apply ltn_ord.
    assert (is_finite (fprec ty) (femax ty)
              (let l1 :=
                 vec_to_list_float n.+1
                   (\row_j A2_J A (inord i) j)^T in
               let l2 :=
                 vec_to_list_float n.+1
                   (\col_j X_m_jacobi k x0 b A j
                             ord0) in
               dotprod_r l1 l2) = true).
    { pose proof (@finite_fma_from_bounded _ ty).
      specialize (H2 (vec_to_list_float n.+1
                         (\row_j A2_J A (inord i) j)^T)
                      ( vec_to_list_float n.+1
                          (\col_j X_m_jacobi k x0 b A j ord0))).
      rewrite combine_length !length_veclist Nat.min_id in H2.
      specialize (H2 (dotprod_r 
                            (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                            (vec_to_list_float n.+1
                                 (\col_j X_m_jacobi k x0 b A j  ord0)))).
      specialize (H2 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                          (\col_j X_m_jacobi k x0 b A j ord0))).
      assert ((g1 ty (n.+2 + 1)%coq_nat n.+2 <=  fmax ty)%Re).
      { by apply g1_constraint_Sn. } specialize (H2 H3).
      apply H2. intros.
      repeat split.
      + destruct x1. simpl. apply in_combine_l in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev (vec_to_list_float n.+1
                                 (\row_j A2_J A (inord i) j)^T)) f (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite mxE in H52. rewrite -H52. apply HfA2.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_r in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev
                                (vec_to_list_float n.+1
                                   (\col_j X_m_jacobi k x0 b A j ord0))) f0 (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite -H52. apply IHk.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_l in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev (vec_to_list_float n.+1
                                 (\row_j A2_J A (inord i) j)^T)) f (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite mxE in H52. rewrite -H52. 
          apply bound_3.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_r in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev
                                (vec_to_list_float n.+1
                                   (\col_j X_m_jacobi k x0 b A j ord0))) f0 (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite -H52.
          destruct IHk as [IHk1 IHk2]. 
          apply (x_k_bound (@inord n m)) in IHk2.
          eapply Rle_lt_trans.
          apply IHk2. apply bound_2.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
    }
    assert (is_finite (fprec ty) (femax ty)
            (BMINUS ty (b (inord i) ord0)
               ((A2_J A *f X_m_jacobi k x0 b A)
                  (inord i) ord0)) = true).
    { apply Bplus_bminus_opp_implies.
      apply BPLUS_no_overflow_is_finite.
        + apply Hb.
        + rewrite is_finite_Bopp. rewrite mxE. apply H2.
        + unfold Bplus_no_overflow. 
          pose proof (@generic_round_property ty).
          specialize (H3 (FT2R (b (inord i) ord0) +
                             FT2R
                               (BOPP ty
                                  ((A2_J A *f
                                    X_m_jacobi k x0 b A)
                                     (inord i) ord0)))%Re).
          destruct H3 as [d1 [e1 [Hde1 [Hd1 [He1 H3]]]]].
          rewrite H3.
          eapply Rle_lt_trans. apply Rabs_triang.
          eapply Rle_lt_trans. apply Rplus_le_compat_l.
          apply He1. apply Rcomplements.Rlt_minus_r.
          rewrite Rabs_mult.
          eapply Rle_lt_trans.
          apply Rmult_le_compat_l. apply Rabs_pos.
          eapply Rle_trans. apply Rabs_triang.
          rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1.
          apply Rcomplements.Rlt_div_r.
          apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
          eapply Rle_lt_trans. apply Rabs_triang.
          rewrite [in X in (_ + X < _)%Re]/FT2R B2R_Bopp Rabs_Ropp.
          fold (@FT2R ty). rewrite mxE.
          pose proof (@fma_dotprod_forward_error _ ty).
          specialize (H4 (vec_to_list_float n.+1
                                  (\row_j A2_J A (inord i) j)^T)
                         (vec_to_list_float n.+1
                            (\col_j X_m_jacobi k x0 b A j  ord0))).
          rewrite !length_veclist in H4.
          assert (n.+1 = n.+1). { lia. } specialize (H4 H5). 
          clear H5.
          specialize (H4 (dotprod_r 
                            (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                            (vec_to_list_float n.+1
                                 (\col_j X_m_jacobi k x0 b A j  ord0)))).
          specialize (H4 
                     (\sum_j ( (FT2R (A2_J A (inord i) j)) * 
                               (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
          specialize (H4
                     (\sum_j (Rabs (FT2R (A2_J A (inord i) j)) * 
                              Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
          specialize (H4 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                          (\col_j X_m_jacobi k x0 b A j ord0))).
          assert (\sum_j
                     (FT2R
                        (A2_J A (inord i) j) *
                      FT2R
                        (X_m_jacobi k x0 b
                           A j ord0))%Re = 
                  \sum_(j < n.+1)
                          FT2R_mat (A2_J A) (inord i) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                          FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
          { apply eq_big. intros. by []. intros.
            assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
            { unfold widen_ord. 
              apply val_inj. by simpl. 
            } rewrite H6. by rewrite !mxE.
          } rewrite H5 in H4.
          specialize (H4 (@R_dot_prod_rel_holds _ _  n.+1 i (leqnn n.+1) (A2_J A)
                        (\col_j X_m_jacobi k x0 b A j ord0))). 
          assert (\sum_j
                     (Rabs
                        (FT2R
                           (A2_J A 
                              (inord i) j)) *
                      Rabs
                        (FT2R
                           (X_m_jacobi k
                              x0 b A j ord0))) =  
                  sum_fold
                    (map (uncurry Rmult)
                       (map Rabsp
                          (map FR2
                             (combine
                                (vec_to_list_float n.+1
                                   (\row_j (A2_J A) (inord i) j)^T)
                                (vec_to_list_float n.+1 
                                  (\col_j X_m_jacobi k x0 b A j ord0))))))).
          { rewrite -sum_fold_mathcomp_equiv.
            apply eq_big. by []. intros.
            assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
            { unfold widen_ord. 
              apply val_inj. by simpl. 
            } rewrite H7. by rewrite !mxE.
          } rewrite H6 in H4.
          specialize (H4 (R_dot_prod_rel_abs_holds    n.+1 i (A2_J A)
                        (\col_j X_m_jacobi k x0 b A j ord0))).
          rewrite -H6 in H4. rewrite -H5 in H4. clear H5 H6.
          specialize (H4 H2). 
          eapply Rle_lt_trans. apply Rplus_le_compat_l. 
          apply Rle_trans with 
          ((1 + g ty n.+1) * 
            Rabs  (\sum_j
                      Rabs (FT2R (A2_J A (inord i) j)) *
                      Rabs (FT2R (X_m_jacobi k x0 b A j ord0))) + 
            g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
          * apply Rle_trans with 
            (Rabs ( \sum_j
                      (FT2R (A2_J A (inord i) j) *
                       FT2R(X_m_jacobi k x0 b A j ord0)))  +
              (g ty n.+1 *
                  Rabs
                    (\sum_j
                        Rabs
                          (FT2R (A2_J A (inord i) j)) *
                        Rabs
                          (FT2R
                             (X_m_jacobi k x0 b A j
                                ord0))) +
                  g1 ty n.+1 (n.+1 - 1)%coq_nat))%Re.
            rewrite Rplus_comm.
            apply Rcomplements.Rle_minus_l.
            eapply Rle_trans. apply Rabs_triang_inv.
            apply H4. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
            rewrite Rmult_plus_distr_r. apply Rplus_le_compat_r.
            rewrite Rmult_1_l. rewrite Rabs_sum_in.
            rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
            apply /RleP. apply Rabs_ineq.
          * apply Rle_refl.
          * rewrite Rabs_sum_in. rewrite sum_abs_eq; last by (intros; apply Rabs_pos).
            eapply Rle_lt_trans. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
            apply Rplus_le_compat_l.
            apply Rmult_le_compat_l.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rle_trans with 
            ((vec_inf_norm
                 (x_fix x (FT2R_mat b) (FT2R_mat A)) +
                     rho ^ k * f_error 0 b x0 x A +
                     (1 - rho ^ k) / (1 - rho) * d_mag) * 
              \sum_j (Rabs ( FT2R (A2_J A (inord i) j))))%Re.
            ++ apply /RleP. rewrite RmultE.
               rewrite big_distrr /=.
               apply big_sum_ge_ex_abstract.
               intros. rewrite -RmultE.
               rewrite Rabs_mult. rewrite Rmult_comm.
               apply Rmult_le_compat_r. apply Rabs_pos.
               apply x_k_bound. apply IHk.
            ++ apply Rle_refl.
            ++ apply bound_4.
    }
    apply BMULT_no_overflow_is_finite.
    + apply Ha1_inv.
    + rewrite nth_vec_to_list_float; last by apply ltn_ord.
      rewrite mxE. apply H3.
    + rewrite nth_vec_to_list_float; last by apply ltn_ord.
      unfold Bmult_no_overflow.
      unfold rounded.
      pose proof (@generic_round_property ty 
                  (FT2R (A1_inv_J A (inord i) ord0) *
                     FT2R
                       ((b -f
                         A2_J A *f X_m_jacobi k x0 b A)
                          (inord i) ord0))).
      destruct H4 as [d [e [Hde [Hd [He H4]]]]].
      rewrite H4. 
      eapply Rle_lt_trans.
      apply Rabs_triang. eapply Rle_lt_trans.
      apply Rplus_le_compat_l. apply He.
      apply Rcomplements.Rlt_minus_r. rewrite Rabs_mult.
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rle_trans with (Rabs 1 + Rabs d)%Re.
      apply Rabs_triang. rewrite Rabs_R1.
      apply Rplus_le_compat_l. apply Hd. 
      apply Rcomplements.Rlt_div_r.
      apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
      rewrite Rabs_mult. rewrite [in X in (_ * X < _)%Re]mxE. 
      rewrite Bminus_bplus_opp_equiv.
      pose proof (@BPLUS_accurate' _ ty).
      specialize (H5 (b (inord i) ord0) (BOPP ty
            ((A2_J A *f X_m_jacobi k x0 b A)
                          (inord i) ord0))).
      assert (is_finite (fprec ty) (femax ty)
               (BPLUS ty (b (inord i) ord0)
                  (BOPP ty
                     ((A2_J A *f
                       X_m_jacobi k x0 b A)
                        (inord i) ord0))) = true).
      { by apply Bminus_bplus_opp_implies . }
      specialize (H5 H6).
      destruct H5 as [d1 [Hd1 H5]].
      rewrite H5.
      - rewrite Rabs_mult. eapply Rle_lt_trans.
        apply Rmult_le_compat_l. apply Rabs_pos.
        apply Rmult_le_compat_l. apply Rabs_pos.
        apply Rle_trans with (Rabs 1 + Rabs d1)%Re.
        apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
        apply Hd1. rewrite -Rmult_assoc.
        apply Rcomplements.Rlt_div_r.
        apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
        eapply Rle_lt_trans. apply Rmult_le_compat_l.
        apply Rabs_pos. apply Rabs_triang.
        rewrite [in X in (_ * (_ + X) < _)%Re]/FT2R B2R_Bopp.
        rewrite Rabs_Ropp. fold (@FT2R ty).
        rewrite [in X in (_ * (_ + X) < _)%Re]mxE.
        pose proof (@fma_dotprod_forward_error _ ty).
        specialize (H7 (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                       (vec_to_list_float n.+1
                          (\col_j X_m_jacobi k x0 b A j  ord0))).
        rewrite !length_veclist in H7.
        assert (n.+1 = n.+1). { lia. } specialize (H7 H8). 
        clear H8.
        specialize (H7 (dotprod_r 
                          (vec_to_list_float n.+1
                              (\row_j A2_J A (inord i) j)^T)
                          (vec_to_list_float n.+1
                               (\col_j X_m_jacobi k x0 b A j  ord0)))).
       specialize (H7 
                   (\sum_j ( (FT2R (A2_J A (inord i) j)) * 
                             (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
      specialize (H7 
                   (\sum_j (Rabs (FT2R (A2_J A (inord i) j)) * 
                            Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
      specialize (H7 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                        (\col_j X_m_jacobi k x0 b A j ord0))).
      assert (\sum_j
                 (FT2R
                    (A2_J A (inord i) j) *
                  FT2R
                    (X_m_jacobi k x0 b
                       A j ord0))%Re = 
              \sum_(j < n.+1)
                      FT2R_mat (A2_J A) (inord i) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                      FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
      { apply eq_big. intros. by []. intros.
        assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
        { unfold widen_ord. 
          apply val_inj. by simpl. 
        } rewrite H9. by rewrite !mxE.
      } rewrite H8 in H7.
      specialize (H7 (@R_dot_prod_rel_holds _ _  n.+1 i (leqnn n.+1) (A2_J A)
                    (\col_j X_m_jacobi k x0 b A j ord0))). 
      assert (\sum_j
                 (Rabs
                    (FT2R
                       (A2_J A 
                          (inord i) j)) *
                  Rabs
                    (FT2R
                       (X_m_jacobi k
                          x0 b A j ord0))) =  
              sum_fold
                (map (uncurry Rmult)
                   (map Rabsp
                      (map FR2
                         (combine
                            (vec_to_list_float n.+1
                               (\row_j (A2_J A) (inord i) j)^T)
                            (vec_to_list_float n.+1 
                              (\col_j X_m_jacobi k x0 b A j ord0))))))).
      { rewrite -sum_fold_mathcomp_equiv.
        apply eq_big. by []. intros.
        assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
        { unfold widen_ord. 
          apply val_inj. by simpl. 
        } rewrite H10. by rewrite !mxE.
      } rewrite H9 in H7.
      specialize (H7 (R_dot_prod_rel_abs_holds    n.+1 i (A2_J A)
                    (\col_j X_m_jacobi k x0 b A j ord0))).
      rewrite -H9 in H7. rewrite -H8 in H7. clear H8 H9.
      specialize (H7 H2). 
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rplus_le_compat_l.
      apply Rle_trans with 
      ((1 + g ty n.+1) * 
        Rabs  (\sum_j
                  Rabs (FT2R (A2_J A (inord i) j)) *
                  Rabs (FT2R (X_m_jacobi k x0 b A j ord0))) + 
        g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
      * apply Rle_trans with 
        (Rabs ( \sum_j
                  (FT2R (A2_J A (inord i) j) *
                   FT2R(X_m_jacobi k x0 b A j ord0)))  +
          (g ty n.+1 *
              Rabs
                (\sum_j
                    Rabs
                      (FT2R (A2_J A (inord i) j)) *
                    Rabs
                      (FT2R
                         (X_m_jacobi k x0 b A j
                            ord0))) +
              g1 ty n.+1 (n.+1 - 1)%coq_nat))%Re.
        rewrite Rplus_comm.
        apply Rcomplements.Rle_minus_l.
        eapply Rle_trans. apply Rabs_triang_inv.
        apply H7. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
        rewrite Rmult_plus_distr_r. apply Rplus_le_compat_r.
        rewrite Rmult_1_l. rewrite Rabs_sum_in.
        rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
        apply /RleP. apply Rabs_ineq.
      * apply Rle_refl.
      * rewrite  Rabs_sum_in.
        rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
        (** This gives us information about conditions in terms of 
            conditions on input
        **)
        eapply Rle_lt_trans. apply Rmult_le_compat_l.
        apply Rabs_pos. rewrite -Rplus_assoc.
        apply Rplus_le_compat_r. apply Rplus_le_compat_l.
        apply Rmult_le_compat_l.
        apply Rplus_le_le_0_compat; try nra; try apply g_pos.
        apply Rle_trans with 
            ((vec_inf_norm
                 (x_fix x (FT2R_mat b) (FT2R_mat A)) +
                     rho ^ k * f_error 0 b x0 x A +
                     (1 - rho ^ k) / (1 - rho) * d_mag) * 
              \sum_j (Rabs ( FT2R (A2_J A (inord i) j))))%Re.
            ++ apply /RleP. rewrite RmultE.
               rewrite big_distrr /=.
               apply big_sum_ge_ex_abstract.
               intros. rewrite -RmultE.
               rewrite Rabs_mult. rewrite Rmult_comm.
               apply Rmult_le_compat_r. apply Rabs_pos.
               apply x_k_bound. apply IHk.
            ++ apply Rle_refl.
            ++ apply bound_5.
   - apply Hb.
   - rewrite is_finite_Bopp. rewrite mxE. apply H2.
   - by apply Bminus_bplus_opp_implies .
 }
  split.
  (** finiteness of x_k+1 **)
  { apply Hfin. }
  destruct IHk as [Hfx_k IHk].
  simpl.
  assert (((1 - rho * rho ^ k) / (1 - rho))%Re = 
           (rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re).
  { assert ((rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re = 
            (rho * ((1 - rho ^ k) / (1 - rho)) + (1 - rho) * / (1 - rho))%Re).
    { rewrite Rinv_r; nra. } rewrite H2. clear H2.
    assert ((rho * ((1 - rho ^ k) / (1 - rho)) +
                  (1 - rho) * / (1 - rho))%Re = 
             (( (rho * (1 - rho ^ k)) * / (1 - rho))%Re + 
              (1 - rho) * / (1 - rho))%Re).
    { nra. } rewrite H2. clear H2.
    rewrite -Rmult_plus_distr_r. nra.
  } rewrite H2. 
  rewrite Rmult_plus_distr_r.
  assert ((rho * rho ^ k * f_error 0 b x0 x A +
            (rho * ((1 - rho ^ k) / (1 - rho)) * d_mag + 1 * d_mag))%Re = 
           (rho * (rho ^ k * f_error 0 b x0 x A +
                        (1 - rho ^ k) / (1 - rho) * d_mag) + d_mag)%Re).
  { nra. } rewrite H3.
  apply Rle_trans with (rho * f_error k b x0 x A + d_mag)%Re.
  - unfold f_error. 
    assert (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                 x_fix x (FT2R_mat b) (FT2R_mat A) = 
             (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
               x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A)) +
             (x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) -
              x_fix x (FT2R_mat b) (FT2R_mat A))).
    { by rewrite add_vec_distr_2. } rewrite H4. clear H4.
    apply Rle_trans with 
    (vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                       x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) ) +
     vec_inf_norm ((x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) -
                      x_fix x (FT2R_mat b) (FT2R_mat A))))%Re.
    * apply /RleP. apply triang_ineq.
    * apply Rle_trans with 
      (vec_inf_norm
         (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
          x_fix (FT2R_mat (X_m_jacobi k x0 b A)) 
            (FT2R_mat b) (FT2R_mat A)) +
        R2 * f_error k b x0 x A)%Re.
      ++ apply Rplus_le_compat_l.
         unfold x_fix. rewrite diag_matrix_vec_mult_diff.
         rewrite add_vec_distr_4. 
         rewrite -mulmxBr.
         apply Rle_trans with
         ( vec_inf_norm (A1_diag (FT2R_mat A)) * 
           vec_inf_norm (A2_J_real (FT2R_mat A) *m (x -
                                  FT2R_mat
                                   (X_m_jacobi k x0 b A))))%Re.
         -- apply /RleP.
            apply vec_inf_norm_diag_matrix_vec_mult_R.
         -- apply Rle_trans with 
            (vec_inf_norm (A1_diag (FT2R_mat A)) * 
              (matrix_inf_norm (A2_J_real (FT2R_mat A)) *
               vec_inf_norm (x - FT2R_mat (X_m_jacobi k x0 b A))))%Re.
            ** apply Rmult_le_compat_l.
               +++ apply /RleP. apply vec_norm_pd.
               +++ apply /RleP. apply submult_prop.
            ** assert ((vec_inf_norm (A1_diag (FT2R_mat A)) *
                         (matrix_inf_norm (A2_J_real (FT2R_mat A)) *
                          vec_inf_norm (x - FT2R_mat (X_m_jacobi k x0 b A))))%Re = 
                        ((vec_inf_norm (A1_diag (FT2R_mat A)) * matrix_inf_norm (A2_J_real (FT2R_mat A))) *
                        (vec_inf_norm (x - FT2R_mat (X_m_jacobi k x0 b A))))%Re).
               { nra. } rewrite H4. unfold R2. 
               rewrite sub_vec_comm_1.
               rewrite -vec_inf_norm_opp. unfold f_error. rewrite -x_fixpoint.
               +++ apply Rle_refl.
               +++ unfold x. rewrite mulmxA.
                  assert (FT2R_mat A *m A_real^-1 = 1).
                  { fold A_real. by rewrite mulmxV . }
                  rewrite H5. by rewrite mul1mx /b_real.
               +++ intros. rewrite !mxE. apply H1.
         -- auto.
      ++ eapply Rle_trans.
         -- apply Rplus_le_compat_r.
            apply Rle_trans with 
            (vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0 b A) -  
                           x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A) +
             vec_inf_norm (x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A - 
                              x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                                  (FT2R_mat b) (FT2R_mat A)))%Re.
            ** assert ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                         x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A)) = 
                       ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -  
                           x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A) +
                        (x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A - 
                              x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                                  (FT2R_mat b) (FT2R_mat A)))).
               { by rewrite add_vec_distr_2. } rewrite H4. 
               apply /RleP. apply triang_ineq.
            ** apply Rle_refl.
         -- remember (vec_inf_norm
                       (x_fix_FT2R
                          (FT2R_mat (X_m_jacobi k x0 b A))
                          (FT2R_mat b) A -
                        x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                          (FT2R_mat b) (FT2R_mat A))) as inv_bound.
            apply Rle_trans with 
            ((vec_inf_norm 
              (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
             vec_inf_norm 
              (diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
               x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A))
                    (FT2R_mat b) A)) + 
              inv_bound + R2 * f_error k b x0 x A)%Re.
             ** repeat apply Rplus_le_compat_r.
                assert ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                            x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) A) = 
                        (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                            diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
                        (diag_matrix_vec_mult_R (FT2R_mat (A1_inv_J A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
                          x_fix_FT2R (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) A)).
               { by rewrite add_vec_distr_2. } rewrite H4.
               apply /RleP.
               apply triang_ineq.
             ** eapply Rle_trans. apply Rplus_le_compat_r. apply Rplus_le_compat_r.
                +++ apply Rplus_le_compat.
                    --- simpl. unfold jacobi_iter. 
                        apply Rle_trans with 
                          ((vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                            vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) * g ty n.+1 +
                               g1 ty n.+1 (n.+1 - 1))%Re.
                        *** pose proof (@vec_norm_diag ty n). 
                            apply H4. intros.
                            pose proof (@In_nth (ftype ty * ftype ty)
                                           (rev (combine
                                              (vec_to_list_float n.+1 (A1_inv_J A))
                                              (vec_to_list_float n.+1 (b -f A2_J A *f X_m_jacobi k x0 b A)))) xy 
                                            (Zconst ty 1, Zconst ty 0) ).
                            rewrite -in_rev in H6. specialize (H6 H5).
                            destruct H6 as [j [Hlength Hnth]].
                            rewrite rev_nth in Hnth.
                            ++++ rewrite combine_length !length_veclist Nat.min_id in Hnth.
                                 assert ((n.+1 - j.+1)%coq_nat = (n.+1.-1 - j)%coq_nat).
                                 { lia. } rewrite H6 in Hnth. rewrite combine_nth in Hnth.
                                 rewrite !nth_vec_to_list_float in Hnth.
                                 rewrite -Hnth /=.
                                 specialize (Hfin (@inord n j)).
                                 rewrite mxE in Hfin. rewrite !nth_vec_to_list_float in Hfin.
                                 rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                 apply bmult_overflow_implies in Hfin; try apply Hfin.
                                 apply bmult_overflow_implies in Hfin; try apply Hfin.
                                 by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 by apply /ssrnat.ltP.
                                 rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                 by apply /ssrnat.ltP. by rewrite !length_veclist.
                           ++++ by rewrite rev_length in Hlength.
                        *** apply Rplus_le_compat_r.
                            apply Rmult_le_compat_r.
                            apply g_pos.
                            apply Rmult_le_compat_l.
                            apply /RleP. apply vec_norm_pd.
                            assert ((vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                                  (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) <=
                                    (vec_inf_norm (FT2R_mat b) + vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                    (default_rel ty))).
                            { apply vec_float_sub. intros.
                              pose proof (@In_nth (ftype ty * ftype ty)
                                           (rev (combine
                                              (vec_to_list_float n.+1 b)
                                              (vec_to_list_float n.+1 (A2_J A *f X_m_jacobi k x0 b A)))) xy 
                                            (Zconst ty 0, Zconst ty 0) ).
                              rewrite -in_rev in H5. specialize (H5 H4).
                              destruct H5 as [j [Hlength Hnth]].
                              rewrite rev_nth in Hnth.
                              ++++ rewrite combine_length !length_veclist Nat.min_id in Hnth.
                                   assert ((n.+1 - j.+1)%coq_nat = (n.+1.-1 - j)%coq_nat).
                                   { lia. } rewrite H5 in Hnth. rewrite combine_nth in Hnth.
                                   rewrite !nth_vec_to_list_float in Hnth.
                                   rewrite -Hnth /=.
                                   specialize (Hfin (@inord n j)).
                                   rewrite mxE in Hfin. rewrite !nth_vec_to_list_float in Hfin.
                                   rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2. rewrite is_finite_Bopp in Hfin2.  try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   try apply Hfin2.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP. by rewrite !length_veclist.
                             ++++ by rewrite rev_length in Hlength.
                            } apply reverse_triang_ineq in H4.
                            apply Rle_trans with 
                            ((vec_inf_norm (FT2R_mat b) +
                                    vec_inf_norm
                                      (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                   (1 + default_rel ty))%Re.
                            ++++ rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                                 apply Rle_trans with 
                                 (vec_inf_norm
                                   (FT2R_mat b -
                                    FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)) + 
                                   (vec_inf_norm (FT2R_mat b) +
                                      vec_inf_norm
                                        (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                     default_rel ty)%Re.
                                 ---- assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                      { intros. nra. } apply H5. by apply /RleP.
                                 ---- apply Rplus_le_compat_r.
                                      assert (vec_inf_norm
                                                  (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)) = 
                                              vec_inf_norm (- (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)))).
                                      { by rewrite vec_inf_norm_opp. } rewrite H5.
                                      apply /RleP. apply triang_ineq.
                            ++++ apply Rmult_le_compat_r.
                                 ---- apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                 ---- apply Rplus_le_compat_l.
                                      assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                                      { apply matrix_vec_mult_bound_corollary. intros.
                                        specialize (Hfin (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H6. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H7 in H6. clear H7.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H7 in H6. clear H7. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H7.
                                        } rewrite H7 in H6. 
                                        specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                                        specialize (H6 H5). apply H6.
                                        by rewrite !length_veclist.


                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H6. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H7 in H6. clear H7.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H7 in H6. clear H7. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H7.
                                        } rewrite H7 in H6. 
                                        specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                                        specialize (H6 H5). apply H6.
                                        by rewrite !length_veclist.
                                        
                                        intros.
                                        specialize (Hfin (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        by rewrite mxE in Hfin22.
                                       
                                      }
                                      apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                                      **** rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                                           apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                                           +++++ apply reverse_triang_ineq in H5.
                                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                                 { intros. nra. } apply H6. apply /RleP. apply H5.
                                           +++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                                  replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                                      **** apply Rle_refl.
                    --- unfold x_fix_FT2R. rewrite diag_matrix_vec_mult_diff .
                        apply Rle_trans with
                        (vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                         vec_inf_norm (FT2R_mat
                                         (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                       (FT2R_mat b -
                                        A2_J_real (FT2R_mat A) *m 
                                        FT2R_mat (X_m_jacobi k x0 b A))))%Re.
                        *** apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R .
                        *** apply Rmult_le_compat_l.
                            ++++ apply /RleP. apply vec_norm_pd.
                            ++++ assert ((FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                          (FT2R_mat b -
                                           A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A))) =
                                         (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) - 
                                          (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) +
                                         (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) - 
                                           (FT2R_mat b -
                                           A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A)))).
                                 { by rewrite add_vec_distr_2. } rewrite H4. clear H4.
                                 apply /RleP. apply triang_ineq.
         +++ assert (FT2R_mat b -
                         FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                         (FT2R_mat b -
                          A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A))  =
                     - (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                        A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A)) ).
             { rewrite add_vec_distr_4. by rewrite sub_vec_comm_1. auto. } rewrite H4. clear H4.
             rewrite -vec_inf_norm_opp. rewrite -RplusE.
             rewrite Rmult_plus_distr_l. eapply Rle_trans.
             *** apply Rplus_le_compat_r. apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                apply Rplus_le_compat.
                ++++ apply /RleP. apply vec_float_sub.
                    intros.
                     pose proof (@In_nth (ftype ty * ftype ty)
                                           (rev (combine
                                              (vec_to_list_float n.+1 b)
                                              (vec_to_list_float n.+1 (A2_J A *f X_m_jacobi k x0 b A)))) xy 
                                            (Zconst ty 0, Zconst ty 0) ).
                              rewrite -in_rev in H5. specialize (H5 H4).
                              destruct H5 as [j [Hlength Hnth]].
                              rewrite rev_nth in Hnth.
                              ---- rewrite combine_length !length_veclist Nat.min_id in Hnth.
                                   assert ((n.+1 - j.+1)%coq_nat = (n.+1.-1 - j)%coq_nat).
                                   { lia. } rewrite H5 in Hnth. rewrite combine_nth in Hnth.
                                   rewrite !nth_vec_to_list_float in Hnth.
                                   rewrite -Hnth /=.
                                   specialize (Hfin (@inord n j)).
                                   rewrite mxE in Hfin. rewrite !nth_vec_to_list_float in Hfin.
                                   rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   apply bplus_overflow_implies in Hfin2. rewrite is_finite_Bopp in Hfin2.  try apply Hfin2.
                                   apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                   rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                   try apply Hfin2.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP.
                                   rewrite rev_length combine_length !length_veclist Nat.min_id in Hlength.
                                   by apply /ssrnat.ltP. by rewrite !length_veclist.
                             ---- by rewrite rev_length in Hlength.
               ++++ assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite H4. apply /RleP. apply matrix_vec_mult_bound_corollary.
                    intros.
                    specialize (Hfin (@inord n i)). 
                    rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                    rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                    rewrite inord_val in Hfin. repeat split; try apply Hfin.
                    apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                    rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                    apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                    destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                    rewrite mxE in Hfin22.  
                    pose proof (@dotprod_finite_implies ty).
                    specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                    rewrite !combine_split  in H6. 
                    assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                    { by simpl. } rewrite H7 in H6. clear H7.
                     assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                     { by simpl. } rewrite H7 in H6. clear H7. 
                     assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                     { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                       assert (y = ord0). { by apply ord1. } by rewrite H7.
                     } rewrite H7 in H6. 
                     specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                     specialize (H6 H5). apply H6.
                     by rewrite !length_veclist.


                     apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                     rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                     apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                     destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                     rewrite mxE in Hfin22.  
                     pose proof (@dotprod_finite_implies ty).
                     specialize (H6 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                     rewrite !combine_split  in H6. 
                     assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                     { by simpl. } rewrite H7 in H6. clear H7.
                     assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                     { by simpl. } rewrite H7 in H6. clear H7. 
                     assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                     { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                       assert (y = ord0). { by apply ord1. } by rewrite H7.
                     } rewrite H7 in H6. 
                     specialize (H6 Hfin22 xy). rewrite -H7 in H6.
                     specialize (H6 H5). apply H6.
                     by rewrite !length_veclist.
                                        
                     intros.
                     specialize (Hfin (@inord n i)). 
                     rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                     rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                     rewrite inord_val in Hfin. repeat split; try apply Hfin.
                     apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                     rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                     apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                     destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                     by rewrite mxE in Hfin22.
            *** eapply Rle_trans.
                ++++ apply Rplus_le_compat_r. apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                    rewrite -!RmultE -!RplusE. apply Rmult_le_compat_l.
                    --- apply /RleP. apply vec_norm_pd.
                    --- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                        apply default_rel_ge_0. 
                        apply Rplus_le_compat_l.
                        apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                        ****  rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                            assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                           { apply matrix_vec_mult_bound_corollary. intros.

                             specialize (Hfin  (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H5 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H5. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H6 in H5. clear H6.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H6 in H5. clear H6. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H6.
                                        } rewrite H6 in H5. 
                                        specialize (H5 Hfin22 xy). rewrite -H6 in H5.
                                        specialize (H5 H4). apply H5.
                                        by rewrite !length_veclist.


                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        rewrite mxE in Hfin22.  
                                        pose proof (@dotprod_finite_implies ty).
                                        specialize (H5 (combine  (vec_to_list_float n.+1
                                                                      (\row_j0 A2_J A (inord i) j0)^T)
                                                                  (vec_to_list_float n.+1 (X_m_jacobi k x0 b A)))).
                                        rewrite !combine_split  in H5. 
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).1 = 
                                                       vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T). 
                                        { by simpl. } rewrite H6 in H5. clear H6.
                                        assert ((vec_to_list_float n.+1
                                                         (\row_j0 A2_J A  (inord i) j0)^T,
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)).2 = 
                                                       vec_to_list_float n.+1 (X_m_jacobi k x0 b A)). 
                                        { by simpl. } rewrite H6 in H5. clear H6. 
                                        assert (X_m_jacobi k x0 b A = \col_j (X_m_jacobi k x0 b A j ord0)).
                                        { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
                                          assert (y = ord0). { by apply ord1. } by rewrite H6.
                                        } rewrite H6 in H5. 
                                        specialize (H5 Hfin22 xy). rewrite -H6 in H5.
                                        specialize (H5 H4). apply H5.
                                        by rewrite !length_veclist.
                                        
                                        intros.
                                        specialize (Hfin (@inord n i)). 
                                        rewrite mxE in Hfin. rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite nth_vec_to_list_float in Hfin; last by apply ltn_ord.
                                        rewrite inord_val in Hfin. repeat split; try apply Hfin.
                                        apply bmult_overflow_implies in Hfin. destruct Hfin as [Hfin1 Hfin2].
                                        rewrite mxE in Hfin2. apply Bminus_bplus_opp_implies  in Hfin2.
                                        apply bplus_overflow_implies in Hfin2; try apply Hfin2.
                                        destruct Hfin2 as [Hfin21 Hfin22]. rewrite is_finite_Bopp in Hfin22.
                                        by rewrite mxE in Hfin22.
                           }
                            apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                            +++++ apply reverse_triang_ineq in H4.
                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                 { intros. nra. } apply H5. apply /RleP. apply H4.
                            +++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                    replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                        **** apply Rle_refl.
               ++++ (** This is where I collect terms to get rho and dmag **)
                    assert ((vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm
                                  (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              1 +
                              (vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm
                                  (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty) * g ty n.+1 +
                             g1 ty n.+1 (n.+1 - 1) +
                             vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm
                                  (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty +
                              (matrix_inf_norm (FT2R_mat (A2_J A)) *
                               vec_inf_norm
                                 (FT2R_mat (X_m_jacobi k x0 b A)) *
                               g ty n.+1 + g1 ty n.+1 (n.+1 - 1))) +
                             inv_bound + R2 * f_error k b x0 x A)%Re = 
                          ((( (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                              default_rel ty * (1 + g ty n.+1) + g ty n.+1) *
                              (vec_inf_norm (FT2R_mat (A1_inv_J A)) * matrix_inf_norm (FT2R_mat (A2_J A)))) *
                              vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))) +
                           ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                            (vec_inf_norm (FT2R_mat (A1_inv_J A)) * vec_inf_norm (FT2R_mat b)) +
                           ( (1+ g ty n.+1) * g1 ty n.+1 (n.+1 - 1) * (1 + default_rel ty)) *
                            (vec_inf_norm (FT2R_mat (A1_inv_J A))) + g1 ty n.+1 (n.+1 - 1))) + 
                           inv_bound + R2 * f_error k b x0 x A)%Re).
                   { nra. } rewrite H4. clear H4. 
                   eapply Rle_trans.
                   apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                   --- rewrite Heqinv_bound .
                       unfold x_fix_FT2R, x_fix. rewrite diag_matrix_vec_mult_diff_r.
                       apply Rle_trans with 
                       (vec_inf_norm (FT2R_mat (A1_inv_J A) - A1_diag (FT2R_mat A)) * 
                        vec_inf_norm (FT2R_mat b -
                             A2_J_real (FT2R_mat A) *m  FT2R_mat (X_m_jacobi k x0 b A)))%Re. 
                       ****  apply /RleP. apply vec_inf_norm_diag_matrix_vec_mult_R.
                       **** apply Rle_trans with 
                            ((vec_inf_norm (A1_diag (FT2R_mat A)) * (default_rel ty) + (default_abs ty)) *
                            (vec_inf_norm (FT2R_mat b) + matrix_inf_norm (A2_J_real (FT2R_mat A)) *
                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))))%Re.
                             ---- apply Rmult_le_compat.
                                  +++++ apply /RleP. apply vec_norm_pd.
                                  +++++ apply /RleP. apply vec_norm_pd.
                                  +++++  pose proof (@inverse_mat_norm_bound ty n A ).
                                         assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                         assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                         by specialize (H4 H5 H6).
                                  +++++  apply Rle_trans with
                                        (vec_inf_norm (FT2R_mat b) + vec_inf_norm (-(A2_J_real (FT2R_mat A) *m 
                                                                          FT2R_mat (X_m_jacobi k x0 b A))))%Re.
                                         apply /RleP. apply triang_ineq. rewrite -vec_inf_norm_opp. 
                                         apply Rplus_le_compat_l. apply /RleP. apply submult_prop.
                             ---- apply Rle_refl. 
                   --- assert ((vec_inf_norm (FT2R_mat (A1_inv_J A)) <= 
                                vec_inf_norm (A1_diag (FT2R_mat A))* (1 + default_rel ty) +
                                default_abs ty)%Re).
                       { rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                         pose proof (@inverse_mat_norm_bound ty n A ).
                         assert (forall i : 'I_n.+1,
                                  is_finite (fprec ty) (femax ty)
                                    (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                         assert (forall i : 'I_n.+1,
                                    is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                         specialize (H4 H5 H6).
                         assert ((vec_inf_norm
                                      (FT2R_mat (A1_inv_J A) -
                                       A1_diag A_real) <=
                                    vec_inf_norm (A1_diag A_real) *
                                    default_rel ty + default_abs ty)). { by apply /RleP. }
                         apply reverse_triang_ineq in H7.
                         assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                         { intros. nra. } apply H8. by apply /RleP.
                       } eapply Rle_trans.
                       **** apply Rplus_le_compat_r.
                            apply Rplus_le_compat.
                            ---- apply Rplus_le_compat.
                                 +++++ apply Rmult_le_compat_r.
                                       ----- apply /RleP. apply vec_norm_pd.
                                       ----- apply Rmult_le_compat_l.
                                             ***** apply Rplus_le_le_0_compat; last by apply g_pos.
                                                   apply Rplus_le_le_0_compat.
                                                   repeat apply Rmult_le_pos.
                                                   apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                                                   apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
                                                   apply g_pos. apply Rmult_le_pos.
                                                   apply default_rel_ge_0. apply Rplus_le_le_0_compat.
                                                   nra. apply g_pos.
                                             ***** apply Rmult_le_compat_r. apply /RleP. apply matrix_norm_pd.
                                                   pose proof (@inverse_mat_norm_bound ty n A ).
                                                   assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                                   assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                                   specialize (H5 H6 H7).
                                                   assert ((vec_inf_norm
                                                                (FT2R_mat (A1_inv_J A) -
                                                                 A1_diag A_real) <=
                                                              vec_inf_norm (A1_diag A_real) *
                                                              default_rel ty + default_abs ty)). { by apply /RleP. }
                                                   apply reverse_triang_ineq in H8.
                                                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                                                   { intros. nra. } 
                                                   apply Rle_trans with 
                                                   (vec_inf_norm (A1_diag A_real) * (1+ default_rel ty) + default_abs ty)%Re.
                                                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.  apply H9. by apply /RleP.
                                                   apply Rle_refl.
                                  +++++ apply Rplus_le_compat_r. apply Rplus_le_compat.
                                         ----- apply Rmult_le_compat_l. apply Rplus_le_le_0_compat.
                                               apply Rmult_le_pos. apply g_pos. apply Rplus_le_le_0_compat; try nra.
                                               apply default_rel_ge_0. apply default_rel_ge_0.
                                               apply Rmult_le_compat_r. apply /RleP. apply vec_norm_pd.
                                               pose proof (@inverse_mat_norm_bound ty n A ).
                                                   assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                                   assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                                   specialize (H5 H6 H7).
                                                   assert ((vec_inf_norm
                                                                (FT2R_mat (A1_inv_J A) -
                                                                 A1_diag A_real) <=
                                                              vec_inf_norm (A1_diag A_real) *
                                                              default_rel ty + default_abs ty)). { by apply /RleP. }
                                                   apply reverse_triang_ineq in H8.
                                                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                                                   { intros. nra. }
                                                   apply Rle_trans with 
                                                   (vec_inf_norm (A1_diag A_real) * (1+ default_rel ty) + default_abs ty)%Re.
                                                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.  apply H9. by apply /RleP.
                                                   apply Rle_refl.
                                         ----- apply Rmult_le_compat_l.
                                               apply Rmult_le_pos. apply Rmult_le_pos; try apply g1_pos.  
                                               apply Rplus_le_le_0_compat. nra. apply g_pos.
                                               apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
                                               pose proof (@inverse_mat_norm_bound ty n A ).
                                                   assert (forall i : 'I_n.+1,
                                                            is_finite (fprec ty) (femax ty)
                                                              (BDIV ty (Zconst ty 1) (A i i)) = true) by apply Hdivf.
                                                   assert (forall i : 'I_n.+1,
                                                              is_finite (fprec ty) (femax ty) (A i i) = true) by apply HAf.
                                                   specialize (H5 H6 H7).
                                                   assert ((vec_inf_norm
                                                                (FT2R_mat (A1_inv_J A) -
                                                                 A1_diag A_real) <=
                                                              vec_inf_norm (A1_diag A_real) *
                                                              default_rel ty + default_abs ty)). { by apply /RleP. }
                                                   apply reverse_triang_ineq in H8.
                                                   assert (forall a b c d:R, (a - b <= c + d)%Re -> (a <= b + c + d)%Re).
                                                   { intros. nra. }
                                                   apply Rle_trans with 
                                                   (vec_inf_norm (A1_diag A_real) * (1+ default_rel ty) + default_abs ty)%Re.
                                                   rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.  apply H9. by apply /RleP.
                                                   apply Rle_refl.
                             ---- apply Rle_refl.
                       **** assert ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                      g ty n.+1 +
                                      default_rel ty * (1 + g ty n.+1) +
                                      g ty n.+1) *
                                     ((vec_inf_norm (A1_diag A_real) *
                                       (1 + default_rel ty) + default_abs ty) *
                                      matrix_inf_norm (FT2R_mat (A2_J A))) *
                                     vec_inf_norm
                                       (FT2R_mat (X_m_jacobi k x0 b A)) +
                                     ((g ty n.+1 * (1 + default_rel ty) +
                                       default_rel ty) *
                                      ((vec_inf_norm (A1_diag A_real) *
                                        (1 + default_rel ty) + default_abs ty) *
                                       vec_inf_norm (FT2R_mat b)) +
                                      (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                      (1 + default_rel ty) *
                                      (vec_inf_norm (A1_diag A_real) *
                                       (1 + default_rel ty) + default_abs ty) +
                                      g1 ty n.+1 (n.+1 - 1)) +
                                     (vec_inf_norm (A1_diag (FT2R_mat A)) *
                                      default_rel ty + default_abs ty) *
                                     (vec_inf_norm (FT2R_mat b) +
                                      matrix_inf_norm (A2_J_real (FT2R_mat A)) *
                                      vec_inf_norm
                                        (FT2R_mat (X_m_jacobi k x0 b A))) +
                                     R2 * f_error k b x0 x A)%Re = 
                                     ( ((( ( ((1 + g ty n.+1) * (1 + default_rel ty) *
                                          g ty n.+1 + default_rel ty * (1 + g ty n.+1) +
                                          g ty n.+1) * (1 + default_rel ty) + default_rel ty ) *
                                        (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (FT2R_mat (A2_J A)))) +
                                         ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                          g ty n.+1 + default_rel ty * (1 + g ty n.+1) +
                                          g ty n.+1 ) * default_abs ty) + default_abs ty) * matrix_inf_norm (FT2R_mat (A2_J A))) *
                                        vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) ) +
                                        (((g ty n.+1 * (1 + default_rel ty) +
                                             default_rel ty) *
                                            ((vec_inf_norm (A1_diag A_real) *
                                              (1 + default_rel ty) + default_abs ty) *
                                             vec_inf_norm (FT2R_mat b)) +
                                            (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                            (1 + default_rel ty) *
                                            (vec_inf_norm (A1_diag A_real) *
                                             (1 + default_rel ty) + default_abs ty) +
                                            g1 ty n.+1 (n.+1 - 1)) +
                                            (vec_inf_norm (A1_diag (FT2R_mat A)) *
                                                    default_rel ty + default_abs ty) * vec_inf_norm (FT2R_mat b)) +
                                        R2 * f_error k b x0 x A )%Re).
                                 { assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                                       by case: (x1 == y :> nat).
                                    } rewrite -!H5. fold A_real. nra.
                                 } rewrite H5. clear H5. 
                    assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite -H5. fold A_real. fold R2. fold R2. fold b_real. 
                    assert ((vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) <= 
                             f_error k b x0 x A + 
                             vec_inf_norm (x_fix x b_real A_real))%Re).
                    { unfold f_error.
                      apply Rle_trans with 
                      (vec_inf_norm ((FT2R_mat (X_m_jacobi k x0 b A) -
                                        x_fix x (FT2R_mat b) (FT2R_mat A)) + 
                                      x_fix x b_real A_real)).
                      + rewrite sub_vec_3. apply Rle_refl.
                      + apply /RleP. apply triang_ineq.
                    } 
                    apply Rle_trans with
                    (((((1 + g ty n.+1) * (1 + default_rel ty) *
                          g ty n.+1 +
                          default_rel ty * (1 + g ty n.+1) +
                          g ty n.+1) * (1 + default_rel ty) +
                         default_rel ty) * R2 +
                        (((1 + g ty n.+1) * (1 + default_rel ty) *
                          g ty n.+1 +
                          default_rel ty * (1 + g ty n.+1) +
                          g ty n.+1) * default_abs ty +
                         default_abs ty) *
                        matrix_inf_norm (A2_J_real A_real)) *
                       (f_error k b x0 x A +
                            vec_inf_norm (x_fix x b_real A_real)) +
                       ((g ty n.+1 * (1 + default_rel ty) +
                         default_rel ty) *
                        ((vec_inf_norm (A1_diag A_real) *
                          (1 + default_rel ty) + default_abs ty) *
                         vec_inf_norm b_real) +
                        (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                        (1 + default_rel ty) *
                        (vec_inf_norm (A1_diag A_real) *
                         (1 + default_rel ty) + default_abs ty) +
                        g1 ty n.+1 (n.+1 - 1) +
                        (vec_inf_norm (A1_diag A_real) *
                         default_rel ty + default_abs ty) *
                        vec_inf_norm b_real) +
                       R2 * f_error k b x0 x A )%Re.
                    ---- repeat apply Rplus_le_compat_r.
                        repeat apply Rmult_le_compat_l.
                        ***** apply Rplus_le_le_0_compat.
                              apply Rmult_le_pos.
                              repeat apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
                              repeat apply Rmult_le_pos.
                              +++++ apply Rplus_le_le_0_compat; try apply g_pos.
                                    apply Rplus_le_le_0_compat.
                                    repeat apply Rmult_le_pos.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                                    apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                    apply g_pos. apply Rmult_le_pos. apply default_rel_ge_0.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                              +++++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                              +++++ unfold R2. apply Rmult_le_pos.
                                     ----- apply /RleP. apply vec_norm_pd.
                                     ----- apply /RleP. apply matrix_norm_pd.
                              +++++ apply Rmult_le_pos; last by (apply /RleP;apply matrix_norm_pd).
                                    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
                                    apply Rmult_le_pos; last by apply default_abs_ge_0.
                                    apply Rplus_le_le_0_compat; last by apply g_pos.
                                    apply Rplus_le_le_0_compat.
                                    repeat apply Rmult_le_pos.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                                    apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                    apply g_pos.
                                    apply Rmult_le_pos. apply default_rel_ge_0.
                                    apply Rplus_le_le_0_compat; try nra; try apply g_pos.
                        ***** apply H6.
                    ---- assert ( (((((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * (1 + default_rel ty) +
                                   default_rel ty) * R2 +
                                  (((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * default_abs ty +
                                   default_abs ty) *
                                  matrix_inf_norm (A2_J_real A_real)) *
                                 (f_error k b x0 x A +
                                  vec_inf_norm (x_fix x b_real A_real)) +
                                 ((g ty n.+1 * (1 + default_rel ty) +
                                   default_rel ty) *
                                  ((vec_inf_norm (A1_diag A_real) *
                                    (1 + default_rel ty) + default_abs ty) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   (1 + default_rel ty) + default_abs ty) +
                                  g1 ty n.+1 (n.+1 - 1) +
                                  (vec_inf_norm (A1_diag A_real) *
                                   default_rel ty + default_abs ty) *
                                  vec_inf_norm b_real) +
                                 R2 * f_error k b x0 x A)%Re = 
                                ((( ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * (1 + default_rel ty) +
                                   default_rel ty) * R2 +
                                  (((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * default_abs ty +
                                   default_abs ty) *
                                  matrix_inf_norm (A2_J_real A_real)) + R2) *
                                  f_error k b x0 x A) + 
                                (((g ty n.+1 * (1 + default_rel ty) +
                                   default_rel ty) *
                                  ((vec_inf_norm (A1_diag A_real) *
                                    (1 + default_rel ty) + default_abs ty) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   (1 + default_rel ty) + default_abs ty) +
                                  g1 ty n.+1 (n.+1 - 1) +
                                  (vec_inf_norm (A1_diag A_real) *
                                   default_rel ty + default_abs ty) *
                                  vec_inf_norm b_real) + 
                                  ((((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * (1 + default_rel ty) +
                                   default_rel ty) * R2 +
                                  (((1 + g ty n.+1) * (1 + default_rel ty) *
                                    g ty n.+1 +
                                    default_rel ty * (1 + g ty n.+1) +
                                    g ty n.+1) * default_abs ty +
                                   default_abs ty) *
                                  matrix_inf_norm (A2_J_real A_real)) * 
                                  vec_inf_norm (x_fix x b_real A_real)))%Re).
                              { nra. }  rewrite H7. clear H7. fold delta. fold rho. fold d_mag.
                              unfold f_error. fold b_real. fold A_real. apply Rle_refl.
 - apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * by apply rho_ge_0.
    * nra.
Admitted.
 
End WITHNANS.


