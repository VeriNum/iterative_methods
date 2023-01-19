From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

Require Import floatlib jacob_list_fun_model fma_dot_mat_model 
               inf_norm_properties fma_matrix_vec_mult.

Require Import common fma_dot_acc float_acc_lems dotprod_model.
Require Import fma_matrix_vec_mult vec_sum_inf_norm_rel.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas fma_is_finite.

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


(** Define forward error **)

Fixpoint vec_to_list_real {n:nat} (m:nat) (v :'cV[R]_n.+1)
   : list R := 
   match m with 
   | O => []
   | S p => [v (@inord n p) ord0] ++ vec_to_list_real p v
   end.


Definition A1_diag {n: nat} {ty} (A: 'M[ftype ty]_n.+1) : 'cV[R]_n.+1:=
  \col_i (FT2R (BDIV ty (Zconst ty 1) (A i i))).

Definition diag_matrix_vec_mult_R {n:nat} (v1 v2 : 'cV[R]_n.+1)
  : 'cV[R]_n.+1 :=
  \col_i ((nth (n.+1.-1 -i) (vec_to_list_real n.+1 v1) 0%Re) * 
          (nth (n.+1.-1 -i) (vec_to_list_real n.+1 v2) 0%Re)).

Lemma nth_vec_to_list_real_sub {n:nat} i m (v1 v2 :'cV[R]_n.+1) d:
  (i < m)%nat ->
  nth (m.-1 -i) (@vec_to_list_real n m (v1 - v2)) d = 
  nth (m.-1 -i) (@vec_to_list_real n m v1) d - 
  nth (m.-1 -i) (@vec_to_list_real n m v2) d.
Proof.
intros.
induction m.
+ by rewrite ltn0 in H.
+ simpl. rewrite -subn_gt0 in IHm. rewrite -predn_sub in IHm.
  destruct (m-i)%nat.
  - by rewrite !mxE /=.
  - simpl in IHm. by apply IHm.
Qed.

Lemma diag_matrix_vec_mult_diff {n:nat} (v1 v2 v3 : 'cV[R]_n.+1):
  diag_matrix_vec_mult_R v1 v2 - diag_matrix_vec_mult_R v1 v3 = 
  diag_matrix_vec_mult_R v1 (v2 - v3).
Proof.
apply /matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite nth_vec_to_list_real_sub.
+ rewrite -!RmultE -!RminusE. field_simplify. auto.
+ apply ltn_ord.
Qed.

Lemma nth_vec_to_list_real {n:nat} i m (v :'cV[R]_n.+1) d:
  (i < m)%nat ->
  nth (m.-1 -i) (@vec_to_list_real n m v) d = v (@inord n i) ord0.
Proof.
intros.
elim: m i H => [ | m IHm] i H.
+ by [].
+ simpl.
  rewrite leq_eqVlt in H.
  assert ((i == m) \/ (i < m)%nat).
  { by apply /orP. } destruct H0.
  - assert (i = m). { by apply /eqP. }
    rewrite H1. simpl.
    assert ((m - m)%nat = 0%N). 
    { apply /eqP. rewrite subn_eq0. by []. } by rewrite H2 /=.
  - assert (nth (m.-1 - i) (vec_to_list_real m v)
                d = v (inord i) ord0).
    { by apply IHm. } 
    rewrite -H1. rewrite -[in RHS]predn_sub.
    rewrite -subn_gt0 in H0. rewrite -predn_sub in H1.
    by destruct (m - i)%nat.
Qed.


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


Definition A2_J_real {n:nat} (A: 'M[R]_n.+1): 
  'M[R]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then 0%Re else A i j. 

(** Define real real functional model **)
Definition x_fix {n:nat} {ty} x b (A: 'M[ftype ty]_n.+1) :
  'cV[R]_n.+1 :=
  let A_real := FT2R_mat A in
  let r := b - ((A2_J_real A_real) *m x) in
  diag_matrix_vec_mult_R (A1_diag A_real) r.

Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A in
  vec_inf_norm (FT2R_mat x_k - x).


Definition matrix_of_diag_A1 {ty} {n:nat} (A: 'M[ftype ty]_n.+1) :
 'M[ftype ty]_n.+1 :=
 \matrix_(i, j) 
    (if (i == j :> nat) then (A1_inv_J A i ord0) else (Zconst ty 0)).


Lemma rho_ge_0 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel ty in
  let rho := (((1 + g ty n.+1) * (1 + delta) * g ty n.+1 +
                delta * (1 + g ty n.+1) + g ty n.+1 + 1) * R)%Re in
 (0 <= rho)%Re.
Proof.
intros.
unfold rho.
repeat apply Rmult_le_pos.
+ apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rplus_le_le_0_compat.
      ++ repeat apply Rmult_le_pos.
         -- apply Rplus_le_le_0_compat. nra. apply g_pos.
         -- unfold delta. apply Rplus_le_le_0_compat. nra.
            apply default_rel_ge_0.
         -- apply g_pos.
      ++ unfold delta. apply Rmult_le_pos.
         -- unfold delta. apply default_rel_ge_0.
         -- apply Rplus_le_le_0_compat. nra. apply g_pos.
    * apply g_pos.
  - nra.
+ apply /RleP. apply vec_norm_pd.
+ apply /RleP. apply matrix_norm_pd.
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


Lemma x_fixpoint {n:nat} {ty} x b (A: 'M[ftype ty]_n.+1):
  let A_real := FT2R_mat A in 
  A_real *m x = b ->
  (forall i, (FT2R_mat A) i i <> 0%Re) ->
  x = x_fix x b A.
Proof.
intros.
unfold x_fix. unfold diag_matrix_vec_mult_R.
apply /matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite !nth_vec_to_list_real.
+ rewrite !mxE. 
  assert (x x0 y = ((1 / FT2R (A (inord x0) (inord x0))) *
                    (FT2R (A (inord x0) (inord x0)) * x x0 y))%Re).
  { assert (((1 / FT2R (A (inord x0) (inord x0))) *
                    (FT2R (A (inord x0) (inord x0)) * x x0 y))%Re = 
             ((FT2R (A (inord x0) (inord x0)) * / FT2R (A (inord x0) (inord x0)) )*
              x x0 y)%Re).
    { nra. } rewrite H1. rewrite Rinv_r.
    nra. specialize (H0 (@inord n x0)). rewrite !mxE in H0. apply H0.
  } rewrite H1.
  assert (((FT2R (A (inord x0) (inord x0)) * x x0 y))%Re  = 
           (b (inord x0) ord0 -
              \sum_j A2_J_real (FT2R_mat A) (inord x0) j * x j ord0)%Re).   
  { assert (forall x y z:R, (x + y = z)%Re -> (x = z - y)%Re).
    { intros. nra. } apply H2.
    assert ((FT2R (A (inord x0) (inord x0)) * x x0 y +
              \sum_j A2_J_real (FT2R_mat A) (inord x0) j * x j ord0)%Re = 
              \sum_j ((FT2R_mat A) x0 j * x j ord0)%Re).
    { unfold A2_J_real. rewrite [in RHS](bigD1 x0) /=.
      rewrite inord_val. 
      assert (y = ord0). { by apply ord1. } rewrite H3. rewrite mxE.
      apply Rplus_eq_compat_l. 
      assert (\sum_(i < n.+1 | i != x0)
                    ((FT2R_mat A) x0 i * x i ord0)%Re = 
               \sum_(i < n.+1)
                   (if (~~ (i == x0 :> nat)) then 
                      ((FT2R_mat A) x0 i * x i ord0)%Re else 0%Re)).
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


(** remember to remove this later **)
Lemma ft2r_mat_equiv {ty} {m n : nat} (A : 'M[ftype ty]_(m.+1,n.+1)):
  fma_matrix_vec_mult.FT2R_mat A = FT2R_mat A.
Proof.
by unfold fma_matrix_vec_mult.FT2R_mat, FT2R_mat.
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
     (Rabs (FT2R (fst (xy))) <= sqrt ((F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1)))%Re /\
     (Rabs (FT2R (snd (xy))) <= sqrt ((F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1)))%Re) ->

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
  { unfold Bmult_no_overflow. unfold rounded.
    pose proof (generic_round_property ty 
                  (FT2R
         (nth (n.+1.-1 - @inord n i)
            (vec_to_list_float n.+1 v1)
            (Zconst ty 0)) *
       FT2R
         (nth (n.+1.-1 - @inord n i)
            (vec_to_list_float n.+1 v2)
            (Zconst ty 0)))).
    destruct H2 as [d [e [Heq [Hd [He H2]]]]].
    rewrite H2. rewrite !nth_vec_to_list_float.
    + rewrite !inord_val.
      apply Rle_lt_trans with
      (Rabs
         (FT2R (v1 (inord i) ord0) *
          FT2R (v2 (inord i) ord0) * (1 + d)) + Rabs e)%Re.
      - apply Rabs_triang.
      - rewrite !Rabs_mult.
        apply Rle_lt_trans with
        (Rabs (FT2R (v1 (inord i) ord0)) *
           Rabs (FT2R (v2 (inord i) ord0)) * 
           (1 + default_rel ty) + default_abs ty)%Re.
        * apply Rplus_le_compat.
          ++ apply Rmult_le_compat_l.
             -- apply Rmult_le_pos; apply Rabs_pos.
             -- apply Rle_trans with (Rabs 1 + Rabs d)%Re.
                ** apply Rabs_triang.
                ** rewrite Rabs_R1. apply Rplus_le_compat_l.
                   apply Hd.
          ++ apply He.
        * apply Rle_lt_trans with 
            ((sqrt
              (F' ty /
               (INR n.+1 * (1 + default_rel ty) ^ n.+1))) ^ 2 * (1 + default_rel ty) +
             default_abs ty)%Re.
          ++ apply Rplus_le_compat_r.
             apply Rmult_le_compat_r.
             -- apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
             -- assert (forall x:R, (x^2)%Re = (x * x)%Re).
                { intros. simpl;nra. } rewrite H3.
                assert (Hin: In (v1 (inord i) ord0, v2 (inord i) ord0)
                           (combine (vec_to_list_float n.+1 v1)
                              (vec_to_list_float n.+1 v2))).
                { apply in_rev. rewrite -combine_rev; last by rewrite !length_veclist.
                  assert ((v1 (inord i) ord0, v2 (inord i) ord0) = 
                           nth i (combine (rev (vec_to_list_float n.+1 v1))
                                    (rev (vec_to_list_float n.+1 v2))) (Zconst ty 0, Zconst ty 0)).
                  { rewrite combine_nth. rewrite !rev_nth !length_veclist.
                    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat).
                    { lia. } rewrite H4. rewrite !nth_vec_to_list_float; try by [].
                    by rewrite size_map size_enum_ord in H0.
                    by rewrite size_map size_enum_ord in H0.
                    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H0.
                    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H0.
                    by rewrite !rev_length !length_veclist.
                 } rewrite H4. apply nth_In. rewrite combine_length.
                 rewrite !rev_length !length_veclist Nat.min_id.
                 rewrite size_map size_enum_ord in H0. by apply /ssrnat.ltP.
                } specialize (H (v1 (inord i) ord0, v2 (inord i) ord0) Hin).
                destruct H as [Hf1 [Hf2 [Ha1 Ha2]]].
                apply Rmult_le_compat; try apply Rabs_pos. 
               ** apply Rle_trans with 
                    (sqrt ((F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1))); try apply Ha1.
                  apply sqrt_le_1_alt.
                  apply Rmult_le_compat_r.
                  +++ rewrite Rinv_mult_distr.
                      --- apply Rmult_le_pos.
                          *** apply Rlt_le. apply Rinv_0_lt_compat.
                              apply lt_0_INR. lia.
                          *** apply Rlt_le. apply Rinv_0_lt_compat.
                              apply pow_lt. apply Rplus_lt_0_compat. nra.
                              apply default_rel_gt_0.
                      --- apply not_0_INR. lia.
                      --- apply pow_nonzero.
                          assert ((0 <=  default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                          { nra. } apply H. apply default_rel_ge_0.

                 +++ assert (forall x y:R, (x * y <= x * 1)%Re -> (x * y <= x)%Re).
                     { intros. nra. } apply H. apply Rmult_le_compat_l;try nra.
                     apply F_p_ge_0.
              ** apply Rle_trans with 
                    (sqrt ((F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1))); try apply Ha2.
                  apply sqrt_le_1_alt.
                  apply Rmult_le_compat_r.
                  +++ rewrite Rinv_mult_distr.
                      --- apply Rmult_le_pos.
                          *** apply Rlt_le. apply Rinv_0_lt_compat.
                              apply lt_0_INR. lia.
                          *** apply Rlt_le. apply Rinv_0_lt_compat.
                              apply pow_lt. apply Rplus_lt_0_compat. nra.
                              apply default_rel_gt_0.
                      --- apply not_0_INR. lia.
                      --- apply pow_nonzero.
                          assert ((0 <=  default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                          { nra. } apply H. apply default_rel_ge_0.

                 +++ assert (forall x y:R, (x * y <= x * 1)%Re -> (x * y <= x)%Re).
                     { intros. nra. } apply H. apply Rmult_le_compat_l;try nra.
                     apply F_p_ge_0.
          ++ rewrite pow2_sqrt.
             -- apply Rle_lt_trans with 
                (F' ty + default_abs ty)%Re.
                ** apply Rplus_le_compat_r.
                   assert ((F' ty / (INR n.+1 * (1 + default_rel ty) ^ n.+1) *
                                (1 + default_rel ty))%Re = 
                            ((F' ty * / (INR n.+1 * (1 + default_rel ty) ^ n.+1)) *
                               (1 + default_rel ty))%Re).
                   { nra. } rewrite H3. clear H3.
                   rewrite Rinv_mult_distr.
                   +++  assert ((F' ty *
                                   (/ INR n.+1 * / (1 + default_rel ty) ^ n.+1) *
                                   (1 + default_rel ty))%Re = 
                                 (F' ty * (/ INR n.+1 * ((1 + default_rel ty) */ (1 + default_rel ty) ^ n.+1)))%Re).
                        {  nra. } rewrite H3. clear H3.
                        assert (forall x y:R, (x * y <= x * 1)%Re -> (x * y <= x)%Re).
                        { intros. nra. } apply H3. apply Rmult_le_compat_l.
                        --- apply  F_p_ge_0 .
                        --- apply rel_le_1.
                   +++ apply not_0_INR. lia.
                   +++ apply pow_nonzero.
                       assert ((0 <= default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                       { intros. nra. } apply H3. apply default_rel_ge_0.
                ** unfold F'. 
                   rewrite Rmult_minus_distr_l. rewrite Rmult_1_r.
                   assert ((fmax ty - fmax ty * (2 * default_rel ty) +
                              default_abs ty)%Re = 
                            (fmax ty - (2 * fmax ty * default_rel ty - default_abs ty))%Re).
                   { nra. } rewrite H3.
                   assert (forall x y:R, (0 < y)%Re -> (x - y < x)%Re).
                   { intros. nra. } apply H4. apply delta_eps_lt_fmax.
          -- apply Rmult_le_pos.
             ** apply  F_p_ge_0 .
             ** rewrite Rinv_mult_distr.
                +++ apply Rmult_le_pos.
                    --- apply Rlt_le. apply Rinv_0_lt_compat.
                        apply lt_0_INR. lia.
                    --- apply Rlt_le. apply Rinv_0_lt_compat.
                        apply pow_lt. apply Rplus_lt_0_compat. nra.
                        apply default_rel_gt_0.
                +++ apply not_0_INR. lia.
                +++ apply pow_nonzero.
                    assert ((0 <=  default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                    { nra. } apply H3. apply default_rel_ge_0.
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


(* 
Lemma vec_norm_diag {ty} {n:nat} (v1 v2 : 'cV[ftype ty]_n.+1):
  (forall (xy : ftype ty * ftype ty),
    In xy
      (combine
         (vec_to_list_float n.+1  v1)
         (vec_to_list_float n.+1 v2)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\ 
     (Rabs (FT2R (fst (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1)))%Re /\
     (Rabs (FT2R (snd (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1)))%Re) ->

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
  { unfold Bmult_no_overflow. unfold rounded.
    pose proof (generic_round_property ty 
                  (FT2R
         (nth (n.+1.-1 - @inord n i)
            (vec_to_list_float n.+1 v1)
            (Zconst ty 0)) *
       FT2R
         (nth (n.+1.-1 - @inord n i)
            (vec_to_list_float n.+1 v2)
            (Zconst ty 0)))).
    destruct H2 as [d [e [Heq [Hd [He H2]]]]].
    rewrite H2. rewrite !nth_vec_to_list_float.
    + rewrite !inord_val.
      apply Rle_lt_trans with
      (Rabs
         (FT2R (v1 (inord i) ord0) *
          FT2R (v2 (inord i) ord0) * (1 + d)) + Rabs e)%Re.
      - apply Rabs_triang.
      - rewrite !Rabs_mult.
        apply Rle_lt_trans with
        (Rabs (FT2R (v1 (inord i) ord0)) *
           Rabs (FT2R (v2 (inord i) ord0)) * 
           (1 + default_rel ty) + default_abs ty)%Re.
        * apply Rplus_le_compat.
          ++ apply Rmult_le_compat_l.
             -- apply Rmult_le_pos; apply Rabs_pos.
             -- apply Rle_trans with (Rabs 1 + Rabs d)%Re.
                ** apply Rabs_triang.
                ** rewrite Rabs_R1. apply Rplus_le_compat_l.
                   apply Hd.
          ++ apply He.
        * apply Rle_lt_trans with 
            ((sqrt
              (F' ty /
               (INR n.+1 * (1 + default_rel ty) ^ n.+1))) ^ 2 * (1 + default_rel ty) +
             default_abs ty)%Re.
          ++ apply Rplus_le_compat_r.
             apply Rmult_le_compat_r.
             -- apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
             -- assert (forall x:R, (x^2)%Re = (x * x)%Re).
                { intros. simpl;nra. } rewrite H3.
                assert (Hin: In (v1 (inord i) ord0, v2 (inord i) ord0)
                           (combine (vec_to_list_float n.+1 v1)
                              (vec_to_list_float n.+1 v2))).
                { apply in_rev. rewrite -combine_rev; last by rewrite !length_veclist.
                  assert ((v1 (inord i) ord0, v2 (inord i) ord0) = 
                           nth i (combine (rev (vec_to_list_float n.+1 v1))
                                    (rev (vec_to_list_float n.+1 v2))) (Zconst ty 0, Zconst ty 0)).
                  { rewrite combine_nth. rewrite !rev_nth !length_veclist.
                    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat).
                    { lia. } rewrite H4. rewrite !nth_vec_to_list_float; try by [].
                    by rewrite size_map size_enum_ord in H0.
                    by rewrite size_map size_enum_ord in H0.
                    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H0.
                    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H0.
                    by rewrite !rev_length !length_veclist.
                 } rewrite H4. apply nth_In. rewrite combine_length.
                 rewrite !rev_length !length_veclist Nat.min_id.
                 rewrite size_map size_enum_ord in H0. by apply /ssrnat.ltP.
                } specialize (H (v1 (inord i) ord0, v2 (inord i) ord0) Hin).
                destruct H as [Hf1 [Hf2 [Ha1 Ha2]]].
                apply Rmult_le_compat; try apply Rabs_pos; try apply Ha1; try apply Ha2.
          ++ rewrite pow2_sqrt.
             -- apply Rle_lt_trans with 
                (F' ty + default_abs ty)%Re.
                ** apply Rplus_le_compat_r.
                   assert ((F' ty / (INR n.+1 * (1 + default_rel ty) ^ n.+1) *
                                (1 + default_rel ty))%Re = 
                            ((F' ty * / (INR n.+1 * (1 + default_rel ty) ^ n.+1)) *
                               (1 + default_rel ty))%Re).
                   { nra. } rewrite H3. clear H3.
                   rewrite Rinv_mult_distr.
                   +++  assert ((F' ty *
                                   (/ INR n.+1 * / (1 + default_rel ty) ^ n.+1) *
                                   (1 + default_rel ty))%Re = 
                                 (F' ty * (/ INR n.+1 * ((1 + default_rel ty) */ (1 + default_rel ty) ^ n.+1)))%Re).
                        {  nra. } rewrite H3. clear H3.
                        assert (forall x y:R, (x * y <= x * 1)%Re -> (x * y <= x)%Re).
                        { intros. nra. } apply H3. apply Rmult_le_compat_l.
                        --- apply  F_p_ge_0 .
                        --- apply rel_le_1.
                   +++ apply not_0_INR. lia.
                   +++ apply pow_nonzero.
                       assert ((0 <= default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                       { intros. nra. } apply H3. apply default_rel_ge_0.
                ** unfold F'. 
                   rewrite Rmult_minus_distr_l. rewrite Rmult_1_r.
                   assert ((fmax ty - fmax ty * (2 * default_rel ty) +
                              default_abs ty)%Re = 
                            (fmax ty - (2 * fmax ty * default_rel ty - default_abs ty))%Re).
                   { nra. } rewrite H3.
                   assert (forall x y:R, (0 < y)%Re -> (x - y < x)%Re).
                   { intros. nra. } apply H4. apply delta_eps_lt_fmax.
          -- apply Rmult_le_pos.
             ** apply  F_p_ge_0 .
             ** rewrite Rinv_mult_distr.
                +++ apply Rmult_le_pos.
                    --- apply Rlt_le. apply Rinv_0_lt_compat.
                        apply lt_0_INR. lia.
                    --- apply Rlt_le. apply Rinv_0_lt_compat.
                        apply pow_lt. apply Rplus_lt_0_compat. nra.
                        apply default_rel_gt_0.
                +++ apply not_0_INR. lia.
                +++ apply pow_nonzero.
                    assert ((0 <=  default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                    { nra. } apply H3. apply default_rel_ge_0.
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

*)

Lemma sqrt_full_le: 
  forall x:R,
  (1 <= x)%Re ->
  (sqrt x <= x)%Re.
Proof.
intros. 
assert ((sqrt x <= sqrt x * sqrt x)%Re -> 
        (sqrt x <= x)%Re).
{ rewrite sqrt_def. nra. nra. }
apply H0. 
assert ((sqrt x * 1<= sqrt x * sqrt x)%Re ->
        (sqrt x <= sqrt x * sqrt x)%Re).
{ nra. } apply H1.
apply Rmult_le_compat_l.
apply sqrt_pos.
replace 1%Re with (sqrt 1%Re); try by rewrite sqrt_1.
apply  sqrt_le_1_alt. nra.
Qed.


Print default_rel.
Print Z.pow_pos.

(*
Lemma C_ge_0 (m n:nat):
  (0 <= C m n)%Re.
Proof.
unfold C. apply Rmult_le_pos.
+ apply pos_INR.
+ rewrite Rinv_mult_distr.
  - apply Rmult_le_pos; 
    (apply Rlt_le, Rinv_0_lt_compat; apply lt_0_INR, lt_O_fact).
  - apply not_0_INR. apply fact_neq_0.
  - apply not_0_INR. apply fact_neq_0.
Qed.


Lemma fact_bound:
  forall m n:nat,
  (n <= m)%coq_nat -> 
  (INR (fact m) / INR (fact (m - n)%coq_nat) <= INR (m ^ n))%Re.
Proof.
intros.
induction n.
+ simpl. 
  assert ((m - 0)%coq_nat = m). { lia. } rewrite H0.
  assert ((INR (fact m) / INR (fact m) )%Re= 1%Re).
  { apply Rinv_r. apply not_0_INR. apply fact_neq_0. }
  rewrite H1. nra.
+ simpl.
  assert ((n <= m)%coq_nat).
  { lia. } specialize (IHn H0).
  rewrite mult_INR. 
  assert (INR (fact (m - S n)%coq_nat) =  (INR (fact (m - n)%coq_nat) * / INR (m - n)%coq_nat )%Re).
  { assert ((m-n)%coq_nat = S (m - S n)%coq_nat).
    { lia.  } 
    assert (fact (m - n)%coq_nat = fact (S (m - S n)%coq_nat)).
    { by rewrite H1. } rewrite H2. simpl.
    assert ((fact (m - S n)%coq_nat + (m - S n)%coq_nat * fact (m - S n)%coq_nat)%coq_nat = 
            ((m - n)%coq_nat * fact (m - S n)%coq_nat)%coq_nat).
    { assert ((fact (m - n.+1)%coq_nat +
                (m - n.+1)%coq_nat * fact (m - n.+1)%coq_nat)%coq_nat = 
              (fact (m - n.+1)%coq_nat * 1%nat +
                (m - n.+1)%coq_nat * fact (m - n.+1)%coq_nat)%coq_nat).
      { lia.

lia. } rewrite H3. rewrite mult_INR.
    assert (INR (m - n) * INR (fact (m - S n)) * / INR (m - n) = 
            INR (fact (m - S n)) * (INR (m - n) */ INR (m - n))).
    { nra. } rewrite H4. rewrite Rinv_r. nra.
    apply not_0_INR;lia.
  } rewrite H1. 
  assert (INR (fact m) / (INR (fact (m - n)) * / INR (m - n)) = 
          INR (fact m) * / (INR (fact (m - n)) * / INR (m - n))).
  { nra. } rewrite H2. rewrite Rinv_mult_distr.
  - rewrite Rinv_involutive.
    * assert (INR (fact m) * (/ INR (fact (m - n)) * INR (m - n)) = 
              (INR (fact m) / INR (fact (m - n))) * INR (m - n)).
      { nra. } rewrite H3.
      apply Rle_trans with 
      (INR (m ^ n) * INR (m - n)).
      ++ apply Rmult_le_compat_r.
         -- apply pos_INR. 
         -- apply IHn.
      ++ rewrite Rmult_comm. apply Rmult_le_compat_r.
         -- apply pos_INR.
         -- apply le_INR; lia.
    * apply not_0_INR;lia.
  - apply not_0_INR, fact_neq_0.
  - apply Rinv_neq_0_compat. apply not_0_INR;lia.
Qed.
*)

Require Import generalize.

Lemma pow_1: forall n:nat,
  (1^n)%Re = 1%Re.
Admitted.

Require Import Coq.ZArith.Znat.
Lemma fact_distr {n: nat}:
  (fact n + n * fact n)%nat =
  (fact n * (n + 1))%nat.
Admitted.

Lemma ratio_gt_0 {ty}:
  forall m:nat, 
  let u0 := default_rel ty in
  (m < 2 ^ (Z.to_nat (fprec ty)))%nat ->
  (0 < (1 - INR m * u0 / INR 2))%Re.
Admitted.
(*
Proof.
intros.
replace (INR 2) with 2 by (simpl;nra).
assert (INR m * u0 < 2 -> 0 < 1 - INR m * u0 / 2).
{ nra. } apply H0.
unfold u0. simpl.
assert (INR m < 2 * 2 * IZR (Z.pow_pos 2 23) ->
        INR m * (/ 2 * / IZR (Z.pow_pos 2 23)) < 2).
{ simpl; nra. } apply H1.
apply Rlt_trans with 
(INR (Z.to_nat (Z.pow_pos 2 23))).
+ apply lt_INR;lia.
+ rewrite INR_IZR_INZ. 
  assert ((Z.of_nat (Z.to_nat (Z.pow_pos 2 23))) = Z.pow_pos 2 23).
  { lia. } rewrite H2. nra.
Qed.
  
*)

Lemma delta_bound {ty} :
  forall m:nat, 
  let u0 := default_rel ty in
  (m < 2 ^ (Z.to_nat (fprec ty)))%nat ->
  (((1 + u0) ^ m - 1) < 2)%Re.
Proof.
intros.
assert (((1 + u0) ^ m  < 3)%Re -> ((1 + u0) ^ m - 1 < 2)%Re).
{ nra. } apply H0.
assert ((1+u0)%Re = (u0 + 1)%Re). { nra. } rewrite H1. clear H1.
rewrite binomial.
apply Rle_lt_trans with
(sum_f_R0 (fun i : nat => ((INR (m ^ i) / INR (fact i)) * u0 ^ i * 1 ^ (m - i))%Re) m).
+ apply sum_Rle. intros.
  rewrite Rmult_assoc. 
  match goal with |-context[(_ <= ?a * ?b * ?c)%Re]=>
    replace (a * b * c)%Re with (a * (b * c))%Re by nra
  end. apply Rmult_le_compat.
  - apply C_ge_0 .
  - apply Rmult_le_pos. try apply Rlt_le,x_pow_gt_0;try nra.
    unfold u0. apply default_rel_gt_0. simpl.
    apply Rlt_le. apply pow_lt. nra.
  - unfold C. 
    assert ((INR (fact m) / (INR (fact n) * INR (fact (m - n))))%Re = 
              ((INR (fact m) / INR (fact (m-n))) * / INR (fact n))%Re).
    { assert ((INR (fact m) / (INR (fact n) * INR (fact (m - n))))%Re = 
              (INR (fact m) * / (INR (fact n) * INR (fact (m - n))))%Re).
      { nra. } rewrite H2. 
      rewrite Rinv_mult_distr; try nra; try apply not_0_INR, fact_neq_0.
    } rewrite H2. apply Rmult_le_compat_r.
    * apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR. apply lt_O_fact.
    * apply fact_bound;lia.
  - rewrite pow_1. nra.
+ assert (m = 0%nat \/ (0 < m)%nat). { admit. } destruct H1.
  - rewrite H1. simpl. nra.
  - apply Rle_lt_trans with 
    (1 + INR m *u0 * sum_f_R0 (fun i: nat => (INR (m^i) * u0^i / INR (2^i))%Re) (m-1)%nat)%Re.
    * rewrite decomp_sum.
      ++ simpl.
         assert ((1 / 1 * 1 * 1 ^ (m - 0)%nat)%Re = 1%Re). { rewrite pow1. nra. }
         rewrite H2. clear H2.
         apply Rplus_le_compat_l.
         rewrite scal_sum. 
         assert ((m - 1)%nat = (Init.Nat.pred m)). { by rewrite -subn1. } rewrite H2.
         apply sum_Rle. intros.
         rewrite !mult_INR. rewrite pow1.
         assert ((INR m * INR (m ^ n) / INR (fact n + n * fact n) *
                    (u0 * u0 ^ n) * 1)%Re = 
                 (( INR (m ^ n) / INR (fact n + n * fact n) * u0^n) * 
                 (INR m * u0) )%Re).
         { nra. } rewrite H4. apply Rmult_le_compat_r.
         -- apply Rmult_le_pos. apply pos_INR. unfold u0;simpl.
            apply default_rel_ge_0.
         -- rewrite Rmult_assoc. 
            assert ((INR (m ^ n) * u0 ^ n / INR (2 ^ n))%Re = 
                    (INR (m ^ n) * ( / INR (2 ^ n) * u0^n))%Re).
            { nra. } rewrite H5. apply Rmult_le_compat_l.
            ** apply pos_INR.
            ** apply Rmult_le_compat_r. 
               apply pow_le. unfold u0. apply default_rel_ge_0.
               assert (n = 0%nat \/ (0 < n)%nat).
               { admit. } destruct H6. 
               +++ rewrite H6. simpl. nra.
               +++ assert (n = 1%nat \/ (1 < n)%nat). { admit. } destruct H7.
                   --- rewrite H7. simpl. nra.
                   --- apply Rlt_le, Rinv_lt_contravar.
                       *** apply Rmult_lt_0_compat. apply lt_0_INR. 
                           apply pow_2_gt_0. apply lt_0_INR. apply /ssrnat.ltP.
                           rewrite addn_gt0. apply /orP. left. apply /ssrnat.ltP. apply lt_O_fact. 
                       *** assert ((fact n + n * fact n)%nat = (fact n * (n+1))%nat).
                           { by rewrite fact_distr. }
                           rewrite H8. apply fact_low_bound. by apply /ssrnat.ltP.
      ++ by apply /ssrnat.ltP.
   * assert (sum_f_R0 (fun i : nat =>
                          (INR (m ^ i) * u0 ^ i / INR (2 ^ i))%Re)  (m - 1) = 
             sum_f_R0 (fun i : nat => ((INR m * u0 / INR 2)^i)%Re) (m-1)).
     { apply sum_eq. intros.
       rewrite !pow_INR. rewrite [in RHS]Rpow_mult_distr.
       rewrite Rpow_mult_distr. rewrite -Rinv_pow. nra.
       simpl; nra.
     } rewrite H2. clear H2.
     assert ((m - 1)%nat = (Init.Nat.pred m)). { by rewrite -subn1. } rewrite H2.
     pose proof (GP_finite (INR m * u0 / INR 2) (Init.Nat.pred m) ).
     apply pow_invert_eq in H3.
     ++ rewrite H3.
        assert ((Init.Nat.pred m + 1)%coq_nat = m). { rewrite -subn1. admit. } rewrite H4.
        assert (((INR m * u0 * / ( INR m * u0 / INR 2 - 1)) *  
                  ((INR m * u0 / INR 2) ^ m - 1) < 2)%Re -> (1 +
                  INR m * u0 *
                  (((INR m * u0 / INR 2) ^ m - 1) /
                   (INR m * u0 / INR 2 - 1)) < 3)%Re).
        { intros. nra. } apply H5. clear H5.
        assert ((INR m * u0 * / (INR m * u0 / INR 2 - 1) *
                    ((INR m * u0 / INR 2) ^ m - 1))%Re = 
                 (INR m * u0 * / (1 - INR m * u0 / INR 2) *
                    (1 - (INR m * u0 / INR 2) ^ m ))%Re).
        { assert ((INR m * u0 / INR 2 - 1)%Re = (- ((1 - INR m * u0 / INR 2)))%Re).
          { nra. } rewrite H5.
          assert (((INR m * u0 / INR 2)^m - 1)%Re = (- ((1 - (INR m * u0 / INR 2)^m)))%Re).
          { nra. } rewrite H6. 
          rewrite -Ropp_inv_permute. 
          + nra.
          + pose proof (ratio_gt_0 H).
            assert ((0< (1 - INR m * u0 / INR 2))%Re -> 
                    (1 - INR m * u0 / INR 2)%Re <> 0%Re).
            { nra. } apply H8. unfold u0. apply H7.
        } rewrite H5.
        replace 2%Re with (2 * 1)%Re by nra.
        apply Rmult_lt_compat.
        -- apply Rmult_le_pos.
           ** apply Rmult_le_pos; try apply pos_INR; try (unfold u0; simpl;nra). 
              unfold u0. apply default_rel_ge_0.
           ** apply Rlt_le, Rinv_0_lt_compat. replace (1* 1)%Re with 1%Re by nra.  by apply ratio_gt_0. 
        -- assert (((INR m * u0 / INR 2) ^ m <= 1)%Re -> 
                    (0 <= 1 - (INR m * u0 / INR 2) ^ m)%Re).
           { nra. }  apply H6.
           assert (1%Re = (1^m)%Re). { by rewrite pow1. } rewrite H7.
           apply pow_incr. split.
           ** apply Rmult_le_pos.
              +++ apply Rmult_le_pos; try apply pos_INR; try (unfold u0;simpl;nra).
                  unfold u0. apply default_rel_ge_0.
              +++ simpl;nra.
           ** assert ((0 < (1 - INR m * u0 / INR 2))%Re -> 
                        (INR m * u0 / INR 2 <= 1)%Re).
              { nra. } apply H8. by apply ratio_gt_0. 
        --  assert (2%Re = ((2 * (1 - INR m * u0 / INR 2)) * / (1 - INR m * u0 / INR 2))%Re ).
            { match goal with |-context[(_ = (?a * ?b) * ?c)%Re]=>
                replace ((a*b)*c)%Re with (a * (b * c))%Re by nra
              end. rewrite Rinv_r.
              nra.
              pose proof (ratio_gt_0 H).
              assert ((0< (1 - INR m * u0 / INR 2))%Re -> 
                    (1 - INR m * u0 / INR 2)%Re <> 0%Re).
              { nra. } apply H7. unfold u0. apply H6. 
            } rewrite H6.
            apply Rmult_lt_compat_r.
            ** by apply Rinv_0_lt_compat,ratio_gt_0. 
            ** replace (INR 2) with 2%Re by (simpl;nra).
               assert ((2 * (1 - INR m * u0 / 2))%Re = (2 - INR m * u0)%Re).
               { nra. } rewrite H7.
               assert ((INR m * u0 < 1)%Re -> (INR m * u0 < 2 - INR m * u0)%Re).
               { nra. } apply H8. admit.
               (*apply Rlt_le_trans with
               (INR (Z.to_nat (Z.pow_pos 2 23)) * u0).
               +++ apply Rmult_lt_compat_r. unfold u0;simpl;nra.
                   apply lt_INR;lia.
               +++  rewrite INR_IZR_INZ. 
                    assert ((Z.of_nat (Z.to_nat (Z.pow_pos 2 23))) = Z.pow_pos 2 23).
                    { lia. } rewrite H9. unfold u0;simpl;nra. *)
         -- assert ( (0 < (INR m * u0 / INR 2) ^ m)%Re ->
                     (1 - (INR m * u0 / INR 2) ^ m < 1)%Re).
            { nra. } apply H6. apply x_pow_gt_0. 
            apply Rmult_lt_0_compat.
            ** apply Rmult_lt_0_compat.
               +++ apply lt_0_INR. lia.
               +++ unfold u0;simpl. apply default_rel_gt_0.
            ** simpl;nra.
     ++ pose proof (ratio_gt_0 H).
        assert ((0< (1 - INR m * u0 / INR 2))%Re -> 
                    0%Re <> (INR m * u0 / INR 2 - 1)%Re).
        { nra. } apply H5. unfold u0. apply H4.
Admitted.


Lemma n_bound {ty} {n:nat}:
  (n.+1 < 2 ^ Z.to_nat (fprec ty))%nat ->
  (sqrt
   (F' ty / 2 /
    (INR n.+1 * (1 + default_rel ty) ^ n.+1)) <=
 F' ty / 2 /
 (INR n.+1 * (1 + default_rel ty) ^ n.+1))%Re.
Proof.
intros.
apply sqrt_full_le.
assert ((F' ty / 2 /
           (INR n.+1 *
            (1 + default_rel ty) ^ n.+1))%Re = 
         ((F' ty) * / (2 * (INR n.+1 * (1 + default_rel ty) ^ n.+1)))%Re).
{ rewrite Rinv_mult_distr. nra. nra.
  apply Rmult_integral_contrapositive. split.
  + apply not_0_INR. lia.
  + apply pow_nonzero. 
    assert ((0 <  default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
    { nra. } apply H0, default_rel_gt_0.
} rewrite H0.
apply pow_invert.
+ apply Rmult_lt_0_compat. nra.
  apply Rmult_lt_0_compat. apply lt_0_INR. lia.
  apply pow_lt. apply Rplus_lt_0_compat. nra. apply default_rel_gt_0.
+ apply Rle_trans with 
  ((2 * INR n.+1) * 3)%Re.
  - assert ((1 * (2 *(INR n.+1 * (1 + default_rel ty) ^ n.+1)))%Re = 
            ((2 * INR n.+1) * (1 + default_rel ty) ^ n.+1)%Re).
    { nra. } rewrite H1.
    apply Rmult_le_compat_l.
    * apply Rmult_le_pos; try nra. apply Rlt_le, lt_0_INR. lia.
    * apply Rlt_le.
      assert ((((1 + default_rel ty) ^ n.+1 - 1) < 2)%Re -> 
              ((1 + default_rel ty) ^ n.+1 < 3)%Re).
      { nra. } apply H2. by apply delta_bound .
  - assert ((2 * INR n.+1 * 3)%Re = (6 * INR n.+1)%Re).
    { nra. } rewrite H1. 
    apply Rle_trans with 
    (6 * INR (2 ^ Z.to_nat (fprec ty)))%Re.
    * apply Rmult_le_compat_l. nra. apply Rlt_le.
      apply lt_INR. by apply /ssrnat.ltP. 
    * unfold F'. unfold fmax, default_rel.
      assert ((1 - 2 * (/ 2 * bpow Zaux.radix2 (- fprec ty + 1)))%Re = 
              (1 - bpow Zaux.radix2 (- fprec ty + 1))%Re).
      { nra. } rewrite H2. 
      rewrite Rmult_minus_distr_l. rewrite Rmult_1_r.
      assert ( ((6 * INR (2 ^ Z.to_nat (fprec ty)) + bpow Zaux.radix2 (femax ty) *
                     bpow Zaux.radix2 (- fprec ty + 1))%Re <= 
                bpow Zaux.radix2 (femax ty))%Re -> 
              (6 * INR (2 ^ Z.to_nat (fprec ty)) <=
               bpow Zaux.radix2 (femax ty) -
               bpow Zaux.radix2 (femax ty) * bpow Zaux.radix2 (- fprec ty + 1))%Re).
      { nra. } apply H3. admit.
Admitted.

(** State the forward error theorem **)
Theorem jacobi_forward_error_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  (n.+1 < 2 ^ Z.to_nat (fprec ty))%nat ->
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  x != 0 ->
  (forall (v1 v2: 'cV[ftype ty]_n.+1)
          (xy : ftype ty * ftype ty),
    In xy
      (combine
         (vec_to_list_float n.+1 v1)
         (vec_to_list_float n.+1 v2)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\ 
      (Rabs (FT2R (fst (xy))) <= sqrt ((F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1)))%Re /\
      (Rabs (FT2R (snd (xy))) <= sqrt ((F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1)))%Re) ->
  
   let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
   let delta := default_rel ty in
   let rho := (((1 + g ty n.+1) * (1 + delta) * g ty n.+1 +
                delta * (1 + g ty n.+1) + g ty n.+1 + 1) * R)%Re in
   let d_mag := (((1 + g ty n.+1) * (1 + delta) * g ty n.+1 +
                   delta * (1 + g ty n.+1) + g ty n.+1) *
                  (R * vec_inf_norm (x_fix x b_real A)) +
                  ((g ty n.+1 * (1 + delta) + delta) *
                   (vec_inf_norm (A1_diag A_real) *
                    vec_inf_norm b_real) +
                   (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                   (1 + delta) * vec_inf_norm (A1_diag A_real)) +
                  g1 ty n.+1 (n.+1 - 1))%Re in 

  (rho < 1)%Re ->
   A_real \in unitmx ->
  (forall i : 'I_n.+1, FT2R_mat A i i <> 0%Re) ->
  forall x0: 'cV[ftype ty]_n.+1, 
  forall k:nat,
  (f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + ((1 - rho^k) / (1 - rho))* d_mag)%Re.
Proof.
intro Hbound. intros.
induction k.
+ simpl. nra.
+ simpl.
  assert (((1 - rho * rho ^ k) / (1 - rho))%Re = 
           (rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re).
  { assert ((rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re = 
            (rho * ((1 - rho ^ k) / (1 - rho)) + (1 - rho) * / (1 - rho))%Re).
    { rewrite Rinv_r; nra. } rewrite H4. clear H4.
    assert ((rho * ((1 - rho ^ k) / (1 - rho)) +
                  (1 - rho) * / (1 - rho))%Re = 
             (( (rho * (1 - rho ^ k)) * / (1 - rho))%Re + 
              (1 - rho) * / (1 - rho))%Re).
    { nra. } rewrite H4. clear H4.
    rewrite -Rmult_plus_distr_r. nra.
  } rewrite H4. 
  rewrite Rmult_plus_distr_r.
  assert ((rho * rho ^ k * f_error 0 b x0 x A +
            (rho * ((1 - rho ^ k) / (1 - rho)) * d_mag + 1 * d_mag))%Re = 
           (rho * (rho ^ k * f_error 0 b x0 x A +
                        (1 - rho ^ k) / (1 - rho) * d_mag) + d_mag)%Re).
  { nra. } rewrite H5.
  apply Rle_trans with (rho * f_error k b x0 x A + d_mag)%Re.
  - unfold f_error. 
    assert (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                 x_fix x (FT2R_mat b) A = 
             (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
               x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A) +
             (x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A -
              x_fix x (FT2R_mat b) A)).
    { by rewrite add_vec_distr_2. } rewrite H6. clear H6.
    apply Rle_trans with 
    (vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                       x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A ) +
     vec_inf_norm ((x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) A -
                      x_fix x (FT2R_mat b) A)))%Re.
    * apply /RleP. apply triang_ineq.
    * apply Rle_trans with 
      (vec_inf_norm
         (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
          x_fix (FT2R_mat (X_m_jacobi k x0 b A)) 
            (FT2R_mat b) A) +
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
               { nra. } rewrite H6. unfold R2.
               rewrite sub_vec_comm_1.
               rewrite -vec_inf_norm_opp. unfold f_error. rewrite -x_fixpoint.
               +++ apply Rle_refl.
               +++ unfold x. rewrite mulmxA.
                  assert (FT2R_mat A *m A_real^-1 = 1).
                  { fold A_real. by rewrite mulmxV . }
                  rewrite H7. by rewrite mul1mx /b_real.
               +++ apply H3.
         -- auto.
      ++ eapply Rle_trans.
         -- apply Rle_trans with 
            ((vec_inf_norm 
              (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
             vec_inf_norm 
              (diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
               x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                    (FT2R_mat b) A)) + 
              R2 * f_error k b x0 x A)%Re.
             ** apply Rplus_le_compat_r.
                assert ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                            x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) A) = 
                        (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                            diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
                        (diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
                          x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) A)).
               { by rewrite add_vec_distr_2. } rewrite H6.
               apply /RleP.
               apply triang_ineq.
             ** apply Rplus_le_compat_r.
                +++ apply Rplus_le_compat.
                    --- simpl. unfold jacobi_iter. 
                        apply Rle_trans with 
                          ((vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                            vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) * g ty n.+1 +
                               g1 ty n.+1 (n.+1 - 1))%Re.
                        *** pose proof (@vec_norm_diag ty n). 
                            assert (A1_diag (FT2R_mat A) = FT2R_mat (A1_inv_J A)).
                            { apply matrixP. unfold eqrel. intros. rewrite !mxE. 


 admit. }
                            rewrite H7. apply H6. intros.
                            specialize (H0 (A1_inv_J A) (b -f A2_J A *f X_m_jacobi k x0 b A)).
                            by apply H0.
                        *** assert (FT2R_mat (A1_inv_J A) = A1_diag A_real).
                            { apply matrixP. unfold eqrel. intros. rewrite !mxE /=.
                              admit.
                            } rewrite H6. apply Rplus_le_compat_r.
                            apply Rmult_le_compat_r.
                            apply g_pos.
                            apply Rmult_le_compat_l.
                            apply /RleP. apply vec_norm_pd.
                            assert ((vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                                  (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) <=
                                    (vec_inf_norm (FT2R_mat b) + vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                    (default_rel ty))).
                            { apply vec_float_sub. intros.
                              specialize (H0 b (A2_J A *f X_m_jacobi k x0 b A) xy H7).
                              destruct H0 as [Hf1 [Hf2 [Ha1 Ha2]]].   
                              repeat split; try apply Hf1; try apply Hf2;
                              (apply Rle_trans with
                                (sqrt
                                   (F' ty / 2 /
                                    (INR n.+1 * (1 + default_rel ty) ^ n.+1)))%Re; try apply Ha1; try apply Ha2;
                                try apply n_bound). by []. by [].
                            } apply reverse_triang_ineq in H7.
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
                                      { intros. nra. } apply H8. by apply /RleP.
                                 ---- apply Rplus_le_compat_r.
                                      assert (vec_inf_norm
                                                  (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)) = 
                                              vec_inf_norm (- (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)))).
                                      { by rewrite vec_inf_norm_opp. } rewrite H8.
                                      apply /RleP. apply triang_ineq.
                            ++++ apply Rmult_le_compat_r.
                                 ---- apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                 ---- apply Rplus_le_compat_l.
                                      assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                                      { apply matrix_vec_mult_bound_corollary.  admit. }
                                      apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                                      **** rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                                           apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                                           +++++ apply reverse_triang_ineq in H8.
                                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                                 { intros. nra. } apply H9. apply /RleP. apply H8.
                                           +++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                                  replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                                      **** apply Rle_refl.
                    --- unfold x_fix. rewrite diag_matrix_vec_mult_diff .
                        apply Rle_trans with
                        (vec_inf_norm (A1_diag (FT2R_mat A)) *
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
                                 { by rewrite add_vec_distr_2. } rewrite H6. clear H6.
                                 apply /RleP. apply triang_ineq.
         -- assert (FT2R_mat b -
                         FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                         (FT2R_mat b -
                          A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A))  =
                     - (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                        A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A)) ).
             { rewrite add_vec_distr_4. by rewrite sub_vec_comm_1. auto. } rewrite H6. clear H6.
             rewrite -vec_inf_norm_opp. rewrite -RplusE.
             rewrite Rmult_plus_distr_l. eapply Rle_trans.
             ** apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                apply Rplus_le_compat.
                +++ apply /RleP. apply vec_float_sub.
                    intros. 
                    specialize (H0 b (A2_J A *f X_m_jacobi k x0 b A) xy H6).
                    destruct H0 as [Hf1 [Hf2 [Ha1 Ha2]]].   
                    repeat split; try apply Hf1; try apply Hf2;
                    (apply Rle_trans with
                                (sqrt
                                   (F' ty / 2 /
                                    (INR n.+1 * (1 + default_rel ty) ^ n.+1)))%Re; try apply Ha1; try apply Ha2;
                    try by apply n_bound).
                +++ assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite H6. apply /RleP. apply matrix_vec_mult_bound_corollary.
                    intros. admit.
             ** rewrite !ft2r_mat_equiv .
                eapply Rle_trans.
                +++ apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                    rewrite -!RmultE -!RplusE. apply Rmult_le_compat_l.
                    --- apply /RleP. apply vec_norm_pd.
                    --- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                        apply default_rel_ge_0. 
                        apply Rplus_le_compat_l.
                        apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                        *** rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                            assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                           { apply matrix_vec_mult_bound_corollary.  admit. }
                            apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                            ++++ apply reverse_triang_ineq in H6.
                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                 { intros. nra. } apply H7. apply /RleP. apply H6.
                            ++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                    replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                        *** apply Rle_refl.
               +++ assert ((vec_inf_norm (A1_diag A_real) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) * 1 +
                              (vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty) * g ty n.+1 +
                             g1 ty n.+1 (n.+1 - 1) +
                             vec_inf_norm (A1_diag (FT2R_mat A)) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty +
                              (matrix_inf_norm (FT2R_mat (A2_J A)) *
                               vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                               g ty n.+1 + g1 ty n.+1 (n.+1 - 1))) +
                             R2 * f_error k b x0 x A)%Re = 
                          ((( (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                              default_rel ty * (1 + g ty n.+1) + g ty n.+1) *
                              (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (FT2R_mat (A2_J A)))) *
                              vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))) +
                           ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                            (vec_inf_norm (A1_diag A_real) * vec_inf_norm (FT2R_mat b)) +
                           ( (1+ g ty n.+1) * g1 ty n.+1 (n.+1 - 1) * (1 + default_rel ty)) *
                            (vec_inf_norm (A1_diag A_real)) ) + g1 ty n.+1 (n.+1 - 1)) + 
                           R2 * f_error k b x0 x A)%Re).
                   { fold A_real. nra. } rewrite H6. clear H6. fold R2.
                   assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite -H6. fold A_real. fold R2. fold b_real.
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
                    (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                        default_rel ty * (1 + g ty n.+1) + 
                        g ty n.+1) * R2 *
                       (f_error k b x0 x A +
                            vec_inf_norm (x_fix x b_real A_real)) +
                       ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                        (vec_inf_norm (A1_diag A_real) *
                         vec_inf_norm b_real) +
                        (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                        (1 + default_rel ty) *
                        vec_inf_norm (A1_diag A_real)) +
                       g1 ty n.+1 (n.+1 - 1) + R2 * f_error k b x0 x A )%Re.
                    --- repeat apply Rplus_le_compat_r.
                        repeat apply Rmult_le_compat_l.
                        *** apply Rmult_le_pos.
                            ++++ apply Rplus_le_le_0_compat.
                                 ---- apply Rplus_le_le_0_compat.
                                      **** repeat apply Rmult_le_pos.
                                           +++++ apply Rplus_le_le_0_compat. nra. apply g_pos.
                                           +++++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                           +++++ apply g_pos.
                                      **** apply Rmult_le_pos.
                                           +++++ apply default_rel_ge_0.
                                           +++++ apply Rplus_le_le_0_compat. nra. apply g_pos.
                                 ---- apply g_pos.
                            ++++ unfold R2. apply Rmult_le_pos.
                                 ---- apply /RleP. apply vec_norm_pd.
                                 ---- apply /RleP. apply matrix_norm_pd.
                        *** apply H7.
                    --- assert ((((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                                  default_rel ty * (1 + g ty n.+1) + 
                                  g ty n.+1) * R2 *
                                 (f_error k b x0 x A +
                                  vec_inf_norm (x_fix x b_real A_real)) +
                                 ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  vec_inf_norm (A1_diag A_real)) +
                                 g1 ty n.+1 (n.+1 - 1) + R2 * f_error k b x0 x A)%Re = 
                                ((((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                                  default_rel ty * (1 + g ty n.+1) +   g ty n.+1 + 1) * R2) *
                                f_error k b x0 x A + 
                                (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                                  default_rel ty * (1 + g ty n.+1) + g ty n.+1) *
                                  (R2  * vec_inf_norm (x_fix x b_real A_real)) +
                                  ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  vec_inf_norm (A1_diag A_real)) +
                                 g1 ty n.+1 (n.+1 - 1)))%Re).
                        { nra. } rewrite H8. clear H8. fold delta. fold rho. fold d_mag.
                        unfold f_error. fold b_real. fold A_real. apply Rle_refl.
  - apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * by apply rho_ge_0.
    * nra.
Admitted. 
  





(*
(** State the forward error theorem **)
Theorem jacobi_forward_error_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  x != 0 ->
  (forall (v1 v2: 'cV[ftype ty]_n.+1)
          (xy : ftype ty * ftype ty),
    In xy
      (combine
         (vec_to_list_float n.+1 v1)
         (vec_to_list_float n.+1 v2)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\ 
      (Rabs (FT2R (fst (xy))) <= (F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1))%Re /\
      (Rabs (FT2R (snd (xy))) <= (F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1))%Re) ->
  
   let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
   let delta := default_rel ty in
   let rho := (((1 + g ty n.+1) * (1 + delta) * g ty n.+1 +
                delta * (1 + g ty n.+1) + g ty n.+1 + 1) * R)%Re in
   let d_mag := (((1 + g ty n.+1) * (1 + delta) * g ty n.+1 +
                   delta * (1 + g ty n.+1) + g ty n.+1) *
                  (R * vec_inf_norm (x_fix x b_real A_real)) +
                  ((g ty n.+1 * (1 + delta) + delta) *
                   (vec_inf_norm (A1_diag A_real) *
                    vec_inf_norm b_real) +
                   (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                   (1 + delta) * vec_inf_norm (A1_diag A_real)) +
                  g1 ty n.+1 (n.+1 - 1))%Re in 

  (rho < 1)%Re ->
   A_real \in unitmx ->
  (forall i : 'I_n.+1, FT2R_mat A i i <> 0%Re) ->
  forall x0: 'cV[ftype ty]_n.+1, 
  forall k:nat,
  (f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + ((1 - rho^k) / (1 - rho))* d_mag)%Re.
Proof.
induction k.
+ simpl. nra.
+ simpl.
  assert (((1 - rho * rho ^ k) / (1 - rho))%Re = 
           (rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re).
  { assert ((rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re = 
            (rho * ((1 - rho ^ k) / (1 - rho)) + (1 - rho) * / (1 - rho))%Re).
    { rewrite Rinv_r; nra. } rewrite H4. clear H4.
    assert ((rho * ((1 - rho ^ k) / (1 - rho)) +
                  (1 - rho) * / (1 - rho))%Re = 
             (( (rho * (1 - rho ^ k)) * / (1 - rho))%Re + 
              (1 - rho) * / (1 - rho))%Re).
    { nra. } rewrite H4. clear H4.
    rewrite -Rmult_plus_distr_r. nra.
  } rewrite H4. 
  rewrite Rmult_plus_distr_r.
  assert ((rho * rho ^ k * f_error 0 b x0 x A +
            (rho * ((1 - rho ^ k) / (1 - rho)) * d_mag + 1 * d_mag))%Re = 
           (rho * (rho ^ k * f_error 0 b x0 x A +
                        (1 - rho ^ k) / (1 - rho) * d_mag) + d_mag)%Re).
  { nra. } rewrite H5.
  apply Rle_trans with (rho * f_error k b x0 x A + d_mag)%Re.
  - unfold f_error. 
    assert (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                 x_fix x (FT2R_mat b) (FT2R_mat A) = 
             (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
               x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A)) +
             (x_fix (FT2R_mat (X_m_jacobi k x0 b A)) (FT2R_mat b) (FT2R_mat A) -
              x_fix x (FT2R_mat b) (FT2R_mat A))).
    { by rewrite add_vec_distr_2. } rewrite H6. clear H6.
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
               { nra. } rewrite H6. unfold R2.
               rewrite sub_vec_comm_1.
               rewrite -vec_inf_norm_opp. unfold f_error. rewrite -x_fixpoint.
               +++ apply Rle_refl.
               +++ unfold x. rewrite mulmxA.
                  assert (FT2R_mat A *m A_real^-1 = 1).
                  { fold A_real. by rewrite mulmxV . }
                  rewrite H7. by rewrite mul1mx /b_real.
               +++ apply H3.
         -- auto.
      ++ eapply Rle_trans.
         -- apply Rle_trans with 
            ((vec_inf_norm 
              (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
             vec_inf_norm 
              (diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
               x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                    (FT2R_mat b) (FT2R_mat A))) + 
              R2 * f_error k b x0 x A)%Re.
             ** apply Rplus_le_compat_r.
                assert ((FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                            x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) (FT2R_mat A)) = 
                        (FT2R_mat (X_m_jacobi k.+1 x0 b A) - 
                            diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) +
                        (diag_matrix_vec_mult_R (A1_diag (FT2R_mat A))
                             (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A)) -
                          x_fix (FT2R_mat (X_m_jacobi k x0 b A))
                              (FT2R_mat b) (FT2R_mat A))).
               { by rewrite add_vec_distr_2. } rewrite H6.
               apply /RleP.
               apply triang_ineq.
             ** apply Rplus_le_compat_r.
                +++ apply Rplus_le_compat.
                    --- simpl. unfold jacobi_iter. 
                        apply Rle_trans with 
                          ((vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                            vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A))) * g ty n.+1 +
                               g1 ty n.+1 (n.+1 - 1))%Re.
                        *** pose proof (@vec_norm_diag ty n). 
                            assert (A1_diag (FT2R_mat A) = FT2R_mat (A1_inv_J A)).
                            { apply matrixP. unfold eqrel. intros. rewrite !mxE. admit. }
                            rewrite H7. apply H6. 
                            admit.
                        *** assert (FT2R_mat (A1_inv_J A) = A1_diag A_real).
                            { apply matrixP. unfold eqrel. intros. rewrite !mxE /=.
                              admit.
                            } rewrite H6. apply Rplus_le_compat_r.
                            apply Rmult_le_compat_r.
                            apply g_pos.
                            apply Rmult_le_compat_l.
                            apply /RleP. apply vec_norm_pd.
                            assert ((vec_inf_norm (FT2R_mat (b -f A2_J A *f X_m_jacobi k x0 b A) -
                                                  (FT2R_mat b - FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) <=
                                    (vec_inf_norm (FT2R_mat b) + vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A))) *
                                    (default_rel ty))).
                            { apply vec_float_sub. intros.
                              specialize (H0 b (A2_J A *f X_m_jacobi k x0 b A) xy H7).
                              apply H0.
                            } apply reverse_triang_ineq in H7.
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
                                      { intros. nra. } apply H8. by apply /RleP.
                                 ---- apply Rplus_le_compat_r.
                                      assert (vec_inf_norm
                                                  (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)) = 
                                              vec_inf_norm (- (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A)))).
                                      { by rewrite vec_inf_norm_opp. } rewrite H8.
                                      apply /RleP. apply triang_ineq.
                            ++++ apply Rmult_le_compat_r.
                                 ---- apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                 ---- apply Rplus_le_compat_l.
                                      assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                                      { apply matrix_vec_mult_bound_corollary.  admit. }
                                      apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                                      **** rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                                           apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                                           +++++ apply reverse_triang_ineq in H8.
                                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                                 { intros. nra. } apply H9. apply /RleP. apply H8.
                                           +++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                                  replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                                      **** apply Rle_refl.
                    --- unfold x_fix. rewrite diag_matrix_vec_mult_diff .
                        apply Rle_trans with
                        (vec_inf_norm (A1_diag (FT2R_mat A)) *
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
                                 { by rewrite add_vec_distr_2. } rewrite H6. clear H6.
                                 apply /RleP. apply triang_ineq.
         -- assert (FT2R_mat b -
                         FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                         (FT2R_mat b -
                          A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A))  =
                     - (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                        A2_J_real (FT2R_mat A) *m FT2R_mat (X_m_jacobi k x0 b A)) ).
             { rewrite add_vec_distr_4. by rewrite sub_vec_comm_1. auto. } rewrite H6. clear H6.
             rewrite -vec_inf_norm_opp. rewrite -RplusE.
             rewrite Rmult_plus_distr_l. eapply Rle_trans.
             ** apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                apply Rmult_le_compat_l. apply /RleP. apply vec_norm_pd.
                apply Rplus_le_compat.
                +++ apply /RleP. apply vec_float_sub.
                    intros. 
                    specialize (H0 b (A2_J A *f X_m_jacobi k x0 b A) xy H6).
                    apply H0.
                +++ assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite H6. apply /RleP. apply matrix_vec_mult_bound_corollary.
                    intros. admit.
             ** rewrite !ft2r_mat_equiv .
                eapply Rle_trans.
                +++ apply Rplus_le_compat_r. apply Rplus_le_compat_l.
                    rewrite -!RmultE -!RplusE. apply Rmult_le_compat_l.
                    --- apply /RleP. apply vec_norm_pd.
                    --- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                        apply default_rel_ge_0. 
                        apply Rplus_le_compat_l.
                        apply Rle_trans with 
                                      ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))%Re.
                        *** rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                            assert (vec_inf_norm (FT2R_mat (A2_J A *f X_m_jacobi k x0 b A) -
                                                 (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A))) <=
                                               ((matrix_inf_norm (FT2R_mat (A2_J A)) * vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)))
                                                * g ty n.+1 + g1 ty n.+1 (n.+1 - 1))%Re).
                           { apply matrix_vec_mult_bound_corollary.  admit. }
                            apply Rle_trans with
                                           (vec_inf_norm (FT2R_mat (A2_J A) *m FT2R_mat (X_m_jacobi k x0 b A)) +
                                            (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                             vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                             g ty n.+1 + g1 ty n.+1 (n.+1 - 1)))%Re.
                            ++++ apply reverse_triang_ineq in H6.
                                 assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
                                 { intros. nra. } apply H7. apply /RleP. apply H6.
                            ++++ match goal with |-context[(_ <= ?p + ?a * ?b * ?c + ?d)%Re]=>
                                    replace (p + a * b * c + d)%Re with (p + (a * b * c + d))%Re by nra
                                 end. apply Rplus_le_compat_r. apply /RleP. apply submult_prop.
                        *** apply Rle_refl.
               +++ assert ((vec_inf_norm (A1_diag A_real) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) * 1 +
                              (vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty) * g ty n.+1 +
                             g1 ty n.+1 (n.+1 - 1) +
                             vec_inf_norm (A1_diag (FT2R_mat A)) *
                             ((vec_inf_norm (FT2R_mat b) +
                               (matrix_inf_norm (FT2R_mat (A2_J A)) *
                                vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                                (1 + g ty n.+1) + g1 ty n.+1 (n.+1 - 1))) *
                              default_rel ty +
                              (matrix_inf_norm (FT2R_mat (A2_J A)) *
                               vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A)) *
                               g ty n.+1 + g1 ty n.+1 (n.+1 - 1))) +
                             R2 * f_error k b x0 x A)%Re = 
                          ((( (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                              default_rel ty * (1 + g ty n.+1) + g ty n.+1) *
                              (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (FT2R_mat (A2_J A)))) *
                              vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))) +
                           ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                            (vec_inf_norm (A1_diag A_real) * vec_inf_norm (FT2R_mat b)) +
                           ( (1+ g ty n.+1) * g1 ty n.+1 (n.+1 - 1) * (1 + default_rel ty)) *
                            (vec_inf_norm (A1_diag A_real)) ) + g1 ty n.+1 (n.+1 - 1)) + 
                           R2 * f_error k b x0 x A)%Re).
                   { fold A_real. nra. } rewrite H6. clear H6. fold R2.
                   assert (A2_J_real (FT2R_mat A) = FT2R_mat (A2_J A)).
                    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
                       by case: (x1 == y :> nat).
                    } rewrite -H6. fold A_real. fold R2. fold b_real.
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
                    (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                        default_rel ty * (1 + g ty n.+1) + 
                        g ty n.+1) * R2 *
                       (f_error k b x0 x A +
                            vec_inf_norm (x_fix x b_real A_real)) +
                       ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                        (vec_inf_norm (A1_diag A_real) *
                         vec_inf_norm b_real) +
                        (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                        (1 + default_rel ty) *
                        vec_inf_norm (A1_diag A_real)) +
                       g1 ty n.+1 (n.+1 - 1) + R2 * f_error k b x0 x A )%Re.
                    --- repeat apply Rplus_le_compat_r.
                        repeat apply Rmult_le_compat_l.
                        *** apply Rmult_le_pos.
                            ++++ apply Rplus_le_le_0_compat.
                                 ---- apply Rplus_le_le_0_compat.
                                      **** repeat apply Rmult_le_pos.
                                           +++++ apply Rplus_le_le_0_compat. nra. apply g_pos.
                                           +++++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
                                           +++++ apply g_pos.
                                      **** apply Rmult_le_pos.
                                           +++++ apply default_rel_ge_0.
                                           +++++ apply Rplus_le_le_0_compat. nra. apply g_pos.
                                 ---- apply g_pos.
                            ++++ unfold R2. apply Rmult_le_pos.
                                 ---- apply /RleP. apply vec_norm_pd.
                                 ---- apply /RleP. apply matrix_norm_pd.
                        *** apply H7.
                    --- assert ((((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                                  default_rel ty * (1 + g ty n.+1) + 
                                  g ty n.+1) * R2 *
                                 (f_error k b x0 x A +
                                  vec_inf_norm (x_fix x b_real A_real)) +
                                 ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  vec_inf_norm (A1_diag A_real)) +
                                 g1 ty n.+1 (n.+1 - 1) + R2 * f_error k b x0 x A)%Re = 
                                ((((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                                  default_rel ty * (1 + g ty n.+1) +   g ty n.+1 + 1) * R2) *
                                f_error k b x0 x A + 
                                (((1 + g ty n.+1) * (1 + default_rel ty) * g ty n.+1 +
                                  default_rel ty * (1 + g ty n.+1) + g ty n.+1) *
                                  (R2  * vec_inf_norm (x_fix x b_real A_real)) +
                                  ((g ty n.+1 * (1 + default_rel ty) + default_rel ty) *
                                  (vec_inf_norm (A1_diag A_real) *
                                   vec_inf_norm b_real) +
                                  (1 + g ty n.+1) * g1 ty n.+1 (n.+1 - 1) *
                                  (1 + default_rel ty) *
                                  vec_inf_norm (A1_diag A_real)) +
                                 g1 ty n.+1 (n.+1 - 1)))%Re).
                        { nra. } rewrite H8. clear H8. fold delta. fold rho. fold d_mag.
                        unfold f_error. fold b_real. fold A_real. apply Rle_refl.
  - apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * by apply rho_ge_0.
    * nra.
Admitted. 
  

*)









End WITHNANS.
