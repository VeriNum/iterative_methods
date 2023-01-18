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


Definition A1_diag {n: nat} (A: 'M[R]_n.+1) : 'cV[R]_n.+1:=
  \col_i (1 / (A i i))%Re.

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
Definition x_fix {n:nat} x b (A: 'M[R]_n.+1) :
  'cV[R]_n.+1 :=
  let r := b - ((A2_J_real A) *m x) in
  diag_matrix_vec_mult_R (A1_diag A) r.

Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A_real in
  vec_inf_norm (FT2R_mat x_k - x).


Definition matrix_of_diag_A1 {ty} {n:nat} (A: 'M[ftype ty]_n.+1) :
 'M[ftype ty]_n.+1 :=
 \matrix_(i, j) 
    (if (i == j :> nat) then (A1_inv_J A i ord0) else (Zconst ty 0)).


Lemma rho_ge_0 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let R := vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real) in
  let delta := default_rel ty in
  let rho := ((g ty n.+1 * (1+ delta) * (1+ g ty n.+1) + delta + delta * g ty n.+1 + g ty n.+1) * R)%Re in
  (0 <= rho)%Re.
Proof.
intros.
unfold rho.
repeat apply Rmult_le_pos.
+ apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rplus_le_le_0_compat.
      ++ repeat apply Rmult_le_pos.
         -- apply g_pos.
         -- unfold delta. apply Rplus_le_le_0_compat. nra.
            apply default_rel_ge_0.
         -- apply Rplus_le_le_0_compat. nra. apply g_pos.
      ++ unfold delta. apply default_rel_ge_0.
    * apply Rmult_le_pos.
      ++ unfold delta. apply default_rel_ge_0.
      ++ apply g_pos.
  - apply g_pos.
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
             ((A (inord x0) (inord x0) * / A (inord x0) (inord x0)) *
              x x0 y)%Re).
    { nra. } rewrite H1. rewrite Rinv_r.
    nra. apply H0.
  } rewrite H1.
  assert (((A (inord x0) (inord x0) * x x0 y))%Re  = 
           (b (inord x0) ord0 -
              \sum_j A2_J_real A (inord x0) j * x j ord0)%Re).   
  { assert (forall x y z:R, (x + y = z)%Re -> (x = z - y)%Re).
    { intros. nra. } apply H2.
    assert ((A (inord x0) (inord x0) * x x0 y +
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

(** State the forward error theorem **)
Theorem jacobi_forward_error_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  x != 0 ->
  (forall (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1)
          (xy : ftype ty * ftype ty) (i : 'I_n.+1),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\ 
      Rabs (FT2R (fst (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1) - default_abs ty) /\
      Rabs (FT2R (snd (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1) - default_abs ty)) ->
  
   let R := vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real) in
   let delta := default_rel ty in
   let rho := ((g ty n.+1 * (1+ delta) * (1+ g ty n.+1) + delta + delta * g ty n.+1 + g ty n.+1) * R)%Re in
   let d_mag := ( g ty n.+1 * (1 + delta) * (1 + g ty n.+1) * R * vec_inf_norm x +
                  (delta + delta * g ty n.+1 + g ty n.+1) * R * vec_inf_norm x +
                  g ty n.+1 * (1 + delta) * vec_inf_norm (A1_diag A_real) * vec_inf_norm b_real  +
                  g ty n.+1 * g1 ty n.+1 (n.+1 - 1)%nat * (1 + delta) * vec_inf_norm (A1_diag A_real) +
                  g1 ty n.+1 (n.+1 - 1)%nat * (1+ delta) * vec_inf_norm (A1_diag A_real) +
                  delta * vec_inf_norm (A1_diag A_real) * vec_inf_norm b_real)%Re in

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
               rewrite -RmultE. rewrite sub_vec_comm_1.
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
                    --- admit.
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
             { rewrite add_vec_distr_4. by rewrite sub_vec_comm_1. } rewrite H6. clear H6.
             rewrite -vec_inf_norm_opp.



 admit.
  - apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * by apply rho_ge_0.
    * nra.
Admitted. 
  












End WITHNANS.

