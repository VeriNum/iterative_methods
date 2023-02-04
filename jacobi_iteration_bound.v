Require Import vcfloat.VCFloat.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp.analysis Require Import Rstruct.

Require Import floatlib jacob_list_fun_model.
Require Import fma_real_func_model fma_floating_point_model.
Require Import inf_norm_properties common.
Require Import norm_compat.

Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Require Import fma_floating_point_model.

Section WITH_NANS.

Context {NANS: Nans}.

Definition f_error {NANS: Nans} {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A_real in
  vec_inf_norm (FT2R_mat x_k - x).

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

(** x = A_1^{-1} (b - A_2 x) 
  ||x || = ||A^-1 || ||b||
         \leq (||A|| ||A^-1|| ||b||) / ||A||
          = k (A) ||b|| / || A ||

  ||x|| \leq ( k(A) ||b||) / ||A||
  https://www.maths.manchester.ac.uk/~higham/talks/claode13.pdf 
  https://link.springer.com/content/pdf/10.1007/978-94-017-1116-6_9.pdf
  https://nhigham.com/2021/06/08/bounds-for-the-matrix-condition-number/


**)

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
  
(*
Definition jacobi_preconditions {t: type}
  (A: matrix t) (b: vector t) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in
  
  let x:= mulmx (A_real^-1) b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let x0' := @vector_inj _ x0 n.+1 in
  
  (** dimension of A is positive **)
  (0 < length A)%coq_nat /\
  (length A = length b) /\
  (** Finiteness of A **)
  (forall i j, Binary.is_finite _ _ (A' i j) = true) /\
  (** x <> 0 **)
  x != 0 /\
  (** constant for the contraction mapping **)
  (rho < 1)%Re /\
  (** Invertibility of A **)
  A_real \in unitmx /\
  (** Finiteness of the inverse of diagonal elements of A **)
  (forall i : 'I_n.+1,
    Binary.is_finite (fprec t) (femax t)
      (BDIV t (Zconst t 1) (A' i i)) = true) /\
  (** Finiteness of solution vector at each iteration **)
  (forall k:nat, 
      forall i, Binary.is_finite _ _ ((X_m_jacobi k x0' b' A') i ord0) = true) /\
  (** Constraint on Gamma **)
  (Rsqr (g1 t n.+1 (n.+1 - 1)) < FT2R (accuracy))%Re /\
  (** Gamma is finite **)
  Binary.is_finite _ _ (BMULT t accuracy accuracy) = true /\
  (** constraint on k **)
  (k > Z.to_N (Zceil (ln (((1- rho) * sqrt (INR n.+1) * (1 + g t n.+1) * (f_error 0 b' x0' x A' - d_mag / (1-rho))) /
                          (sqrt (FT2R (accuracy)  - g1 t n.+1 (n.+1 - 1)))) /
                      ln (1 / rho))))%coq_nat.
       
*)


Definition A1_J {ty} {n:nat} (A: 'M[ftype ty]_n.+1) : 'cV[ftype ty]_n.+1 :=
  \col_i (A i i).


Definition k_min {NANS: Nans} {t: type} {n:nat} (A : 'M[ftype t]_n.+1)
  (b : 'cV[ftype t]_n.+1) (acc : ftype t) :=
  let rho := rho_def A b in
  let d_mag := d_mag_def A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := @f_error _ _ _ 0 b x0 x A in
  let Gamma := FT2R (BMULT t acc acc) in
  let delta := default_rel t in
  Z.to_nat (Zceil (Rlog (1 / rho)%Re 
             ((e_0 - d_mag / (1 - rho)) * (1 + rho) /
                ((sqrt
                    ((Gamma - g1 t n.+1 (n.+1 - 1)%coq_nat) /
                     INR n.+1 / (1 + g t n.+1)) -
                  g1 t n.+1 (n.+1 - 1)%coq_nat) /
                 (1 + g t n.+1) /
                 vec_inf_norm (FT2R_mat (A1_J A)) /
                 (1 + delta) -
                 2 * d_mag / (1 - rho)))%Re)).



Definition jacobi_preconditions_math {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in 
  let x:= mulmx (A_real^-1) b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  (** Finiteness of A **)
  (forall i j, Binary.is_finite _ _ (A i j) = true) /\
  (** x <> 0 **)
  x != 0 /\
  (** constant for the contraction mapping **)
  (0 < rho /\ rho < 1)%Re /\
  (** Invertibility of A **)
  A_real \in unitmx /\
  (** Finiteness of the inverse of diagonal elements of A **)
  (forall i : 'I_n.+1,
    Binary.is_finite (fprec t) (femax t)
      (BDIV t (Zconst t 1) (A i i)) = true) /\
  (** Finiteness of solution vector at each iteration **)
  (*(forall k:nat, 
      forall i, Binary.is_finite _ _ ((X_m_jacobi k x0 b A) i ord0) = true) /\
  *)
(** Constraint on Gamma **)
  (g1 t n.+1 (n.+1 - 1)%coq_nat <= FT2R (BMULT t accuracy accuracy))%Re /\
  (** Gamma is finite **)
  Binary.is_finite _ _ (BMULT t accuracy accuracy) = true /\
  (** constraint on k **)
  (k_min A b accuracy < k)%coq_nat.

(** Use: lower case gamma **)

Definition jacobi_preconditions {t: type}
  (A: matrix t) (b: vector t) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
   False.

Lemma jacobi_iteration_bound_monotone:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k k': nat),
   (k <= k')%nat ->
   jacobi_preconditions A b acc k ->
   jacobi_preconditions A b acc k'.
Proof. 
Admitted.

From Flocq Require Import Binary.
Require Import finite_lemmas_additional.

(*
Lemma jacobi_iteration_bound_corollaries:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
   matrix_cols A (matrix_rows A) /\
   Forall (Forall finite) A /\
   Forall finite (invert_diagmatrix (diag_of_matrix A)) /\
   Forall finite b /\ finite acc.
Proof. 
intros. unfold jacobi_preconditions in H.
destruct H as [Hla [Hlab [HfA [Hxneq0 [Hrho [HAinv [Hinvf [Hsolf [HcG1 [HcG2 Hk]]]]]]]]]].
repeat split.
+ unfold matrix_cols, matrix_rows. simpl.
  apply Forall_forall.
  intros.

  admit.
+ apply Forall_nth. intros.
  apply Forall_nth. intros.
  specialize (HfA (@inord (length A).-1 i) (@inord (length A).-1 i0)).
  apply finite_is_finite. rewrite !mxE in HfA.
  rewrite !inordK in HfA.
  - admit.
  - rewrite prednK. by apply /ssrnat.ltP. by apply /ssrnat.ltP.
  - rewrite prednK.
    assert (length (nth i A d) = length A).
    { admit . } rewrite H1 in H0. by apply /ssrnat.ltP.
   by apply /ssrnat.ltP.
+ apply Forall_nth. intros.
  unfold invert_diagmatrix. 
  rewrite (nth_map_inrange (Zconst t 0)).
  - specialize (Hinvf (@inord (length A).-1 i)).
    rewrite !mxE in Hinvf. unfold diag_of_matrix.
    rewrite nth_map_seq.
    * unfold matrix_index. rewrite inordK in Hinvf.
      ++ apply finite_is_finite. apply Hinvf.
      ++ rewrite prednK. rewrite !map_length seq_length /matrix_rows_nat in H.
         by apply /ssrnat.ltP. by apply /ssrnat.ltP.
    * unfold matrix_rows_nat. 
      by rewrite !map_length seq_length /matrix_rows_nat in H.
  - rewrite !map_length seq_length.
    by rewrite !map_length seq_length in H.
+ specialize (Hsolf k.+1).
  apply Forall_nth. intros.
  specialize (Hsolf (@inord (length A).-1 i)).
  apply finite_is_finite.  
  remember (length A).-1 as m. clear Hk HcG2 HcG1.
  rewrite mxE in Hsolf.
  rewrite !nth_vec_to_list_float in Hsolf.
  rewrite inord_val in Hsolf. 
  apply bmult_overflow_implies in Hsolf.
  destruct Hsolf as [Hsolf1 Hsolf2].
  unfold sub_mat in Hsolf2. rewrite !mxE in Hsolf2.
  apply Bminus_bplus_opp_implies  in Hsolf2.
  apply bplus_overflow_implies in Hsolf2.
  destruct Hsolf2 as [Hsolf21 Hsfolf22].
  rewrite inordK in Hsolf21.
  -  admit. (** apply Hsolf21 **)
  - rewrite Heqm. rewrite prednK; try by apply /ssrnat.ltP.
    rewrite Hlab. by apply /ssrnat.ltP.
  - rewrite inordK;
    (try rewrite Heqm;try rewrite prednK; try by apply /ssrnat.ltP;
     try rewrite Hlab;try  by apply /ssrnat.ltP); try by apply /ssrnat.ltP.
  - rewrite inordK;
    (try rewrite Heqm;try rewrite prednK; try by apply /ssrnat.ltP;
     try rewrite Hlab;try  by apply /ssrnat.ltP); try by apply /ssrnat.ltP.
+ apply finite_is_finite.
  apply bmult_overflow_implies in HcG2. by destruct HcG2.
Admitted.
*)

Require Import fma_is_finite.
(** finiteness of dot product **)
Lemma dotprod_finite {t: type} (v : vector t):
is_finite (fprec t) (femax t)
  (dotprod v v) = true.
Proof.
pose proof (@fma_is_finite _ t v v).
assert (length v = length v).
{ lia. } specialize (H H0).
specialize (H (dotprod v v)).
apply H; admit.



Admitted.


Lemma norm2_ge_0 {t: type} (v : vector t):
  (0 <= FT2R (norm2 v))%Re.
Proof.
unfold norm2.
induction v.
+ simpl. nra.
+ unfold dotprod.
  assert (combine (a :: v) (a :: v) = (a, a) :: combine v v).
  { unfold combine;auto. } rewrite H.
  simpl. admit.
Admitted.

(*
Lemma residual_is_finite {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  forall k,
  is_finite (fprec t) (femax t)
  (norm2 (resid (jacobi_n A b x0 k))) = true.
Admitted.
*)


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).



Definition residual_math {t}  {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat):=
  diag_vector_mult (A1_J A) 
    ((X_m_jacobi k.+1 x0 b A) -f (X_m_jacobi k x0 b A)).
  
Print diag_vector_mult.

Lemma A1_equiv {t: type} :
 forall (A: matrix t) (x : nat),
 (x < length A)%coq_nat ->
 nth x (diag_of_matrix A) (Zconst t 0) =
 nth x (nth x A []) (Zconst t 0). 
Proof.
intros. 
by rewrite  /diag_of_matrix nth_map_seq ?/matrix_index ?/matrix_rows_nat.
Qed.


Lemma residual_is_finite {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat):
  let resid := residual_math A x0 b in
  is_finite (fprec t) (femax t)
    (norm2
       (rev
          (vec_to_list_float n.+1 (resid k)))) = true.
Proof.
unfold norm2. apply dotprod_finite.
Qed.


Require Import fma_dot_mat_model.

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
                        (Zconst t 0) = BMULT t (A1_inv_J A' (inord x) ord0)
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

Require Import vec_sum_inf_norm_rel fma_jacobi_forward_error.

Lemma add_vec_distr_5 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a- b) - (c - b) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma dotprod_finite_implies {t: type} (v : vector t):
is_finite (fprec t) (femax t) (dotprod v v) = true ->
(forall x, In x v -> 
           is_finite (fprec t) (femax t) x = true).
Admitted.
  

Lemma vec_succ_err {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b x0 x A in
  (vec_inf_norm (FT2R_mat ((X_m_jacobi k.+1 x0 b A) -f (X_m_jacobi k x0 b A))) <=
    (rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))%Re.
Proof.
intros.
pose proof (@vec_float_sub_1 _ t n).
specialize (H (X_m_jacobi k.+1 x0 b A) (X_m_jacobi k x0 b A)).
assert (forall xy : ftype t * ftype t,
             In xy
               (combine
                  (vec_to_list_float n.+1
                     (X_m_jacobi k.+1 x0 b A))
                  (vec_to_list_float n.+1
                     (X_m_jacobi k x0 b A))) ->
             is_finite (fprec t) (femax t) xy.1 = true /\
             is_finite (fprec t) (femax t) xy.2 = true /\
             is_finite (fprec t) (femax t)
               (BPLUS t xy.1 (BOPP t xy.2)) = true).
{ (** if the  residual is finite then 
      x_k+1 - x_k is finite
  **)
  intros. 
  pose proof (@residual_is_finite  t n A x0 b k).
  unfold norm2 in H1. 
  pose proof (@dotprod_finite_implies t).
  specialize (H2 (rev
             (vec_to_list_float n.+1
                (residual_math A x0 b k))) H1).
  (*pose proof (@residual_is_finite  t n A x0 b k.+1).
  unfold norm2 in H3.  *)
  pose proof (@dotprod_finite_implies t).
  specialize (H3 (rev
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
           (rev
              (vec_to_list_float n.+1
                 (diag_vector_mult 
                    (A1_J A)
                    (X_m_jacobi k.+1 x0 b A -f
                     X_m_jacobi k x0 b A))))).
  { apply nth_In. rewrite Heqv_l in Hm.
    rewrite rev_length length_veclist .
    by rewrite rev_length combine_length !length_veclist Nat.min_id in Hm.
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
      apply bmult_overflow_implies in H3.
      destruct H3 as [Hf1 Hf2].
      rewrite mxE in Hf2.
      apply Bminus_bplus_opp_implies in Hf2.
      rewrite Heqv_l in Hnth. rewrite rev_nth in Hnth.
      rewrite combine_length !length_veclist Nat.min_id in Hnth.
      rewrite combine_nth in Hnth.
      

      apply bplus_overflow_implies  in Hf2.
      rewrite inord_val in Hf2.
      destruct Hf2 as [Hf21 Hf22].
      
      




 admit.
    - by rewrite inordK; rewrite  Heqv_l  combine_length !length_veclist Nat.min_id in Hm;
      apply /ssrnat.ltP.
    
    



 admit.
  + rewrite  Heqv_l  combine_length !length_veclist Nat.min_id in Hm.
    by apply /ssrnat.ltP.
  + rewrite length_veclist.
    by rewrite  Heqv_l  combine_length !length_veclist Nat.min_id in Hm.

    



apply dotprod_finite_implies in H1.


 admit. } specialize (H H0).
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
      { admit. } rewrite H2.
      assert (vec_inf_norm
                 (FT2R_mat (X_m_jacobi k.+1 x0 b A) -
                  x_fix x b_real A_real) = f_error k.+1 b x0 x A).
      { by rewrite /f_error. }
      assert (vec_inf_norm
                 (FT2R_mat (X_m_jacobi k x0 b A) -
                  x_fix x b_real A_real) = f_error k b x0 x A).
      { by rewrite /f_error. } rewrite H3 H4.
      pose proof (@jacobi_forward_error_bound _ t n A b).
      assert (forall i : 'I_n.+1,
                is_finite (fprec t) (femax t) (A i i) = true) by admit.
      assert (x != 0 ) by admit.
      assert ((rho < 1)%Re) by admit.
      assert (FT2R_mat A \in unitmx) by admit.  
      assert (forall i : 'I_n.+1,
              is_finite (fprec t) (femax t)
                (BDIV t (Zconst t 1) (A i i)) = true) by admit.
     assert (forall (k : nat) (i : 'I_n.+1),
                is_finite (fprec t) (femax t)
                  (X_m_jacobi k x0 b A i ord0) = true) by admit. 
     (** also implied by finiteness of residual **)
     specialize (H5 H6 H7 H8 H9 H10 x0 H11).
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
            { nra. } rewrite H14. rewrite Rinv_r; last by nra.
            rewrite Rmult_1_r.
            assert (((rho ^ k * e_0 * (1 - rho)) * / (1- rho))%Re = 
                     ( (rho^k * e_0) * ((1 - rho) * / (1- rho)))%Re).
            { nra. } rewrite H15. rewrite Rinv_r; nra.
          } rewrite H14. clear H14. nra.
        } rewrite H14. clear H14.
        assert ((rho ^ k.+1 * (1 - rho) * e_0 +
                  (1 - rho ^ k.+1) * d_mag +
                  rho ^ k * (1 - rho) * e_0 +
                  (1 - rho ^ k) * d_mag)%Re = 
                (rho ^ k * (1+ rho) * (1 - rho) * e_0 + 
                  2* d_mag  - rho^k * (1 + rho) * d_mag)%Re).
        { simpl. nra. } rewrite H14. clear H14.
        assert ((rho ^ k * (1 + rho) * (1 - rho) * e_0 +
                  2 * d_mag - rho ^ k * (1 + rho) * d_mag)%Re = 
                ((rho ^ k * (1 + rho) * ((1-rho) * e_0 - d_mag)) + 2 * d_mag)%Re).
        { nra. } rewrite H14. clear H14.
        rewrite Rmult_plus_distr_r.
        assert ((rho ^ k * (1 + rho) *
                    ((1 - rho) * e_0 - d_mag) * / (1 - rho))%Re =
                (rho ^ k * (1 + rho) * 
                (e_0 * ( (1 - rho) * / (1 - rho)) - d_mag * /(1 - rho)))%Re).
        { nra. } rewrite H14. clear H14. rewrite Rinv_r; last by nra.
        rewrite Rmult_1_r. nra.
Admitted.



(*** Bound for the residual ***)
Lemma residual_bound {t: type} {n:nat} 
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0:=  \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b x0 x A in
  let resid := residual_math A x0 b in
  let v_l := (vec_to_list_float n.+1 (resid k)) in
  (rho < 1)%Re ->
  (Rabs (FT2R (norm2 (rev v_l))) <= 
    INR n.+1 * 
    (Rsqr (vec_inf_norm (FT2R_mat (A1_J A)) * 
      ((rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
        * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
      (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
Proof.
intros.
eapply Rle_trans.
+ apply norm2_vec_inf_norm_rel.
  - admit.
  - apply residual_is_finite.
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
         Search diag_vector_mult.
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
                     is_finite (fprec t) (femax t) xy.1 = true /\
                     is_finite (fprec t) (femax t) xy.2 = true /\
                     is_finite (fprec t) (femax t)
                       (BMULT t xy.1 xy.2) = true).
            { admit. (** Implied by finiteness of the residual **) } specialize (H0 H1).
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
           { by apply /RleP. } apply reverse_triang_ineq in H2.
           match goal with |-context[(_ <= ?a + ?b + ?c)%Re]=>
            replace (a + b + c)%Re with (a + (b + c))%Re by nra
           end.
           assert (forall x y z:R,  (x - y <= z)%Re -> (x <= y + z)%Re).
           { intros. nra. } apply H3.  by apply /RleP. 
        -- Search diag_matrix_vec_mult_R.
           (** vec_inf_norm_diag_matrix_vec_mult_R **)
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
             { nra. } rewrite H0.
             apply Rplus_le_compat_r. apply Rmult_le_compat_r.
             +++ apply Rplus_le_le_0_compat; try nra; try apply g_pos.
             +++ apply Rmult_le_compat_l. 
                 --- apply /RleP. apply vec_norm_pd.
                 --- apply vec_succ_err.
      ++ apply /RleP. apply vec_norm_pd.
      ++ apply Rplus_le_le_0_compat.
         -- repeat apply Rmult_le_pos.
            ** apply /RleP. apply vec_norm_pd.
            ** apply Rplus_le_le_0_compat.
               +++ repeat apply Rmult_le_pos.
                   --- apply pow_le. by apply rho_ge_0.
                   --- apply Rplus_le_le_0_compat; try nra; try by apply rho_ge_0.
                   --- admit.
               +++ repeat apply Rmult_le_pos.
                   --- nra.
                   --- apply d_mag_ge_0.
                   --- apply Rlt_le. apply Rinv_0_lt_compat. nra.
            ** apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
            ** apply Rplus_le_le_0_compat. nra. apply g_pos.
         -- apply g1_pos.
Admitted.

 Search "Zceil".
Print IZR.
Search"Zlt".

Local Open Scope Z_scope.
Lemma Zceil_INR: forall x:Z,
  (0 < x)%Z ->
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

(** Lemma in terms of mathcomp **)
Lemma zceil_inj: forall x:R,
  (0 < Zceil x)%Z ->
  INR (Z.to_nat (Zceil x)) = x.
Proof.
intros.
rewrite Zceil_INR; last by [].
Search Zceil.
Admitted.

Search "Zceil".
Locate Zceil_IZR.
Close Scope Z_scope.

(*
Lemma zceil_gt_0: forall x:R,
  (0 < x)%Re ->
  (0 < Zceil x).
Proof.
intros. unfold Zceil.
Search (0 < - _)%Z.
apply Z.opp_pos_neg.
pose proof Zceil_le.
specialize (H0 0%Re x).
assert (x = 0 



Admitted.
*)

Require Import float_acc_lems lemmas.



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

Lemma jacobi_iteration_bound {t: type} {n : nat} :
 forall (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (acc: ftype t) (k: nat),
   jacobi_preconditions_math A b acc k -> 
   let acc2 := BMULT t acc acc in
   let x0 := \col_(j < n.+1) (Zconst t 0) in
   let resid := residual_math A x0 b in
   finite acc2 /\ 
   exists j,
    (j <= k)%nat /\
    (forall i, (i <= j)%nat -> finite (norm2 (rev (vec_to_list_float n.+1 (resid i))))) /\
    BCMP t Lt false (norm2 (rev (vec_to_list_float n.+1 (resid j)))) acc2 = false.
    (** rev (_ ) fits perfectly well with norm2_vec_inf_norm_rel **)
Proof.
intros.
unfold jacobi_preconditions_math in H.
destruct H as [HfA [Hneqx [Hrho [HinvA [Hfbdiv [Hfxk [HG [Hfacc Hk]]]]]]]].
split.
+ unfold acc2. by apply finite_is_finite.
+ exists (k_min A b acc).+1. 
  repeat split.
  - by apply /ssrnat.ltP.
  - intros. apply finite_is_finite.
    apply residual_is_finite.
  - unfold BCMP.
    rewrite Bcompare_correct. 
    * rewrite Rcompare_Lt; first by [].
      change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
      remember (FT2R acc2) as Gamma.
      assert (FT2R (norm2 (rev (vec_to_list_float n.+1 (resid (k_min A b acc).+1)))) = 
              Rabs (FT2R (norm2 (rev (vec_to_list_float n.+1 (resid (k_min A b acc).+1)))))).
      { rewrite Rabs_right. nra. apply Rle_ge, norm2_ge_0. }
      rewrite H.
      remember (rho_def A b) as rho.
      remember (d_mag_def A b) as d_mag.
      remember (mulmx ((FT2R_mat A)^-1) (FT2R_mat b)) as x.
      remember (WITH_NANS.f_error 0 b x0 x A) as e_0.
      apply Rle_lt_trans with
      (INR n.+1 * 
        (Rsqr (vec_inf_norm (FT2R_mat (A1_J A)) * 
          ((rho ^ (k_min A b acc).+1 * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
            * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
          (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
      ++ pose proof (@residual_bound t n A b (k_min A b acc).+1).
         assert ((rho_def A b < 1)%Re).
         { rewrite Heqrho in Hrho. apply Hrho. } 
         specialize (H0 H1). unfold resid,x0. rewrite Heqe_0 Heqrho Heqd_mag Heqx.
         unfold x0. apply H0.
      ++ apply Rcomplements.Rlt_minus_r.
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
           + apply Rle_0_minus. by rewrite HeqGamma.
           + apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR; lia.
           + apply Rlt_le. apply Rinv_0_lt_compat. apply Rplus_lt_le_0_compat.
             nra. apply g_pos.
         } rewrite H0. 
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
               +++ admit. (** (e_0 - d_mag / (1 - rho) > 0)%Re **)
               +++ apply Rcomplements.Rlt_div_r;
                   first by (apply Rplus_lt_le_0_compat; try nra; try rewrite Heqrho; by apply rho_ge_0).
                   assert ((rho ^ (k_min A b acc).+1)%Re = (/ / rho ^ (k_min A b acc).+1)%Re).
                   { by rewrite Rinv_inv. }
                   rewrite H1.
                   match goal with |-context[(_ < ?x / ?y / ?z)%Re]=>
                      replace (x / y / z)%Re with (/ ((y * z)  / x))%Re 
                   end. 
                   --- apply Rinv_lt_contravar.
                       *** repeat apply Rmult_lt_0_compat.
                           ++++ admit.
                           ++++ nra.
                           ++++ apply Rinv_0_lt_compat.
                                admit.
                           ++++ apply Rinv_0_lt_compat.
                                apply pow_lt. apply Hrho.
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
                            + assert ( (1 < /rho)%Re -> / rho <> 1%Re). { nra. }
                              apply H2. replace 1%Re with (/1)%Re by nra.
                               apply Rinv_lt_contravar. rewrite Rmult_1_r.
                               apply Hrho. apply Hrho.
                            + apply Rinv_0_lt_compat. apply Hrho.
                            + repeat apply Rmult_lt_0_compat.
                              - admit.
                              - nra.
                              - apply Rinv_0_lt_compat.
                                admit. (** modify the constraint on Gamma **)
                          }
                          rewrite H2.
                          assert ( ((/ rho) ^ (k_min A b acc).+1)%Re = 
                                   Rpower (/rho)%Re (INR (k_min A b acc).+1)).
                          { rewrite Rpower_pow. nra.
                            apply Rinv_0_lt_compat. apply Hrho.
                          }
                          rewrite H3. apply Rpower_lt .
                          ++++ replace 1%Re with (/1)%Re by nra.
                               apply Rinv_lt_contravar. rewrite Rmult_1_r.
                               apply Hrho. 
                               apply Hrho.
                          ++++ apply Rle_lt_trans with (INR (k_min A b acc)).
                               ---- unfold k_min. rewrite Zceil_INR.
                                    rewrite Heqrho Heqe_0 /x0 Heqx Heqd_mag HeqGamma. 
                                    assert ((/ rho_def A b)%Re = (1 / rho_def A b)%Re). { nra. }
                                    rewrite H4. apply Zceil_ub. admit.
                               ---- apply lt_INR. lia.
                   --- rewrite Rinv_div. 
                       match goal with |-context[( _ = ?a / ?b / ?c)%Re]=>
                        replace (a / b / c)%Re with (a * (/b * /c))%Re by nra
                       end. rewrite -Rinv_mult_distr.
                       nra. admit.
                       assert (forall x:R, (0 <= x)%Re -> (1 + x)%Re <> 0%Re).
                       { intros. nra. } apply H2. rewrite Heqrho. by apply rho_ge_0.
          -- apply Rplus_le_le_0_compat; last by apply g1_pos.
             repeat apply Rmult_le_pos.
             ** apply /RleP. apply vec_norm_pd.
             ** apply Rplus_le_le_0_compat.
                +++ repeat apply Rmult_le_pos.
                    --- rewrite Heqrho. by apply rho_ge_0.
                    --- apply pow_le. rewrite Heqrho. by apply rho_ge_0.
                    --- apply Rplus_le_le_0_compat. nra. rewrite Heqrho. by apply rho_ge_0.
                    --- admit. (*** (0 <= e_0 - d_mag / (1 - rho))%Re **)
                +++ repeat apply Rmult_le_pos ; try nra. rewrite Heqd_mag. apply d_mag_ge_0.
                    apply Rlt_le. apply Rinv_0_lt_compat. 
                    apply Rlt_Rminus. apply Hrho.
             ** apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
             ** apply Rplus_le_le_0_compat. nra. apply g_pos.
          -- apply sqrt_pos.
    * apply residual_is_finite.
    * by unfold acc2. 
Admitted.


Lemma jacobi_iteration_bound_lowlevel {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
   jacobi_preconditions_math A' b' acc k ->
   length A = length b ->
   (0 < length A)%coq_nat ->
   let acc2 := BMULT t acc acc in
   let x0 := (repeat  (Zconst t 0) (length b)) in
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
   finite acc2 /\ 
   exists j,
    (j <= k)%nat /\
    let y :=  jacobi_n A b x0 j in
    let r2 := norm2 (resid y) in
    (forall i, (i <= j)%nat -> finite (norm2 (resid (jacobi_n A b x0 i)))) /\
    BCMP t Lt false (norm2 (resid (jacobi_n A b x0 j))) acc2 = false.
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


End WITH_NANS.


