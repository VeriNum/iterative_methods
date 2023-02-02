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

Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
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


(*

Definition rho_def  {t: type} (A: matrix t) (b: vector t) :=
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in  
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

*)


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


(*

Definition d_mag_def {t: type} (A: matrix t) (b: vector t) :=
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in  
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

*)



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


(** finiteness of dot product **)
Lemma dotprod_finite {t: type} (v : vector t):
is_finite (fprec t) (femax t)
  (dotprod v v) = true.
Proof.
induction v.
+ by simpl.
+ unfold dotprod. admit.
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

Lemma residual_is_finite {t: type} :
 forall (A: matrix t) (b: vector t),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  forall k,
  is_finite (fprec t) (femax t)
  (norm2 (resid (jacobi_n A b x0 k))) = true.
Admitted.

(**
Heqv_l : v_l = rev (resid (jacobi_n A b x0 k.-1))
H1 : rev (vec_to_list_float n.+1 (vector_inj v_l n.+1)) =
     resid (jacobi_n A b x0 k.-1)
______________________________________(1/1)
((vec_inf_norm (FT2R_mat (vector_inj v_l n.+1)))² <=
 (rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho))) ^ 2)%Re

**)

Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).

Definition A1_J {ty} {n:nat} (A: 'M[ftype ty]_n.+1) : 'cV[ftype ty]_n.+1 :=
  \col_i (A i i).


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
{ admit. } specialize (H H0).
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


(**
Lemma vec_succ_err {t: type} (A: matrix t) (b: vector t) (k:nat) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let n := (length A).-1 in
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let x0' := @vector_inj _ x0 n.+1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b' x0' x A' in
  (vec_inf_norm (FT2R_mat ((X_m_jacobi k.+1 x0' b' A') -f (X_m_jacobi k x0' b' A'))) <=
    (rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))%Re.
Proof.
intros.
pose proof (@vec_float_sub_1 _ t n).
specialize (H (X_m_jacobi k.+1 x0' b' A') (X_m_jacobi k x0' b' A')).
assert (forall xy : ftype t * ftype t,
             In xy
               (combine
                  (vec_to_list_float n.+1
                     (X_m_jacobi k.+1 x0' b' A'))
                  (vec_to_list_float n.+1
                     (X_m_jacobi k x0' b' A'))) ->
             is_finite (fprec t) (femax t) xy.1 = true /\
             is_finite (fprec t) (femax t) xy.2 = true /\
             is_finite (fprec t) (femax t)
               (BPLUS t xy.1 (BOPP t xy.2)) = true).
{ admit. } specialize (H H0).
apply reverse_triang_ineq in H.
apply Rle_trans with
(vec_inf_norm
      (FT2R_mat (X_m_jacobi k.+1 x0' b' A') -
       FT2R_mat (X_m_jacobi k x0' b' A')) * (1 + default_rel t))%Re.
+ rewrite Rmult_plus_distr_l Rmult_1_r.
  assert (forall x y z:R, (x - y <= z)%Re -> (x <= y + z)%Re).
  { intros. nra. } apply H1.
  by apply /RleP.
+ apply Rmult_le_compat_r.
  - apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  - assert (FT2R_mat (X_m_jacobi k.+1 x0' b' A') -
                FT2R_mat (X_m_jacobi k x0' b' A') = 
            (FT2R_mat (X_m_jacobi k.+1 x0' b' A') - x) - 
            (FT2R_mat (X_m_jacobi k x0' b' A') - x)).
    { by rewrite add_vec_distr_5. } rewrite H1.
    eapply Rle_trans.
    * apply /RleP. apply triang_ineq .
    * rewrite -vec_inf_norm_opp. rewrite -RplusE.
      assert (x = x_fix x b_real A_real).
      { admit. } rewrite H2.
      assert (vec_inf_norm
                 (FT2R_mat (X_m_jacobi k.+1 x0' b' A') -
                  x_fix x b_real A_real) = f_error k.+1 b' x0' x A').
      { by rewrite /f_error. }
      assert (vec_inf_norm
                 (FT2R_mat (X_m_jacobi k x0' b' A') -
                  x_fix x b_real A_real) = f_error k b' x0' x A').
      { by rewrite /f_error. } rewrite H3 H4.
      pose proof (@jacobi_forward_error_bound _ t n A' b').
      assert (forall i : 'I_n.+1,
                is_finite (fprec t) (femax t) (A' i i) = true) by admit.
      assert (x != 0 ) by admit.
      assert ((rho < 1)%Re) by admit.
      assert (FT2R_mat A' \in unitmx) by admit.  
      assert (forall i : 'I_n.+1,
              is_finite (fprec t) (femax t)
                (BDIV t (Zconst t 1) (A' i i)) = true) by admit.
     assert (forall (k : nat) (i : 'I_n.+1),
                is_finite (fprec t) (femax t)
                  (X_m_jacobi k x0' b' A' i ord0) = true) by admit. 
     specialize (H5 H6 H7 H8 H9 H10 x0' H11).
     assert ((f_error k.+1 b' x0' x A' <= rho^k.+1 * (f_error 0 b' x0' x A') + 
                    ((1 - rho^k.+1) / (1 - rho))* d_mag)%Re).
     { by apply (H5 k.+1). }
     assert ((f_error k b' x0' x A' <= rho^k * (f_error 0 b' x0' x A') + 
                    ((1 - rho^k) / (1 - rho))* d_mag)%Re).
     { by apply (H5 k). } 
     eapply Rle_trans.
     ++ apply Rle_trans with
        ((rho ^ k.+1 * f_error 0 b' x0' x A' +
            (1 - rho ^ k.+1) / (1 - rho) * d_mag) + 
        (rho ^ k * f_error 0 b' x0' x A' +
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
**)

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
+ apply norm2_vec_inf_norm_rel; admit.
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
            { admit. } specialize (H0 H1).
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


(*
Lemma residual_bound {t: type} (A: matrix t) (b: vector t) (k:nat) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let n := (length A).-1 in
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let x0' := @vector_inj _ x0 n.+1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b' x0' x A' in
  let resid := residual_math A' x0' b' in
  let v_l := (vec_to_list_float n.+1 (resid k)) in
  (rho < 1)%Re ->
  (Rabs (FT2R (norm2 (rev v_l))) <= 
    INR n.+1 * 
    (Rsqr (vec_inf_norm (FT2R_mat (A1_J A')) * 
      ((rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
        * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
      (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
Proof.
intros.
eapply Rle_trans.
+ apply norm2_vec_inf_norm_rel; admit.
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
            (diag_matrix_vec_mult_R (FT2R_mat (A1_J A'))
            (FT2R_mat (X_m_jacobi k.+1 x0' b' A' -f
                          X_m_jacobi k x0' b' A'))) +
          vec_inf_norm (FT2R_mat (A1_J A')) *
          vec_inf_norm (FT2R_mat (X_m_jacobi k.+1 x0' b' A' -f
                          X_m_jacobi k x0' b' A')) * 
          g t n.+1 +  g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
         -- pose proof (@vec_norm_diag _ t n (A1_J A') 
                        (X_m_jacobi k.+1 x0' b' A' -f
                          X_m_jacobi k x0' b' A')).
            assert (forall xy : ftype t * ftype t,
                     In xy
                       (combine
                          (vec_to_list_float n.+1 (A1_J A'))
                          (vec_to_list_float n.+1
                             (X_m_jacobi k.+1 x0' b' A' -f
                              X_m_jacobi k x0' b' A'))) ->
                     is_finite (fprec t) (femax t) xy.1 = true /\
                     is_finite (fprec t) (femax t) xy.2 = true /\
                     is_finite (fprec t) (femax t)
                       (BMULT t xy.1 xy.2) = true).
            { admit. } specialize (H0 H1).
            assert ((vec_inf_norm
                     (FT2R_mat
                        (diag_vector_mult (A1_J A')
                           (X_m_jacobi k.+1 x0' b' A' -f
                            X_m_jacobi k x0' b' A')) -
                      diag_matrix_vec_mult_R
                        (FT2R_mat (A1_J A'))
                        (FT2R_mat
                           (X_m_jacobi k.+1 x0' b' A' -f
                            X_m_jacobi k x0' b' A'))) <=
                   vec_inf_norm (FT2R_mat (A1_J A')) *
                   vec_inf_norm
                     (FT2R_mat
                        (X_m_jacobi k.+1 x0' b' A' -f
                         X_m_jacobi k x0' b' A')) * 
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
              assert ((vec_inf_norm (FT2R_mat (A1_J A')) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi k.+1 x0' b' A' -f
                             X_m_jacobi k x0' b' A')) +
                       vec_inf_norm (FT2R_mat (A1_J A')) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi k.+1 x0' b' A' -f
                             X_m_jacobi k x0' b' A')) * 
                       g t n.+1 + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re = 
                      (vec_inf_norm (FT2R_mat (A1_J A')) *
                       vec_inf_norm
                         (FT2R_mat
                            (X_m_jacobi k.+1 x0' b' A' -f
                             X_m_jacobi k x0' b' A')) * ( 1 + g t n.+1) + 
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
*)

(** Lemma in terms of mathcomp **)


Lemma jacobi_iteration_bound {t: type} {n : nat} :
 forall (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (acc: ftype t) (k: nat),
   (*jacobi_preconditions A b acc k -> *)
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
split.
+ admit.
+ exists k. (** dummy for now **)
  repeat split.
  - by [].
  - admit.
  - unfold BCMP.
    rewrite Bcompare_correct. 
    * rewrite Rcompare_Lt; first by [].
      change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
      remember (FT2R acc2) as Gamma.
      assert (FT2R (norm2 (rev (vec_to_list_float n.+1 (resid k)))) = 
              Rabs (FT2R (norm2 (rev (vec_to_list_float n.+1 (resid k)))))).
      { rewrite Rabs_right. nra. apply Rle_ge, norm2_ge_0. }
      rewrite H.
      remember (rho_def A b) as rho.
      remember (d_mag_def A b) as d_mag.
      remember (mulmx ((FT2R_mat A)^-1) (FT2R_mat b)) as x.
      remember (f_error 0 b x0 x A) as e_0.
      apply Rle_lt_trans with
      (INR n.+1 * 
        (Rsqr (vec_inf_norm (FT2R_mat (A1_J A)) * 
          ((rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
            * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
          (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
      ++ pose proof (@residual_bound t n A b k).
         assert ((rho_def A b < 1)%Re) by admit.
         specialize (H0 H1). unfold resid,x0. rewrite Heqe_0 Heqrho Heqd_mag Heqx.
         unfold x0. apply H0.
      ++  admit. 
    * admit.
    * admit.
Admitted.


Lemma jacobi_iteration_bound_lowlevel {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
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
remember (length A).-1 as n.
remember (@matrix_inj _ A n.+1 n.+1) as A'.
remember (@vector_inj _ b n.+1) as b'.
specialize (H0 A' b' acc k).
destruct H0 as [Hacc H0].
unfold jacobi_preconditions in H.
destruct H as [HlA [Hlab H]]. 
split.
+ by unfold acc2.
+ destruct H0 as [j [Hjrel H0]].
  exists j. split; try by [].
  intros. destruct H0 as [Hf Hlt]. split.
  - intros.  specialize (Hf i H0).
    pose proof (@vector_residual_equiv t A b x0 i).
    assert (length b = length A) by (symmetry; apply  Hlab).
    assert (length x0 = length A).
    { unfold x0. by rewrite !repeat_length. }
    assert ((0 < length A)%coq_nat) by apply HlA.
    specialize (H1 H2 H3 H4).
    rewrite HeqA' Heqb' in Hf. rewrite -Heqn in H1.
    assert (vector_inj x0 n.+1 = \col_(j < n.+1) (Zconst t 0)).
    { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
      by rewrite nth_repeat.
    } rewrite H5 in H1. rewrite -H1 in Hf.
    pose proof (@v_equiv t).
    specialize (H6 (resid (jacobi_n A b x0 i)) n).
    assert (length (resid (jacobi_n A b x0 i)) = n.+1).
    { repeat rewrite /matrix_vector_mult !map_length combine_length.
      rewrite !map_length. unfold jacobi_n. rewrite iter_length.
      rewrite !seq_length /matrix_rows_nat H2 !Nat.min_id.
      rewrite Heqn prednK. by []. by apply /ssrnat.ltP.
      by []. by []. 
    }
    specialize (H6 H7).
    rewrite H6. 
    assert ((\col_j0 vector_inj
                      (resid (jacobi_n A b x0 i))
                      n.+1 j0 ord0) = 
            vector_inj (resid (jacobi_n A b x0 i)) n.+1).
    { apply /matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H8. apply Hf.
  - pose proof (@vector_residual_equiv t A b x0 j).
    assert (length b = length A) by (symmetry; apply  Hlab).
    assert (length x0 = length A).
    { unfold x0. by rewrite !repeat_length. }
    assert ((0 < length A)%coq_nat) by apply HlA.
    specialize (H0 H1 H2 H3).
    rewrite HeqA' Heqb' in Hlt. rewrite -Heqn in H0.
    assert (vector_inj x0 n.+1 = \col_(j < n.+1) (Zconst t 0)).
    { apply /matrixP. unfold eqrel. intros. rewrite !mxE.
      by rewrite nth_repeat.
    } rewrite H4 in H0. rewrite -H0 in Hlt.
    pose proof (@v_equiv t).
    specialize (H5 (resid (jacobi_n A b x0 j)) n).
    assert (length (resid (jacobi_n A b x0 j)) = n.+1).
    { repeat rewrite /matrix_vector_mult !map_length combine_length.
      rewrite !map_length. unfold jacobi_n. rewrite iter_length.
      rewrite !seq_length H1 !Nat.min_id.
      rewrite Heqn prednK. by []. by apply /ssrnat.ltP.
      by []. by [].
    }
    specialize (H5 H6).
    rewrite H5. 
    assert ((\col_j0 vector_inj
                      (resid (jacobi_n A b x0 j))
                      n.+1 j0 ord0) = 
            vector_inj (resid (jacobi_n A b x0 j)) n.+1).
    { apply /matrixP. unfold eqrel. intros. by rewrite !mxE. }
    rewrite H7. apply Hlt.
Qed.

(*
Lemma FT2R_mat_dissoc {t} {n:nat} (v1 v2: 'cV[ftype t]_n.+1):
  FT2R_mat (v1 -f v2) = (FT2R_mat v1 - FT2R_mat v2) * 


Lemma residual_inf_norm_le {t: type} :
 forall (A: matrix t) (b: vector t) (k:nat),
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
  let v_l := rev (resid (jacobi_n A b x0 k.-1)) in
  let rho := rho_def A b in
  let d_mag := d_mag_def A b in
  let n := (length A).-1 in
  let e_0 := f_error 0 (vector_inj b n.+1)
                          (vector_inj (repeat (Zconst t 0) (length b))  n.+1) ((FT2R_mat (matrix_inj A n.+1 n.+1))^-1 *m 
                           FT2R_mat (vector_inj b n.+1))  (matrix_inj A n.+1 n.+1) in    
  ((vec_inf_norm (FT2R_mat (vector_inj v_l n.+1)))² <=
  (rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho))) ^ 2)%Re
Proof.

intros.
unfold v_l.
assert ((vector_inj (rev (resid (jacobi_n A b x0 k.-1))) n.+1)



unfold resid.
unfold jacobi_residual. 
(** assertion that jacobi residual = x_k+1 - x_k **)

*)




Lemma old_jacobi_iteration_bound {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
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
unfold jacobi_preconditions in H.
destruct H as [Hla [Hlab [HfA [Hxneq0 [Hrho [HAinv [Hinvf [Hsolf [HcG1 [HcG2 Hk]]]]]]]]]].
repeat split.
+ apply finite_is_finite. unfold acc2. apply HcG2.
+ exists k.-1. repeat split.
  - apply leq_pred.
  - intros. apply finite_is_finite.
    apply residual_is_finite .
    (** use the compatibility relation from norms **)
  - unfold BCMP.
    rewrite Bcompare_correct; simpl.
    * 
      rewrite Rcompare_Lt; first by [].
      (** use k to do the proof **)
      change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
      remember (rho_def A b) as rho.
      remember (d_mag_def A b) as d_mag.
      remember (length A).-1 as n.
      remember (f_error 0 (vector_inj b n.+1)
                          (vector_inj (repeat (Zconst t 0) (length b))  n.+1) ((FT2R_mat (matrix_inj A n.+1 n.+1))^-1 *m 
                           FT2R_mat (vector_inj b n.+1))  (matrix_inj A n.+1 n.+1)) as e_0. 
      unfold acc2.
      assert (FT2R (norm2 (resid (jacobi_n A b x0 k.-1))) = 
              Rabs (FT2R (norm2 (resid (jacobi_n A b x0 k.-1))))).
      { rewrite Rabs_right. nra. apply Rle_ge, norm2_ge_0. }
      rewrite H.
      pose proof (@norm2_vec_inf_norm_rel t n _).
      remember (rev (resid (jacobi_n A b x0 k.-1))) as v_l.
      specialize (H0 (@vector_inj _ v_l n.+1)). 
      assert (rev (vec_to_list_float n.+1 (vector_inj v_l n.+1)) = resid (jacobi_n A b x0 k.-1)).
      { apply nth_ext with (Zconst t 0) (Zconst t 0).
        + rewrite rev_length. rewrite length_veclist.
          repeat rewrite !map_length !combine_length. 
          admit.
        + intros. admit.
      } rewrite -H1.
      eapply Rle_lt_trans.
      ++ apply H0. 
         -- admit. (** finiteness of each element in the list **)
         -- rewrite H1. apply residual_is_finite . (** finiteness of 2-norm of the residual **)
      ++ eapply Rle_lt_trans.
         -- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
            ** apply Rplus_le_le_0_compat. nra. apply g_pos.
            ** apply Rmult_le_compat_l. apply pos_INR.
               
               apply Rle_trans with 
               ((rho^k * (1+ rho) * (e_0 - d_mag /  (1 - rho)))^2)%Re.
               +++ admit.
               +++ apply Rle_refl.
         -- 


 admit. (** show that before k, residual > acc2 **)
    * apply residual_is_finite .
    * unfold acc2. apply HcG2.
Admitted.

End WITH_NANS.