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

Definition rho_def  {t: type} (A: matrix t) (b: vector t) :=
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in  
  let x:= mulmx (A_real^-1) b_real in
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
       


Lemma jacobi_iteration_bound_monotone:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k k': nat),
   (k <= k')%nat ->
   jacobi_preconditions A b acc k ->
   jacobi_preconditions A b acc k'.
Proof. 
Admitted.

From Flocq Require Import Binary.
Require Import finite_lemmas_additional.


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
    ((X_m_jacobi k x0 b A) -f (X_m_jacobi k.-1 x0 b A)).
   


Lemma iter_length {ty} n (A: matrix ty) (b: vector ty) (x: vector ty):
  length b = length A ->
  length x = length A ->
  length
  (Nat.iter n
     (fun x0 : vector ty =>
      diagmatrix_vector_mult
        (invert_diagmatrix (diag_of_matrix A))
        (vector_sub b
           (matrix_vector_mult (remove_diag A) x0)))
     x) = length A.
Proof.
induction n.
+ by simpl.
+ simpl. repeat rewrite !map_length combine_length.
  unfold matrix_vector_mult. rewrite map_length.
  rewrite !map_length !seq_length /matrix_rows_nat /=.
  intros. rewrite H. by rewrite !Nat.min_id.
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
  @vector_inj _ (resid (jacobi_n A b x0 k.-1)) n.+1 = 
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
      rewrite !mxE. rewrite inord_val.
      


      unfold diag_of_matrix.
       



unfold jacob_list_fun_model.jacobi_iter.
      repeat rewrite !combine_length !map_length !seq_length.
      unfold diagmatrix_vector_mult, map2, uncurry.
      repeat rewrite !combine_length !map_length !seq_length.




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



Lemma jacobi_iteratio_bound {t: type} :
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