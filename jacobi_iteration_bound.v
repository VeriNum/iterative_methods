Require Import vcfloat.VCFloat.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp.analysis Require Import Rstruct.
Require Import fma_is_finite dotprod_model.
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


(** As suggested by David:
  ||x|| <= ||D^-1 b || / (1 - rho) 
  [ since ||x || = || (D+ N)^-1 b|| <= ||D^-1 b || / (1 - rho) for rho < 1
**)

Print A1_diag.
Definition d_mag_def_alt {t: type} {n:nat} (A: 'M[ftype t]_n.+1) 
  (b: 'cV[ftype t]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in  
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
                     (vec_inf_norm (A1_diag A_real) * 
                       vec_inf_norm b_real * (/ (1 - rho_def A b))))%Re.

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
  (** constant for the contraction mapping **)
  (0 < rho /\ rho < 1)%Re /\
  (** Invertibility of A **)
  A_real \in unitmx /\
  (** Finiteness of the inverse of diagonal elements of A **)
  (forall i : 'I_n.+1,
    Binary.is_finite (fprec t) (femax t)
      (BDIV t (Zconst t 1) (A i i)) = true) /\
(** Constraint on Gamma **)
  (FT2R (BMULT t accuracy accuracy) >
     g1 t n.+1 (n.+1 - 1)%coq_nat +
     INR n.+1 * (1 + g t n.+1) *
     (g1 t n.+1 (n.+1 - 1)%coq_nat +
      2 * (1 + g t n.+1) * (1 + default_rel t) *
      vec_inf_norm (FT2R_mat (A1_J A)) *
      d_mag_def A b * / (1 - rho_def A b))²)%Re /\
  (** Gamma is finite **)
  Binary.is_finite _ _ (BMULT t accuracy accuracy) = true /\
  (** constraint on k **)
  (k_min A b accuracy < k)%coq_nat /\
  (** lower bound on the initial error **)
  (0 < f_error 0 b x0 x A - d_mag / (1 - rho))%Re.

(** Use: lower case gamma **)

Definition jacobi_preconditions {t: type}
  (A: matrix t) (b: vector t) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
   False.

Lemma jacobi_iteration_bound_monotone:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k k': nat),
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
   (k <= k')%nat ->
   jacobi_preconditions_math A' b' acc k ->
   jacobi_preconditions_math A' b' acc k'.
Proof. 
intros.
unfold jacobi_preconditions_math in H0.
unfold jacobi_preconditions_math.
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

From Flocq Require Import Binary.
Require Import finite_lemmas_additional.

(*
Lemma jacobi_iteration_bound_corollaries:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions_math A b acc k ->
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
(*
F' t = 2^e_max ( 1 - 2^-p)
*)

(**
res_k+1 = A_1 \otimes (x_k+1 \ominus x_k)
x_k+1 = D^-1 \otimes (b \ominus (N \otimes x_k))
**)


(** finiteness of dot product **)
Lemma dotprod_finite {t: type} (v : vector t):
(forall xy : ftype t,
  In xy (rev v) ->
  is_finite (fprec t) (femax t) xy = true /\
  (let n := length (rev v) in
   (Rabs (FT2R xy) <=
    sqrt
      (F' t / 2 /
       (INR n * (1 + default_rel t) ^ n)))%Re)) ->
is_finite (fprec t) (femax t)
  (dotprod v v) = true.
Proof.
intros.
pose proof (@fma_is_finite _ t (rev v) (rev v)).
assert (length (rev v) = length (rev v)).
{ lia. } specialize (H0 H1).
specialize (H0 (dotprod v v)).
pose proof (@fma_dot_prod_rel_fold_right _ t).
specialize (H2 v v).
rewrite -combine_rev in H2; last by [].
assert (fma_dotprod t v v = dotprod v v).
{ by unfold fma_dotprod, dotprod. }
rewrite H3 in H2. specialize (H0 H2).
apply H0.
intros.
repeat split;
try (specialize (H xy.1); apply H;
      destruct xy; apply in_combine_l in H4; auto);
try (specialize (H xy.2); apply H;
      destruct xy; apply in_combine_r in H4; auto).
Qed.


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

Require Import float_acc_lems.


Lemma BMULT_no_overflow_is_finite {NAN: Nans} (t : type): 
  forall (x y : ftype t) 
  (Hx : is_finite _ _ x = true)
  (Hy : is_finite _ _ y = true)
  (Hnov: Bmult_no_overflow t (FT2R x) (FT2R y)),
   Binary.is_finite (fprec t) (femax t) (BMULT t x y) = true.
  
Proof.
intros.
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y) as
  H0.
unfold Bmult_no_overflow in Hnov.
unfold rounded in Hnov.
apply Rlt_bool_true in Hnov.
rewrite Hnov in H0.
destruct H0 as [H01 [H02 H03]].
rewrite H02. by apply /andP.
Qed.


Lemma ov_no_finite {t: type}:
  forall (x : ftype t) ,
  is_nan _ _ x = false ->
  valid_binary (fprec t) (femax t) (B2FF _ _ x) = true ->
  is_finite _ _ x = true.
Proof.
intros. 
destruct x; simpl in *; auto.
Admitted.

(*
        (A (inord m) (inord m)))) *
  Rabs
    (FT2R
       (dotprod_r
          (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)
          (vec_to_list_float n.+1
             (\col_j X_m_jacobi
                       k.+1 x0 b A
                       j ord0))) -
     FT2R
       (dotprod_r
          (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)
          (vec_to_list_float n.+1
             (\col_j X_m_jacobi k
                       x0 b A j
                       ord0))))
*)

Require Import fma_dot_acc fma_matrix_vec_mult.

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


Lemma dot_prod_sub  {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m: 
  (m < n.+1)%nat ->
  (Rabs
    (FT2R
       (dotprod_r
          (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)
          (vec_to_list_float n.+1
             (\col_j X_m_jacobi
                       k.+1 x0 b A
                       j ord0))) -
     FT2R
       (dotprod_r
          (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)
          (vec_to_list_float n.+1
             (\col_j X_m_jacobi k
                       x0 b A j
                       ord0)))) <= 1)%Re.
Proof.
intros.
pose proof (@fma_dotprod_forward_error _ t).
specialize (H0 (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)  (vec_to_list_float n.+1
             (\col_j X_m_jacobi
                       k.+1 x0 b A
                       j ord0))).
assert ((1 <=
            length
              (vec_to_list_float n.+1
                 (\row_j A2_J A 
                           (inord m) j)^T))%coq_nat).
{ rewrite length_veclist. lia. } specialize (H0 H1).
assert ( length
           (vec_to_list_float n.+1
              (\row_j A2_J A 
                        (inord m) j)^T) =
         length
           (vec_to_list_float n.+1
              (\col_j X_m_jacobi k.+1
                        x0 b A j ord0))).
{ by rewrite !length_veclist. } specialize (H0 H2).
specialize ( H0 (dotprod_r
                  (vec_to_list_float n.+1
                     (\row_j A2_J A
                               (inord m) j)^T)
                  (vec_to_list_float n.+1
                     (\col_j X_m_jacobi
                               k.+1 x0 b A
                               j ord0)))).
specialize (H0 
             (\sum_j ( (FT2R (A2_J A (inord m) j)) * 
                       (FT2R (X_m_jacobi k.+1 x0 b A j ord0)))%Re)).
specialize (H0 
             (\sum_j (Rabs (FT2R (A2_J A (inord m) j)) * 
                      Rabs (FT2R (X_m_jacobi k.+1 x0 b A j ord0)))%Re)).
specialize (H0 (@fma_dot_prod_rel_holds _ _ _ n.+1 m (A2_J A) 
                  (\col_j X_m_jacobi k.+1 x0 b A j ord0))).
assert (\sum_j
           (FT2R
              (A2_J A (inord m) j) *
            FT2R
              (X_m_jacobi k.+1 x0 b
                 A j ord0))%Re = 
        \sum_(j < n.+1)
                FT2R_mat (A2_J A) (inord m) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                FT2R_mat (\col_j X_m_jacobi k.+1 x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
{ apply eq_big. intros. by []. intros.
  assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
  { unfold widen_ord. 
    apply val_inj. by simpl. 
  } rewrite H4. by rewrite !mxE.
} rewrite H3 in H0.
specialize (H0 (@R_dot_prod_rel_holds _ _  n.+1 m (leqnn n.+1) (A2_J A)
              (\col_j X_m_jacobi k.+1 x0 b A j ord0))). 
assert (\sum_j
           (Rabs
              (FT2R
                 (A2_J A 
                    (inord m) j)) *
            Rabs
              (FT2R
                 (X_m_jacobi k.+1
                    x0 b A j ord0))) =  
        sum_fold
          (map (uncurry Rmult)
             (map Rabsp
                (map FR2
                   (combine
                      (vec_to_list_float n.+1
                         (\row_j (A2_J A) (inord m) j)^T)
                      (vec_to_list_float n.+1 
                        (\col_j X_m_jacobi k.+1 x0 b A j ord0))))))).
{ rewrite -sum_fold_mathcomp_equiv.
  apply eq_big. by []. intros.
  assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
  { unfold widen_ord. 
    apply val_inj. by simpl. 
  } rewrite H5. by rewrite !mxE.
} rewrite H4 in H0.
specialize (H0 (R_dot_prod_rel_abs_holds    n.+1 m (A2_J A)
              (\col_j X_m_jacobi k.+1 x0 b A j ord0))).
rewrite -H4 in H0. rewrite -H3 in H0. clear H3 H4.
assert (forall xy : ftype t * ftype t,
          In xy
            (combine
               (vec_to_list_float n.+1
                  (\row_j A2_J A
                           (inord m) j)^T)
               (vec_to_list_float n.+1
                  (\col_j X_m_jacobi
                           k.+1 x0 b A
                           j ord0))) ->
          is_finite (fprec t) 
            (femax t) xy.1 = true /\
          is_finite (fprec t) 
            (femax t) xy.2 = true) by admit.
assert (is_finite (fprec t) 
       (femax t)
       (dotprod_r
          (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)
          (vec_to_list_float n.+1
             (\col_j X_m_jacobi
                       k.+1 x0 b A
                       j ord0))) = true) by admit.
specialize (H0 H3 H4).
pose proof (@fma_dotprod_forward_error _ t).
specialize (H5 (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)  (vec_to_list_float n.+1
             (\col_j X_m_jacobi
                       k x0 b A
                       j ord0))).
specialize (H5 H1).
assert ( length
           (vec_to_list_float n.+1
              (\row_j A2_J A 
                        (inord m) j)^T) =
         length
           (vec_to_list_float n.+1
              (\col_j X_m_jacobi k
                        x0 b A j ord0))).
{ by rewrite !length_veclist. } specialize (H5 H6).
specialize ( H5 (dotprod_r
                  (vec_to_list_float n.+1
                     (\row_j A2_J A
                               (inord m) j)^T)
                  (vec_to_list_float n.+1
                     (\col_j X_m_jacobi
                               k x0 b A
                               j ord0)))).
specialize (H5 
             (\sum_j ( (FT2R (A2_J A (inord m) j)) * 
                       (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
specialize (H5 
             (\sum_j (Rabs (FT2R (A2_J A (inord m) j)) * 
                      Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
specialize (H5 (@fma_dot_prod_rel_holds _ _ _ n.+1 m (A2_J A) 
                  (\col_j X_m_jacobi k x0 b A j ord0))).
assert (\sum_j
           (FT2R
              (A2_J A (inord m) j) *
            FT2R
              (X_m_jacobi k x0 b
                 A j ord0))%Re = 
        \sum_(j < n.+1)
                FT2R_mat (A2_J A) (inord m) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
{ apply eq_big. intros. by []. intros.
  assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
  { unfold widen_ord. 
    apply val_inj. by simpl. 
  } rewrite H8. by rewrite !mxE.
} rewrite H7 in H5.
specialize (H5 (@R_dot_prod_rel_holds _ _  n.+1 m (leqnn n.+1) (A2_J A)
              (\col_j X_m_jacobi k x0 b A j ord0))). 
assert (\sum_j
           (Rabs
              (FT2R
                 (A2_J A 
                    (inord m) j)) *
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
                         (\row_j (A2_J A) (inord m) j)^T)
                      (vec_to_list_float n.+1 
                        (\col_j X_m_jacobi k x0 b A j ord0))))))).
{ rewrite -sum_fold_mathcomp_equiv.
  apply eq_big. by []. intros.
  assert ((widen_ord (m:=n.+1) (leqnn n.+1) i) = i).
  { unfold widen_ord. 
    apply val_inj. by simpl. 
  } rewrite H9. by rewrite !mxE.
} rewrite H8 in H5.
specialize (H5 (R_dot_prod_rel_abs_holds    n.+1 m (A2_J A)
              (\col_j X_m_jacobi k x0 b A j ord0))).
rewrite -H8 in H5. rewrite -H7 in H5. clear H7 H8.
assert (forall xy : ftype t * ftype t,
          In xy
            (combine
               (vec_to_list_float n.+1
                  (\row_j A2_J A
                           (inord m) j)^T)
               (vec_to_list_float n.+1
                  (\col_j X_m_jacobi
                           k x0 b A
                           j ord0))) ->
          is_finite (fprec t) 
            (femax t) xy.1 = true /\
          is_finite (fprec t) 
            (femax t) xy.2 = true) by admit.
assert (is_finite (fprec t) 
       (femax t)
       (dotprod_r
          (vec_to_list_float n.+1
             (\row_j A2_J A
                       (inord m) j)^T)
          (vec_to_list_float n.+1
             (\col_j X_m_jacobi
                       k x0 b A
                       j ord0))) = true) by admit.
specialize (H5 H7 H8).
clear H8 H7 H4 H3.
assert (forall a b x y:R, (x <= a /\ - a <= x)%Re -> (y <= b /\ -b <= y)%Re ->
                 (- (a + b) <= x - y <= a + b)%Re).
{ intros. nra. } rewrite length_veclist in H0.
rewrite length_veclist in H5.
apply Rabs_def3 in H0.
apply Rabs_def3 in H5.
specialize (H3 (g t n.+1 *
                    Rabs
                      (\sum_j
                          Rabs
                            (FT2R (A2_J A (inord m) j)) *
                          Rabs
                            (FT2R
                               (X_m_jacobi k.+1 x0 b A j
                                  ord0))) +
                    g1 t n.+1 (n.+1 - 1)%coq_nat)%Re 
              ( g t n.+1 *
                Rabs
                  (\sum_j
                      Rabs
                        (FT2R (A2_J A (inord m) j)) *
                      Rabs
                        (FT2R
                           (X_m_jacobi k x0 b A j
                              ord0))) +
                g1 t n.+1 (n.+1 - 1)%coq_nat)%Re
              (FT2R
                  (dotprod_r
                     (vec_to_list_float n.+1
                        (\row_j A2_J A (inord m) j)^T)
                     (vec_to_list_float n.+1
                        (\col_j X_m_jacobi k.+1 x0
                                  b A j ord0))) -
                \sum_j
                   (FT2R (A2_J A (inord m) j) *
                    FT2R
                      (X_m_jacobi k.+1 x0 b A j
                         ord0)))%Re 
              (FT2R
                  (dotprod_r
                     (vec_to_list_float n.+1
                        (\row_j A2_J A (inord m) j)^T)
                     (vec_to_list_float n.+1
                        (\col_j X_m_jacobi k x0 b
                                  A j ord0))) -
                \sum_j
                   (FT2R (A2_J A (inord m) j) *
                    FT2R
                      (X_m_jacobi k x0 b A j ord0)))%Re).
specialize (H3 H0 H5).
clear H0 H5.
assert (forall a b c d e:R, (-e <= (a - b) - (c -  d) <= e)%Re ->
                            (-e <= (a - c) - (b - d) <= e)%Re).
{ intros. nra. } apply H0 in H3. clear H0.
assert (forall a b c d :R, (- (a + b + (c + b)) <= d <= (a + b + (c + b)))%Re ->
                             (- ((a + c) + 2 * b) <= d <= ((a + c) + 2 * b))%Re).
{ intros. nra. } apply H0 in H3. clear H0.
apply Rabs_le in H3.



  



















(**
 Bplus_no_overflow t
               (FT2R
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0))
               (FT2R
                  (BOPP t
                     (X_m_jacobi k x0 b A
                        (inord m) ord0)))

**)
Lemma Bplus_x_kp_x_k_no_oveflow {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m: 
  (m < n.+1)%nat ->
  (exists F:R, 
      forall k,
        (Rabs ((FT2R (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0)) - 
               FT2R (X_m_jacobi k x0 b A
                        (inord m) ord0)) <= F)%Re) -> 
  Bplus_no_overflow t
               (FT2R
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0))
               (FT2R
                  (BOPP t
                     (X_m_jacobi k x0 b A
                        (inord m) ord0))).
Proof.
intros.
unfold Bplus_no_overflow.
induction k.
+ pose proof (@generic_round_property t).
  specialize (H1 (FT2R
                     (X_m_jacobi 1 x0 b A
                        (inord m) ord0) +
                   FT2R
                     (BOPP t
                        (X_m_jacobi 0 x0 b A
                           (inord m) ord0)))%Re).
  destruct H1 as [d [e [Hde [Hd [He H1]]]]].
  rewrite H1. clear H1.
  assert ((FT2R
             (X_m_jacobi 1 x0 b A
                (inord m) ord0) +
           FT2R
             (BOPP t
                (X_m_jacobi 0 x0 b A
                   (inord m) ord0)))%Re = 
          (FT2R
             (X_m_jacobi 1 x0 b A
                (inord m) ord0) - 
           FT2R (X_m_jacobi 0 x0 b A
                   (inord m) ord0))%Re).
  { unfold  FT2R. by rewrite B2R_Bopp. }
  rewrite H1.
  admit.
+ pose proof (@generic_round_property t).
  specialize (H1 (FT2R
                   (X_m_jacobi k.+2 x0 b A
                      (inord m) ord0) +
                 FT2R
                   (BOPP t
                      (X_m_jacobi k.+1 x0 b A
                         (inord m) ord0)))%Re ).
  destruct H1 as [d [e [Hde [Hd [He H1]]]]].
  rewrite H1. clear H1.
  assert (X_m_jacobi k.+2 x0 b A (inord m) ord0 = 
          jacobi_iter
             (X_m_jacobi k.+1 x0 b A) b A (inord m) ord0).
  { by simpl. } rewrite H1. clear H1.
  assert (X_m_jacobi k.+1 x0 b A (inord m) ord0 = 
          jacobi_iter
             (X_m_jacobi k x0 b A) b A (inord m) ord0).
  { by simpl. } rewrite H1. clear H1.
  assert ((FT2R
             (jacobi_iter
                (X_m_jacobi k.+1 x0 b A) b
                A (inord m) ord0) +
           FT2R
             (BOPP t
                (jacobi_iter
                   (X_m_jacobi k x0 b A) b
                   A (inord m) ord0)))%Re = 
           (FT2R (jacobi_iter
                    (X_m_jacobi k.+1 x0 b A) b A (inord m) ord0) - 
            FT2R (jacobi_iter
                   (X_m_jacobi k x0 b A) b A (inord m) ord0))%Re).
  { unfold FT2R. by rewrite B2R_Bopp. } rewrite H1. clear H1.
  eapply Rle_lt_trans.
  apply Rabs_triang.
  eapply Rle_lt_trans.
  apply Rplus_le_compat_l. apply He.
  rewrite Rabs_mult. eapply Rle_lt_trans.
  apply Rplus_le_compat_r. apply Rmult_le_compat_l.
  apply Rabs_pos. 
  apply Rle_trans with (Rabs 1 + Rabs d)%Re.
  apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
  apply Hd.
  unfold jacobi_iter.
  rewrite !mxE.
  repeat (rewrite nth_vec_to_list_float; last by rewrite inordK).
  rewrite inord_val.
  pose proof (@BMULT_accurate' _ t).
  specialize (H1 (A1_inv_J A (inord m) ord0) ((b -f
                   A2_J A *f
                   X_m_jacobi k.+1 x0 b A)
                    (inord m) ord0)).
  assert (is_finite (fprec t) 
             (femax t)
             (BMULT t
                (A1_inv_J A (inord m) ord0)
                ((b -f
                  A2_J A *f
                  X_m_jacobi k.+1 x0 b A)
                   (inord m) ord0)) = true) by admit.
  specialize (H1 H2). 
  destruct H1 as [d1 [e1 [Hde1 [Hd1 [He1 H1]]]]].
  pose proof (@BMULT_accurate' _ t).
  specialize (H3 (A1_inv_J A (inord m) ord0) ((b -f
                   A2_J A *f
                   X_m_jacobi k x0 b A)
                    (inord m) ord0)).
  assert (is_finite (fprec t) 
             (femax t)
             (BMULT t
                (A1_inv_J A (inord m) ord0)
                ((b -f
                  A2_J A *f
                  X_m_jacobi k x0 b A)
                   (inord m) ord0)) = true) by admit.
  specialize (H3 H4). 
  destruct H3 as [d2 [e2 [Hde2 [Hd2 [He2 H3]]]]].
  rewrite H1 H3.
  match goal with |-context[(Rabs (?a + ?b - (?c + ?d)) * _ + _ < _)%Re]=>
    replace (a + b - (c + d))%Re with ((a - c) + (b - d))%Re by nra
  end.
  eapply Rle_lt_trans. apply Rplus_le_compat_r.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  apply Rabs_triang.
  eapply Rle_lt_trans. apply Rplus_le_compat_r.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  apply Rplus_le_compat_l.
  apply Rle_trans with (2 * (default_abs t))%Re.
  eapply Rle_trans.
  apply Rabs_triang .
  rewrite Rabs_Ropp. nra. apply Rle_refl.
  rewrite !Rmult_assoc.
  rewrite -Rmult_minus_distr_l. rewrite Rabs_mult.
  assert ((FT2R
             ((b -f
               A2_J A *f
               X_m_jacobi k.+1 x0 b A)
                (inord m) ord0) *   (1 + d1) -
             FT2R
               ((b -f
                 A2_J A *f
                 X_m_jacobi k x0 b A)
                  (inord m) ord0) *  (1 + d2))%Re = 
          ((FT2R
             ((b -f
               A2_J A *f
               X_m_jacobi k.+1 x0 b A)
                (inord m) ord0)  - 
           FT2R
               ((b -f
                 A2_J A *f
                 X_m_jacobi k x0 b A)
                  (inord m) ord0)) * (1+ d1) +
          (FT2R
               ((b -f
                 A2_J A *f
                 X_m_jacobi k x0 b A)
                  (inord m) ord0) * (1+ d1) - 
            FT2R
               ((b -f
                 A2_J A *f
                 X_m_jacobi k x0 b A)
                  (inord m) ord0) * (1+ d2)))%Re).
  { nra. } rewrite H5. clear H5.
  eapply Rle_lt_trans. apply Rplus_le_compat_r.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  apply Rplus_le_compat_r. apply Rmult_le_compat_l.
  apply Rabs_pos. apply Rabs_triang.
  rewrite -Rmult_minus_distr_l.
  assert ((1 + d1 - (1 + d2))%Re = (d1 - d2)%Re).
  { nra. } rewrite H5. clear H5.
  eapply Rle_lt_trans. apply Rplus_le_compat_r.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  apply Rplus_le_compat_r. apply Rmult_le_compat_l.
  apply Rabs_pos. 
  apply Rplus_le_compat. rewrite Rabs_mult. apply Rmult_le_compat_l.
  apply Rabs_pos. apply Rle_trans with (Rabs 1 + Rabs d1)%Re.
  apply Rabs_triang. rewrite Rabs_R1. 
  apply Rplus_le_compat_l. apply Hd1.
  rewrite Rabs_mult. apply Rmult_le_compat_l. apply Rabs_pos.
  apply Rle_trans with (2 * (default_rel t))%Re.
  eapply Rle_trans. apply Rabs_triang.
  rewrite Rabs_Ropp. nra. apply Rle_refl.
  rewrite !mxE.
  rewrite !Bminus_bplus_opp_equiv.
  - pose proof (@BPLUS_accurate' _ t).
    specialize (H5 (b (inord m) ord0) (BOPP t
                      (let l1 :=
                         vec_to_list_float n.+1
                           (\row_j 
                            A2_J A 
                              (inord m) j)^T in
                       let l2 :=
                         vec_to_list_float n.+1
                           (\col_j 
                            X_m_jacobi k.+1 x0
                              b A j ord0) in
                       dotprod_r l1 l2))).
    assert (is_finite (fprec t) (femax t)
               (BPLUS t (b (inord m) ord0)
                  (BOPP t
                     (let l1 :=
                        vec_to_list_float n.+1
                          (\row_j 
                           A2_J A 
                             (inord m) j)^T in
                      let l2 :=
                        vec_to_list_float n.+1
                          (\col_j 
                           X_m_jacobi k.+1 x0 b
                             A j ord0) in
                      dotprod_r l1 l2))) = true) by admit.
    specialize (H5 H6).
    destruct H5 as [d3 [Hd3 H5]].
    rewrite H5.
    assert (FT2R
             (BOPP t
                (let l1 :=
                   vec_to_list_float n.+1
                     (\row_j A2_J A
                             (inord m) j)^T
                   in
                 let l2 :=
                   vec_to_list_float n.+1
                     (\col_j X_m_jacobi
                             k.+1 x0 b A j
                             ord0) in
                 dotprod_r l1 l2)) = 
            (- (FT2R (let l1 :=
                   vec_to_list_float n.+1
                     (\row_j A2_J A
                             (inord m) j)^T
                   in
                 let l2 :=
                   vec_to_list_float n.+1
                     (\col_j X_m_jacobi
                             k.+1 x0 b A j
                             ord0) in
                 dotprod_r l1 l2)))%Re).
    { unfold FT2R. by rewrite B2R_Bopp. } rewrite H7. clear H7.
    pose proof (@BPLUS_accurate' _ t).
    specialize (H7 (b (inord m) ord0) (BOPP t
                    (let l1 :=
                       vec_to_list_float n.+1
                         (\row_j 
                          A2_J A 
                            (inord m) j)^T in
                     let l2 :=
                       vec_to_list_float n.+1
                         (\col_j 
                          X_m_jacobi k x0 b A
                            j ord0) in
                     dotprod_r l1 l2))).
    assert (is_finite (fprec t) (femax t)
             (BPLUS t (b (inord m) ord0)
                (BOPP t
                   (let l1 :=
                      vec_to_list_float n.+1
                        (\row_j 
                         A2_J A 
                           (inord m) j)^T in
                    let l2 :=
                      vec_to_list_float n.+1
                        (\col_j 
                         X_m_jacobi k x0 b A
                           j ord0) in
                    dotprod_r l1 l2))) = true) by admit.
   specialize (H7 H8).
   destruct H7 as [d4 [Hd4 H7]].
   rewrite H7.
   assert (FT2R
             (BOPP t
                (let l1 :=
                   vec_to_list_float n.+1
                     (\row_j A2_J A
                             (inord m) j)^T
                   in
                 let l2 :=
                   vec_to_list_float n.+1
                     (\col_j X_m_jacobi k
                             x0 b A j ord0)
                   in
                 dotprod_r l1 l2)) = 
            (- (FT2R (let l1 :=
                   vec_to_list_float n.+1
                     (\row_j A2_J A
                             (inord m) j)^T
                   in
                 let l2 :=
                   vec_to_list_float n.+1
                     (\col_j X_m_jacobi k
                             x0 b A j ord0)
                   in
                 dotprod_r l1 l2)))%Re).
   { unfold FT2R. by rewrite B2R_Bopp. } rewrite H9. clear H9.
   assert (((FT2R (b (inord m) ord0) +
             -
             FT2R
               (let l1 :=
                  vec_to_list_float n.+1
                    (\row_j A2_J A 
                              (inord m) j)^T
                  in
                let l2 :=
                  vec_to_list_float n.+1
                    (\col_j X_m_jacobi k.+1
                              x0 b A j ord0)
                  in
                dotprod_r l1 l2)) * 
            (1 + d3) -
            (FT2R (b (inord m) ord0) +
             -
             FT2R
               (let l1 :=
                  vec_to_list_float n.+1
                    (\row_j A2_J A 
                              (inord m) j)^T
                  in
                let l2 :=
                  vec_to_list_float n.+1
                    (\col_j X_m_jacobi k x0 b
                              A j ord0) in
                dotprod_r l1 l2)) * 
            (1 + d4))%Re = 
            (((FT2R (b (inord m) ord0) - FT2R
               (let l1 :=
                  vec_to_list_float n.+1
                    (\row_j A2_J A 
                              (inord m) j)^T
                  in
                let l2 :=
                  vec_to_list_float n.+1
                    (\col_j X_m_jacobi k.+1
                              x0 b A j ord0)
                  in
                dotprod_r l1 l2)) - 
            (FT2R (b (inord m) ord0) - FT2R
               (let l1 :=
                  vec_to_list_float n.+1
                    (\row_j A2_J A 
                              (inord m) j)^T
                  in
                let l2 :=
                  vec_to_list_float n.+1
                    (\col_j X_m_jacobi k x0 b
                              A j ord0) in
                dotprod_r l1 l2))) * (1 + d3) +
            ((FT2R (b (inord m) ord0) - FT2R
               (let l1 :=
                  vec_to_list_float n.+1
                    (\row_j A2_J A 
                              (inord m) j)^T
                  in
                let l2 :=
                  vec_to_list_float n.+1
                    (\col_j X_m_jacobi k x0 b
                              A j ord0) in
                dotprod_r l1 l2)) * (1 + d3) - 
            (FT2R (b (inord m) ord0) - FT2R
               (let l1 :=
                  vec_to_list_float n.+1
                    (\row_j A2_J A 
                              (inord m) j)^T
                  in
                let l2 :=
                  vec_to_list_float n.+1
                    (\col_j X_m_jacobi k x0 b
                              A j ord0) in
                dotprod_r l1 l2)) * (1 + d4)))%Re).
    { nra. } rewrite H9. clear H9.
    eapply Rle_lt_trans. apply Rplus_le_compat_r. 
    apply Rmult_le_compat_r.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    apply Rplus_le_compat_r.
    apply Rmult_le_compat_l. apply Rabs_pos.
    apply Rplus_le_compat. apply Rmult_le_compat_r.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat.
    assert (forall a b c:R, ((a - b) - (a - c))%Re = (- (b - c))%Re).
    { intros. nra. } rewrite H9. rewrite Rabs_mult. rewrite Rabs_Ropp.
    apply Rmult_le_compat_l. apply Rabs_pos.
    apply Rle_trans with (Rabs 1 + Rabs d3)%Re.
    apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
    apply Hd3. 
    rewrite -Rmult_minus_distr_l. rewrite Rabs_mult.
    assert ((1 + d3 - (1 + d4))%Re = (d3 - d4)%Re).
    { nra. } rewrite H9. apply Rmult_le_compat_l.
    apply Rabs_pos. apply Rle_trans with (2 * (default_rel t))%Re.
    eapply Rle_trans. apply Rabs_triang. 
    rewrite Rabs_Ropp. nra.
    apply Rle_refl.
    apply Rmult_le_compat_r. 
    apply Rmult_le_pos; try nra; try apply default_rel_ge_0.
    rewrite Rabs_mult. apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Rle_trans with (Rabs 1 + Rabs d4)%Re.
    apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
    apply Hd4.
    eapply Rle_lt_trans. apply Rplus_le_compat_r.
    apply Rmult_le_compat_r.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    apply Rplus_le_compat_r.
    apply Rle_trans with 
    ((1 + default_rel t)^2 * Rabs
       (FT2R
          (BDIV t (Zconst t 1)
             (A (inord m) (inord m)))) * 
       (Rabs
         (FT2R
            (dotprod_r
               (vec_to_list_float n.+1
                  (\row_j A2_J A (inord m) j)^T)
               (vec_to_list_float n.+1
                  (\col_j X_m_jacobi k.+1 x0
                            b A j ord0))) -
          FT2R
            (dotprod_r
               (vec_to_list_float n.+1
                  (\row_j A2_J A (inord m) j)^T)
               (vec_to_list_float n.+1
                  (\col_j X_m_jacobi k x0 b
                            A j ord0))))) +
      4 * (default_rel t) * (1 + default_rel t) * 
      Rabs
       (FT2R
          (BDIV t (Zconst t 1)
             (A (inord m) (inord m)))) *
      Rabs
       (FT2R (b (inord m) ord0) -
        FT2R
          (dotprod_r
             (vec_to_list_float n.+1
                (\row_j A2_J A (inord m) j)^T)
             (vec_to_list_float n.+1
                (\col_j X_m_jacobi k x0 b
                          A j ord0)))))%Re.
   * match goal with |-context[(?a * ((?b + ?c) * ?d + ?e) <= _)%Re]=>
      replace (a * ((b+c)*d + e))%Re with 
              ( a * b * d + (a * c * d + a * e))%Re by nra
     end.
     apply Rplus_le_compat. nra.  
     match goal with |-context[(?a * (?b * ?c) * ?d + ?a * (?e * ?d * ?c) <= _)%Re]=>
        replace (a * (b * c) * d + a * (e * d * c))%Re with 
                (a * ((c * d) * (b + e)))%Re by nra
     end.
     match goal with |-context[( _ <= 4 * ?b * ?c * ?a * ?d)%Re]=>
       replace (4 * b * c * a * d)%Re with (a * (((2 * b) * c) *(2 * d)))%Re by nra
     end. apply Rmult_le_compat_l. apply Rabs_pos. apply Rmult_le_compat_l.
     repeat apply Rmult_le_pos; try nra; try apply bpow_ge_0.
     apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
     assert (forall x:R, (2 * x)%Re = (x + x)%Re) by (intros;nra).
     rewrite H9. clear H9. apply Rplus_le_compat_l.
     apply Rle_refl.
   * apply Rplus_le_compat_l. repeat apply Rmult_le_compat_l.
     repeat apply Rmult_le_pos; try nra; try apply bpow_ge_0; try apply Rabs_pos.
     apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
     apply Rabs_triang.
   * rewrite Rabs_Ropp.

    




  simpl.
  





Admitted.



Lemma residual_is_finite {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat):
  let resid := residual_math A x0 b in
  is_finite (fprec t) (femax t)
    (norm2
       (rev
          (vec_to_list_float n.+1 (resid k)))) = true.
Proof.
unfold norm2. apply dotprod_finite.
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
  - admit.
  - rewrite mxE.  apply Bplus_bminus_opp_implies.
    apply Bplus_no_ov_is_finite.
    * admit.
    * admit.
    * apply Bplus_x_kp_x_k_no_oveflow.
  - admit.
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
  (** bound x_k by max_i { (D^-1 b)_i} \rho ^ i **)
  pose proof (@BMULT_accurate' _ t (A (inord m) (inord m))
              ((X_m_jacobi k.+1 x0 b A -f
                 X_m_jacobi k x0 b A) (inord m) ord0)).
  assert (is_finite (fprec t) (femax t)
             (BMULT t (A (inord m) (inord m))
                ((X_m_jacobi k.+1 x0 b A -f
                  X_m_jacobi k x0 b A)
                   (inord m) ord0)) = true) by admit.
  specialize (H1 H2).
  destruct H1 as [d [e [Hde [Hd [He H1]]]]].
  rewrite H1.
  eapply Rle_trans.
  apply Rabs_triang.
  eapply Rle_trans.
  apply Rplus_le_compat_l. apply He.
  rewrite Rabs_mult. eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l. apply Rabs_pos.
  apply Rle_trans with (Rabs 1 + Rabs d)%Re.
  apply Rabs_triang.
  rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd.
  rewrite Rabs_mult. rewrite mxE.
  rewrite Bminus_bplus_opp_equiv.
  - pose proof (@BPLUS_accurate _ t).
    specialize (H3 (X_m_jacobi k.+1 x0 b A
                           (inord m) ord0)).
    assert (is_finite (fprec t) (femax t)
               (X_m_jacobi k.+1 x0 b A 
                  (inord m) ord0) = true) by admit.
    specialize (H3 H4).
    specialize (H3 (BOPP t
                        (X_m_jacobi k x0 b A  
                             (inord m) ord0))).
    assert (is_finite (fprec t) (femax t)
               (BOPP t
                  (X_m_jacobi k x0 b A 
                     (inord m) ord0)) = true) by admit.
    specialize (H3 H5).
    assert ( Bplus_no_overflow t
               (FT2R
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0))
               (FT2R
                  (BOPP t
                     (X_m_jacobi k x0 b A
                        (inord m) ord0)))) by admit.
    specialize (H3 H6).
    destruct H3 as [d1 [Hd1 H3]].
    rewrite H3.
    assert (FT2R
             (BOPP t
                (X_m_jacobi k x0 b A 
                   (inord m) ord0)) = 
              (- (FT2R (X_m_jacobi k x0 b A 
                     (inord m) ord0)))%Re).
    { unfold FT2R. by rewrite B2R_Bopp. }
    rewrite H7. eapply Rle_trans.
    apply Rplus_le_compat_r.
    apply Rmult_le_compat_r.
    apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    apply Rmult_le_compat_l; first by apply Rabs_pos.
    rewrite Rabs_mult.
    apply Rmult_le_compat_l; first by apply Rabs_pos.
    apply Rle_trans with (Rabs 1 + Rabs d1)%Re.
    apply Rabs_triang.
    apply Rplus_le_compat_l. apply Hd1.
    rewrite Rabs_R1.
    apply Rcomplements.Rle_minus_r.
    apply Rdiv_le_right_elim; first by
    apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
    rewrite -Rmult_assoc.
    apply Rdiv_le_right_elim; first by
    apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
    (** at this point, we have that 
        |A_ii | | x_k+1 - x_k | <= \sqrt{ F' / (2 * n * d^n)} / (1+ d)^2
     **)
    admit.
  - admit.
  - rewrite is_finite_Bopp. admit.
  - apply Bplus_no_ov_is_finite.
    * admit.
    * admit.
    * apply Bplus_x_kp_x_k_no_oveflow.
Admitted.


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
is_finite (fprec t) (femax t) (dotprod (rev v) (rev v)) = true ->
(forall x, In x v -> 
           is_finite (fprec t) (femax t) x = true).
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
  apply bfma_overflow_implies in H.
  destruct H as [Ha1 [Ha2 Hd]].
  destruct H0.
  - by rewrite -H.
  - by specialize (IHv Hd H).
Qed.
  
Require Import float_acc_lems.

Lemma vec_succ_err {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= mulmx (A_real^-1) b_real in
  let e_0 := f_error 0 b x0 x A in
  (rho < 1)%Re ->
  A_real \in unitmx ->
  (forall i, is_finite (fprec t) (femax t)
              (BDIV t (Zconst t 1) (A i i)) = true) ->
  (forall i, is_finite (fprec t) (femax t) (A i i) = true) ->
  (vec_inf_norm (FT2R_mat ((X_m_jacobi k.+1 x0 b A) -f (X_m_jacobi k x0 b A))) <=
    (rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))%Re.
Proof.
intros ? ? ? ? ? ?  ? Hrho HAinv HfinvA HfA.
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
      apply bmult_overflow_implies in H3.
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
        assert (is_finite _ _ (X_m_jacobi k.+1 x0 b A
                                    (inord m) ord0) = true /\
                is_finite _ _  (X_m_jacobi k x0 b A
                                  (inord m) ord0) = true).
        { apply bplus_overflow_implies  in Hf2.
          split; try apply Hf2.
          rewrite is_finite_Bopp in Hf2.
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
          { fold A_real. by rewrite mulmxV . }
          rewrite H2. by rewrite mul1mx /b_real.
        + intros. unfold A_real. rewrite !mxE. by apply BDIV_FT2R_sep_zero.
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
      assert (forall i : 'I_n.+1,
                is_finite (fprec t) (femax t) (A i i) = true) by (intros; apply HfA).
      assert ((rho < 1)%Re) by apply Hrho.
      assert (FT2R_mat A \in unitmx). 
      { by rewrite /A_real in HAinv. }
      assert (forall i : 'I_n.+1,
              is_finite (fprec t) (femax t)
                (BDIV t (Zconst t 1) (A i i)) = true) by (intros; apply HfinvA).
     assert (forall (k : nat) (i : 'I_n.+1),
                is_finite (fprec t) (femax t)
                  (X_m_jacobi k x0 b A i ord0) = true).
     { intros. 
       pose proof (@residual_is_finite  t n A x0 b k0).
       unfold norm2 in H10.
       pose proof (@dotprod_finite_implies t).
       specialize (H11 (
             (vec_to_list_float n.+1
                (residual_math A x0 b k0))) H10).
       specialize (H11 (nth i (rev
                               (vec_to_list_float n.+1
                                  (residual_math A x0 b k0))) (Zconst t 0))).
       assert (In
                (nth i
                   (rev
                      (vec_to_list_float n.+1
                         (residual_math A x0 b k0)))
                   (Zconst t 0))
                (
                   (vec_to_list_float n.+1
                      (residual_math A x0 b k0)))).
       { rewrite rev_nth. apply nth_In. 
          rewrite length_veclist . lia. 
         rewrite !length_veclist. apply /ssrnat.ltP. apply ltn_ord.
      } specialize (H11 H12).
       rewrite rev_nth in H11. rewrite length_veclist in H11.
       assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat).
       { lia. } rewrite H13 in H11.
       rewrite nth_vec_to_list_float in H11;
        last by  apply ltn_ord.
       rewrite !mxE in H11. 
       apply bmult_overflow_implies in H11.
       destruct H11 as [Hf1 Hf2].
       rewrite nth_vec_to_list_float in Hf2;
        last by  apply ltn_ord. rewrite inord_val in Hf2.
       rewrite mxE in Hf2. 
       apply Bminus_bplus_opp_implies in Hf2.
       apply bplus_overflow_implies in Hf2.
       destruct Hf2 as [Hf21 Hf22].
       rewrite inord_val in Hf22.
       by rewrite is_finite_Bopp in Hf22.
       rewrite length_veclist. apply /ssrnat.ltP. apply ltn_ord.
     } 
     (** also implied by finiteness of residual **)
     specialize (H5 H6 H7 H8 H9 x0 H10).
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
            { nra. } rewrite H13. rewrite Rinv_r; last by nra.
            rewrite Rmult_1_r.
            assert (((rho ^ k * e_0 * (1 - rho)) * / (1- rho))%Re = 
                     ( (rho^k * e_0) * ((1 - rho) * / (1- rho)))%Re).
            { nra. } rewrite H14. rewrite Rinv_r; nra.
          } rewrite H13. clear H13. nra.
        } rewrite H13. clear H13.
        assert ((rho ^ k.+1 * (1 - rho) * e_0 +
                  (1 - rho ^ k.+1) * d_mag +
                  rho ^ k * (1 - rho) * e_0 +
                  (1 - rho ^ k) * d_mag)%Re = 
                (rho ^ k * (1+ rho) * (1 - rho) * e_0 + 
                  2* d_mag  - rho^k * (1 + rho) * d_mag)%Re).
        { simpl. nra. } rewrite H13. clear H13.
        assert ((rho ^ k * (1 + rho) * (1 - rho) * e_0 +
                  2 * d_mag - rho ^ k * (1 + rho) * d_mag)%Re = 
                ((rho ^ k * (1 + rho) * ((1-rho) * e_0 - d_mag)) + 2 * d_mag)%Re).
        { nra. } rewrite H13. clear H13.
        rewrite Rmult_plus_distr_r.
        assert ((rho ^ k * (1 + rho) *
                    ((1 - rho) * e_0 - d_mag) * / (1 - rho))%Re =
                (rho ^ k * (1 + rho) * 
                (e_0 * ( (1 - rho) * / (1 - rho)) - d_mag * /(1 - rho)))%Re).
        { nra. } rewrite H13. clear H13. rewrite Rinv_r; last by nra.
        rewrite Rmult_1_r. nra.
Qed.


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


Lemma Gamma_constraint {t}  {n:nat} 
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (k:nat) (acc : ftype t) :
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in
  let Gamma := FT2R (BMULT t acc acc) in 
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
  (FT2R_mat A \in unitmx) ->
  (forall i : 'I_n.+1,
          is_finite (fprec t) (femax t)
            (BDIV t (Zconst t 1) (A i i)) = true) ->
  (forall i : 'I_n.+1,
      is_finite (fprec t) (femax t) (A i i) = true) ->
  (0 < f_error 0 b x0 x A - d_mag / (1 - rho))%Re ->
  (Rabs (FT2R (norm2 (rev v_l))) <= 
    INR n.+1 * 
    (Rsqr (vec_inf_norm (FT2R_mat (A1_J A)) * 
      ((rho ^ k * (1 + rho) * (e_0 - d_mag / (1 - rho)) + 2 * d_mag / (1 - rho)) * (1+ default_rel t))
        * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat) *
      (1 + g t n.+1)) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
Proof.
intros ? ? ? ? ? ? ? ? ? ? HinvA HfinvA HfA He0.
eapply Rle_trans.
+ apply norm2_vec_inf_norm_rel.
  - intros.
    pose proof (@residual_is_finite  t n A x0 b k).
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
                (vec_to_list_float n.+1 (resid k))
                (vec_to_list_float n.+1 (resid k))) as r_l.
    apply in_rev  in H0.
    assert (exists m, (m < length (rev r_l))%coq_nat /\
                      nth m (rev r_l) (Zconst t 0, Zconst t 0) = xy).
    { by apply In_nth. } destruct H4 as [m [Hm Hnth]].
    specialize (H3 (nth m (rev
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
    } specialize (H3 H4). 
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
    } rewrite H5 H6. unfold resid. split; by apply H3.
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
            { intros.
              pose proof (@residual_is_finite  t n A x0 b k).
              unfold norm2 in H2.
              pose proof (@dotprod_finite_implies t).
              specialize (H3 (
                         (vec_to_list_float n.+1
                            (residual_math A x0 b k))) H2).
              pose proof (@dotprod_finite_implies t).
              specialize (H4 (
                              (vec_to_list_float n.+1
                                 (residual_math A x0 b k))) H2).
              remember (combine
                          (vec_to_list_float n.+1 (A1_J A))
                          (vec_to_list_float n.+1
                             (X_m_jacobi k.+1 x0 b A -f
                              X_m_jacobi k x0 b A))) as r_l.
              apply in_rev  in H1.
              assert (exists m, (m < length (rev r_l))%coq_nat /\
                                nth m (rev r_l) (Zconst t 0, Zconst t 0) = xy).
              { by apply In_nth. } destruct H5 as [m [Hm Hnth]].
              unfold residual_math in H4.
              specialize (H4 (nth m (rev
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
              } specialize (H4 H5).
              rewrite rev_nth in H4.
              rewrite length_veclist in H4.
              assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
              { lia. } rewrite H6 in H4.
              rewrite nth_vec_to_list_float in H4.
              + rewrite !mxE in H4.
                rewrite nth_vec_to_list_float in H4; last 
                by rewrite inordK;
                 rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP.
                rewrite nth_vec_to_list_float in H4; last 
                by rewrite inordK;
                 rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP.
                rewrite inord_val in H4. 
                assert (is_finite _ _ (A1_J A (inord m) ord0) = true /\
                        is_finite _ _  ((X_m_jacobi k.+1 x0 b A -f
                                          X_m_jacobi k x0 b A) (inord m) ord0) = true).
                { apply bmult_overflow_implies  in H4.
                  split; try apply H4.
                }  rewrite Heqr_l in Hnth. rewrite rev_nth in Hnth.
                rewrite combine_length !length_veclist Nat.min_id in Hnth.
                assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat).
                { lia. } rewrite H8 in Hnth. rewrite combine_nth in Hnth.
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
                  } rewrite H9 H10.
                  repeat split; try apply H7; try apply H4.
               - by rewrite !length_veclist.
               - by rewrite Heqr_l rev_length in Hm. 
             + by rewrite   Heqr_l  rev_length combine_length !length_veclist Nat.min_id in Hm;
                  apply /ssrnat.ltP.
             + rewrite Heqr_l rev_length combine_length !length_veclist Nat.min_id in Hm.
               by rewrite length_veclist.
           (** Implied by finiteness of the residual **) } specialize (H0 H1).
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
                 --- by apply vec_succ_err.
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
                   --- apply Rlt_le. apply Rinv_0_lt_compat. nra.
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
destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk He0]]]]]]].
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
         specialize (H1 H2). unfold resid,x0. rewrite Heqe_0 Heqrho Heqd_mag Heqx.
         unfold x0. apply H1. 
         apply HinvA.
         by intros.
         by intros. 
         assert (WITH_NANS.f_error 0 b x0 x A = 
                            f_error 0 b x0 x A ).
         { unfold WITH_NANS.f_error, f_error. reflexivity. }
         rewrite /x0 Heqx in H3. rewrite -H3. rewrite Heqd_mag Heqrho Heqx in He0. apply He0.
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
         } rewrite H1. 
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
                   rewrite H2.
                   match goal with |-context[(_ < ?x / ?y / ?z)%Re]=>
                      replace (x / y / z)%Re with (/ ((y * z)  / x))%Re 
                   end. 
                   --- apply Rinv_lt_contravar.
                       *** repeat apply Rmult_lt_0_compat.
                           ++++ apply Rlt_gt.  rewrite Heqe_0. apply He0.
                           ++++ nra.
                           ++++ apply Rinv_0_lt_compat.
                                rewrite HeqGamma. unfold acc2. 
                                rewrite Heqd_mag Heqrho.
                                apply Gamma_constraint. auto.
                                rewrite Heqrho in Hrho. apply Hrho.
                                intros.
                                rewrite !mxE. by apply BDIV_FT2R_sep_zero.
                                rewrite Heqrho Heqd_mag in HG. apply HG.
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
                            + assert ( (1 < /rho)%Re -> (/ rho )%Re <> 1%Re). { nra. }
                              apply H3. replace 1%Re with (/1)%Re by nra.
                               apply Rinv_lt_contravar. rewrite Rmult_1_r.
                               apply Hrho. apply Hrho.
                            + apply Rinv_0_lt_compat. apply Hrho.
                            + repeat apply Rmult_lt_0_compat.
                              - apply Rlt_gt.  rewrite Heqe_0. apply He0.
                              - nra.
                              - apply Rinv_0_lt_compat.
                                rewrite HeqGamma. unfold acc2. 
                                rewrite Heqd_mag Heqrho.
                                apply Gamma_constraint. auto.
                                rewrite Heqrho in Hrho. apply Hrho.
                                intros.
                                rewrite !mxE. by apply BDIV_FT2R_sep_zero.
                                rewrite Heqrho Heqd_mag in HG. apply HG.
                          }
                          rewrite H3.
                          assert ( ((/ rho) ^ (k_min A b acc).+1)%Re = 
                                   Rpower (/rho)%Re (INR (k_min A b acc).+1)).
                          { rewrite Rpower_pow. nra.
                            apply Rinv_0_lt_compat. apply Hrho.
                          }
                          rewrite H4. apply Rpower_lt .
                          ++++ replace 1%Re with (/1)%Re by nra.
                               apply Rinv_lt_contravar. rewrite Rmult_1_r.
                               apply Hrho. 
                               apply Hrho.
                          ++++ apply Rle_lt_trans with (INR (k_min A b acc)).
                               ---- unfold k_min.
                                    assert (WITH_NANS.f_error 0 b x0 x A = 
                                          f_error 0 b x0 x A ).
                                     { unfold WITH_NANS.f_error, f_error. reflexivity. }
                                     rewrite /x0 Heqx in H5.  rewrite  Heqrho Heqd_mag Heqe_0 HeqGamma /x0 Heqx !H5 /acc2.
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
                       { intros. nra. } apply H3. 
                       rewrite Heqe_0. apply He0.
                       assert (forall x:R, (0 <= x)%Re -> (1 + x)%Re <> 0%Re).
                       { intros. nra. } apply H3. rewrite Heqrho. by apply rho_ge_0.
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
    * apply residual_is_finite.
    * by unfold acc2. 
Qed.


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



