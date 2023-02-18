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

Require Import lemmas.
Require Import fma_dot_acc fma_matrix_vec_mult.
From Flocq Require Import Binary.
Require Import finite_lemmas_additional.
Require Import fma_jacobi_forward_error.
Require Import float_acc_lems.
Require Import vec_sum_inf_norm_rel.
Require Import fma_dot_mat_model.

Section WITH_NANS.

Context {NANS: Nans}.

(** Computable definition of rho in reals **)
Definition rho_def_alt  {t: type} {n:nat} (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in   
  let R := (vec_inf_norm (A1_inv_real) * matrix_inf_norm (A2_real))%Re in
  let delta := default_rel t in
  ((((1 + g t n.+1) * (1 + delta) *
                  g t n.+1 + delta * (1 + g t n.+1) +
                  g t n.+1) * (1 + delta) + delta) * R +
                (((1 + g t n.+1) * (1 + delta) *
                  g t n.+1 + delta * (1 + g t n.+1) +
                  g t n.+1) * default_abs t +
                 default_abs t) *
                matrix_inf_norm (A2_real) + R)%Re.

(** Computable definition of d_mag in reals **)
Definition d_mag_def_alt {t: type} {n:nat} (A: 'M[ftype t]_n.+1) 
  (b: 'cV[ftype t]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in 
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in  
  let R := (vec_inf_norm (A1_inv_real) * matrix_inf_norm (A2_real))%Re in
  let delta := default_rel t in
  ((g t n.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_inv_real) *
                      (1 + delta) + default_abs t) *
                     vec_inf_norm b_real) +
                    (1 + g t n.+1) * g1 t n.+1 (n.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_inv_real) *
                     (1 + delta) + default_abs t) +
                    g1 t n.+1 (n.+1 - 1) +
                    (vec_inf_norm (A1_inv_real) * delta +
                     default_abs t) * vec_inf_norm b_real +
                    ((((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * (1 + delta) + delta) * R +
                     (((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * default_abs t +
                      default_abs t) *
                     matrix_inf_norm (A2_real)) *
                     (vec_inf_norm (A1_inv_real) * 
                       vec_inf_norm b_real * (/ (1 - rho_def_alt A b))))%Re.

(** bound for ||x|| **)
Lemma x_bound_exists {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) :
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def :=  (vec_inf_norm (A1_inv_real) *
                      matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
   (vec_inf_norm x1 <= 
      (vec_inf_norm (A1_inv_real) * vec_inf_norm (b_real)) / (1 - R_def))%Re.
Admitted.


(** relation between the non-computable and computable rho **)
Lemma rho_def_le_alt {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
  (rho_def A b <= rho_def_alt A b)%Re.
Admitted.

(** relation between the non-computable and computable d_mag **)
Lemma d_mag_def_le_alt {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
  (d_mag_def A b <= d_mag_def_alt A b)%Re.
Proof.
unfold d_mag_def, d_mag_def_alt.
apply Rplus_le_compat.
+ admit.
+ apply Rmult_le_compat.
  - admit.
  - apply /RleP. apply vec_norm_pd.
  - admit.
  - eapply Rle_trans. apply x_bound_exists.
    * admit.
    * apply Rmult_le_compat_l.
      ++ apply Rmult_le_pos; (apply /RleP; apply vec_norm_pd).
      ++ apply Rlt_le. apply  Rinv_lt_contravar.
         ** apply Rmult_lt_0_compat. apply Rlt_Rminus.
            admit.
            apply Rlt_Rminus. admit.
         ** apply Rplus_le_lt_compat. nra.
            apply Ropp_lt_contravar. admit.
Admitted.

Lemma d_mag_def_alt_ge_0 {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
   (0 <= d_mag_def_alt A b)%Re.
Admitted.


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
  (0 < f_error 0 b x0 x A - d_mag / (1 - rho))%Re /\
  (** finiteness of x0 **)
  (forall i : 'I_n.+1, is_finite (fprec t) (femax t)
                              (x0 i ord0) = true) /\
  (** finitenes of A1^{-} **)
  (forall i, is_finite (fprec t) (femax t)
                        (A1_inv_J A i ord0) = true) /\
  (** finiteness of A2 **)
  (forall i j, is_finite (fprec t) (femax t)
                  (A2_J A i j) = true) /\
  (** finitenes of b **) 
  (forall i, is_finite (fprec t) (femax t)
                          (b i ord0) = true) /\
  (** constraint on the dimension **)
  @size_constraint t n /\
  (** constraint on bounds for input **)
  input_bound A x0 b.

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
  let R_def :=  (vec_inf_norm (A1_inv_real) *
                    matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
  (@f_error _ _ _ 0 b x0 x A  <=
    vec_inf_norm (FT2R_mat x0) + 
    (vec_inf_norm (A1_inv_real) * vec_inf_norm (b_real)) / (1 - R_def))%Re. 
Admitted.

(** Replace Gamma with tau_squared  **)

Definition k_min_alt {NANS: Nans} {t: type} {n:nat} (A : 'M[ftype t]_n.+1)
  (b : 'cV[ftype t]_n.+1) (acc : ftype t) :=
  let rho := rho_def_alt A b in
  let d_mag := d_mag_def_alt A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def :=  (vec_inf_norm (A1_inv_real) *
                      matrix_inf_norm (A2_real))%Re in
  let e_0 := (vec_inf_norm (FT2R_mat x0) + 
              (vec_inf_norm (A1_inv_real) * vec_inf_norm (b_real)) / (1 - R_def))%Re in
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

(** input bound' **)
Definition input_bound_Rcompute {t} {n:nat} 
  (A: 'M[ftype t]_n.+1) (x0 b: 'cV[ftype t]_n.+1):=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def :=  (vec_inf_norm (A1_inv_real) *
                      matrix_inf_norm (A2_real))%Re in
  let x_bound :=  
  ((vec_inf_norm (A1_inv_real) *
        vec_inf_norm (b_real)) / (1 - R_def))%Re in 
  let rho := rho_def_alt A b in 
  let d_mag := d_mag_def_alt A b in
  let e_0 := (vec_inf_norm (FT2R_mat x0) + 
              (vec_inf_norm (A1_inv_real) *
                       vec_inf_norm (b_real)) / (1 - R_def))%Re in
  (forall i,
    (Rabs (FT2R (A i i)) *
     (1 * (1 + rho) *
      (e_0 - 0) +
      2 * d_mag * / (1 - rho) +
      2 *
      x_bound ) <
     (sqrt (fun_bnd t n.+1) - default_abs t) /
     (1 + default_rel t) /
     (1 + default_rel t))%Re) /\ 
  (x_bound +
       1 *
       e_0 +
       1 / (1 - rho) *
       d_mag < sqrt (fun_bnd t n.+1))%Re /\
  (forall i j, 
      (Rabs (FT2R (A2_J A i j )) <
        sqrt (fun_bnd t n.+1))%Re) /\
  (forall i,
     (Rabs (FT2R (b i ord0)) +
     (1 + g t n.+1) *
     (( x_bound +
       1 * e_0 +
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
      (( x_bound +
        1 * e_0 +
        1 / (1 - rho) * d_mag) *
       (\sum_j
           Rabs (FT2R (A2_J A (inord i) j)))) +
      g1 t n.+1 (n.+1 - 1)%coq_nat) <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t) /
     (1 + default_rel t))%Re) /\
  (1 * (1 + rho) *
     (e_0 - d_mag * / (1 - rho)) +
     2 * d_mag * / (1 - rho) +
     2 *
     x_bound <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t))%Re.


Definition strict_diagonal_dominance {t} {n:nat} 
  (A: 'M[ftype t]_n.+1):=
    forall i, 
     (Rabs (FT2R_mat A i i ) > 
      \sum_(j < n.+1 | j != i) Rabs (FT2R_mat A i j))%Re.
 
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

(** Rcompute **)
Definition jacobi_preconditions_Rcompute {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in 
  let rho_hat := rho_def_alt A b in 
  let d_mag := d_mag_def_alt A b in
  let x0 := \col_(j < n.+1) (Zconst t 0) in
  let R_def :=  (vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                   matrix_inf_norm (FT2R_mat (A2_J A)))%Re in
  let e_0 := (vec_inf_norm (FT2R_mat x0) + 
                (vec_inf_norm (FT2R_mat (A1_inv_J A)) *
                    vec_inf_norm (FT2R_mat b)) / (1 - R_def))%Re in
  (** Finiteness of A **)
  (forall i j, Binary.is_finite _ _ (A i j) = true) /\ 
  (** contraction constant **)
  (0< rho_hat /\ rho_hat < 1)%Re /\
  (** diagonal dominance of A **)
  strict_diagonal_dominance A /\
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
      d_mag * / (1 - rho_hat))²)%Re /\
  (** Gamma is finite **)
  Binary.is_finite _ _ (BMULT t accuracy accuracy) = true /\
  (** constraint on k **)
  (k_min_alt A b accuracy < k)%coq_nat /\
  (** lower bound on the initial error **)
  (0 < e_0 - d_mag / (1 - rho_hat))%Re /\
  (** finiteness of x0 **)
  (forall i : 'I_n.+1, is_finite (fprec t) (femax t)
                              (x0 i ord0) = true) /\
  (** finiteness of A2 **)
  (forall i j, is_finite (fprec t) (femax t)
                  (A2_J A i j) = true) /\
  (** finitenes of b **) 
  (forall i, is_finite (fprec t) (femax t)
                          (b i ord0) = true) /\
  (** constraint on the dimension **)
  @size_constraint t n /\
  (** constraint on bounds for input **)
  input_bound_Rcompute A x0 b.


(** g  g1  rho d_mag : what do they mean intuitively **)


Lemma input_bound_compute_implies_math {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1):
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
      apply Rplus_le_compat_l. apply rho_def_le_alt.
      apply Rplus_le_compat. 
      apply f_error0_bnd . admit.
      apply Ropp_le_contravar.
      apply Rmult_le_pos. apply d_mag_ge_0.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. eapply Rle_lt_trans.
      apply rho_def_le_alt. apply Hrho.
    * apply Rmult_le_compat.
      apply Rmult_le_pos. nra. apply d_mag_ge_0.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. eapply Rle_lt_trans.
      apply rho_def_le_alt. apply Hrho.
      apply Rmult_le_compat_l. nra. apply d_mag_def_le_alt.
      assert ((rho_def A b = rho_def_alt A b)%Re \/
                  (rho_def A b < rho_def_alt A b)%Re).
         { pose proof (@rho_def_le_alt t n A b). nra. }
         destruct H. 
         rewrite H; nra.
         apply Rlt_le. apply Rinv_lt_contravar .
         apply Rmult_lt_0_compat.
         apply Rlt_Rminus. apply Hrho.
         apply Rlt_Rminus. eapply Rle_lt_trans.
         apply rho_def_le_alt. apply Hrho.
         apply Rplus_le_lt_compat. nra.
         by apply Ropp_lt_contravar.
  - apply Rmult_le_compat_l. nra.
    apply x_bound_exists. admit.
+ admit.
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [_ [_ [bnd3 _]]]. apply bnd3.
+ admit.
+ admit.
+ intros. unfold input_bound_Rcompute in H.
  destruct H as [_[_[_[_[_ bnd6]]]]].
  eapply Rle_lt_trans; last by apply bnd6.
  rewrite !Rmult_1_l. 





admit.
Admitted.
 

(** Refactoring definitions to make them readable and beautiful **)
Lemma jacobi_precond_compute_implies_math {t: type} {n:nat}
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) (accuracy: ftype t) (k: nat): 
  jacobi_preconditions_Rcompute A b accuracy k ->
  jacobi_preconditions_math A b accuracy k.
Proof.
intros.
unfold jacobi_preconditions_Rcompute in H.
destruct H as [Hfa [Hrho [Hdom [Hfdiv [HG1 [Hfacc [Hk [He0 [Hfx0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]].
repeat (split; try apply size_cons; try by (apply input_bound_compute_implies_math; try apply Hrho); try apply Hfacc;
try (intros; apply Hfb); try (intros; by apply Hfdiv); try (intros; apply HfA2)).
+ apply Hfa.
+ admit.
+ apply Rle_lt_trans with (rho_def_alt A b).
  apply rho_def_le_alt. apply Hrho.
+ by apply diagonal_dominance_implies_invertibility.
+ apply Hfdiv.
+ apply Rgt_lt. eapply Rle_lt_trans; try apply HG1.
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
         apply rho_def_le_alt. apply Hrho.
      ++ apply Rmult_le_compat_l; last by apply d_mag_def_le_alt.
         repeat apply Rmult_le_pos. nra.
         apply Rplus_le_le_0_compat. nra. apply g_pos.
         apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
         apply /RleP. apply vec_norm_pd.
      ++ assert ((rho_def A b = rho_def_alt A b)%Re \/
                  (rho_def A b < rho_def_alt A b)%Re).
         { pose proof (@rho_def_le_alt t n A b). nra. }
         destruct H. 
         rewrite H; nra.
         apply Rlt_le. apply Rinv_lt_contravar .
         apply Rmult_lt_0_compat.
         apply Rlt_Rminus. apply Hrho.
         apply Rlt_Rminus. eapply Rle_lt_trans.
         apply rho_def_le_alt. apply Hrho.
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
      apply rho_def_le_alt. apply Hrho.
    * apply Rplus_le_le_0_compat. apply g1_pos.
      repeat apply Rmult_le_pos. nra.
      apply Rplus_le_le_0_compat. nra. apply g_pos.
      apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
      apply /RleP. apply vec_norm_pd.
      apply d_mag_def_alt_ge_0.
      apply Rlt_le, Rinv_0_lt_compat. 
      apply Rlt_Rminus. apply Hrho.
+ apply Hfacc.
+ admit.
+ admit.
+ intros. apply Hfx0.
+ intros. by rewrite mxE.
+ intros. apply HfA2.
+ intros. apply Hfb.
Admitted.

 .
.
+ apply Hfa.
+ admit.
+ apply Rle_lt_trans with (rho_def_alt A b).
  apply rho_def_le_alt. apply Hrho.
+ by apply diagonal_dominance_implies_invertibility.
+ apply Hfdiv.
+ apply Rlt_gt.
  apply Rle_lt_trans with
  ( g1 t n.+1
         (n.+1 - 1)%coq_nat +
       INR n.+1 * (1 + g t n.+1) *
       (g1 t n.+1
          (n.+1 - 1)%coq_nat +
        2 * (1 + g t n.+1) *
        (1 + default_rel t) *
        vec_inf_norm
          (FT2R_mat (A1_J A)) *
        d_mag_def_alt A b *
        / (1 - rho_def A b))²)%Re.
  - apply Rplus_le_compat_l. apply Rmult_le_compat_l.
    apply Rmult_le_pos. apply pos_INR.
    apply Rplus_le_le_0_compat. nra. apply g_pos.
    apply Rsqr_incr_1.
    * apply Rplus_le_compat_l. apply Rmult_le_compat_r.
      apply Rlt_le. apply Rinv_0_lt_compat. 
      apply Rlt_Rminus.
      apply Rle_lt_trans with (rho_def_alt A b).
      apply rho_def_le_alt. apply Hrho.
      apply Rmult_le_compat_l.
      ++ repeat apply Rmult_le_pos. nra.
         apply Rplus_le_le_0_compat. nra. apply g_pos.
         apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
         apply /RleP. apply vec_norm_pd.
      ++ apply d_mag_def_le_alt.
    * apply Rplus_le_le_0_compat. apply g1_pos.
      repeat apply Rmult_le_pos. nra.
      apply Rplus_le_le_0_compat. nra. apply g_pos.
      apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
      apply /RleP. apply vec_norm_pd.
      apply d_mag_ge_0.
      apply Rlt_le. apply Rinv_0_lt_compat. 
      apply Rlt_Rminus.
      apply Rle_lt_trans with (rho_def_alt A b).
      apply rho_def_le_alt. apply Hrho.
    * apply Rplus_le_le_0_compat. apply g1_pos.
      repeat apply Rmult_le_pos. nra.
      apply Rplus_le_le_0_compat. nra. apply g_pos.
      apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
      apply /RleP. apply vec_norm_pd.
      admit.
      apply Rlt_le. apply Rinv_0_lt_compat. 
      apply Rlt_Rminus.
      apply Rle_lt_trans with (rho_def_alt A b).
      apply rho_def_le_alt. apply Hrho.
  - apply Rgt_lt. admit. 
+ apply Hfacc.
+ apply Nat.lt_trans with (k_min_alt A b accuracy); last by apply Hk.
  unfold k_min, k_min_alt. admit.
+ admit.
+ apply Hfx0.
+ intros. rewrite mxE. apply Hfdiv.
+ apply HfA2.
+ apply Hfb.
+ apply size_cons.
+ apply size_cons.
+ intros. unfold input_bound_Rcompute in Hinp.
  destruct Hinp as [bnd1 _]. specialize (bnd1 i).
  eapply Rle_lt_trans; last by apply bnd1.
  apply Rmult_le_compat_l. apply Rabs_pos.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    * rewrite Rmult_1_l. apply Rmult_le_compat_l.
      apply Rplus_le_le_0_compat. nra. by apply rho_ge_0.
      apply Rplus_le_compat.
      ++ apply f_error0_bnd. auto. admit.
      ++ admit. 
         (** RHS should be 0 **)
    * apply Rmult_le_compat_r.
      apply Rlt_le. apply Rinv_0_lt_compat. 
      apply Rlt_Rminus.
      apply Rle_lt_trans with (rho_def_alt A b).
      apply rho_def_le_alt. apply Hrho.
      apply Rmult_le_compat_l. nra.
      apply d_mag_def_le_alt.
  - apply Rmult_le_compat_l. nra.
    apply x_bound_exists. admit.
+ unfold input_bound_Rcompute in Hinp.
  destruct Hinp as [_ [bnd2 _]].
  eapply Rle_lt_trans; last by apply bnd2.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    * apply x_bound_exists. admit.
    * rewrite !Rmult_1_l.
      apply f_error0_bnd. auto. admit.
  - apply Rmult_le_compat_l.
    apply Rlt_le. 
    replace (1 / (1 - rho_def A b))%Re with 
            (/ (1 - rho_def A b))%Re by nra.
    apply Rinv_0_lt_compat. 
    apply Rlt_Rminus.
    apply Rle_lt_trans with (rho_def_alt A b).
    apply rho_def_le_alt. apply Hrho.
    apply d_mag_def_le_alt.
+ apply Hinp.
+ intros.
  destruct Hinp as [_ [_ [_ [bnd4 _]]]].
  specialize (bnd4 i).
  eapply Rle_lt_trans; last by apply bnd4.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat. nra. apply g_pos.
  apply Rmult_le_compat_r.
  apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. apply Rabs_pos.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    * apply x_bound_exists. admit.
    * rewrite !Rmult_1_l. apply f_error0_bnd. auto. admit. 
  - apply Rmult_le_compat_l.
    apply Rlt_le. 
    replace (1 / (1 - rho_def A b))%Re with 
            (/ (1 - rho_def A b))%Re by nra.
    apply Rinv_0_lt_compat. 
    apply Rlt_Rminus.
    apply Rle_lt_trans with (rho_def_alt A b).
    apply rho_def_le_alt. apply Hrho.
    apply d_mag_def_le_alt.
+ intros.
  destruct Hinp as [_ [_ [_ [_ [bnd5 _]]]]].
  specialize (bnd5 i).
  eapply Rle_lt_trans; last by apply bnd5.
  apply Rmult_le_compat_l. apply Rabs_pos.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat. nra. apply g_pos.
  apply Rmult_le_compat_r.
  apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. apply Rabs_pos.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    * apply x_bound_exists. admit.
    * rewrite !Rmult_1_l. apply f_error0_bnd. auto. admit. 
  - apply Rmult_le_compat_l.
    apply Rlt_le. 
    replace (1 / (1 - rho_def A b))%Re with 
            (/ (1 - rho_def A b))%Re by nra.
    apply Rinv_0_lt_compat. 
    apply Rlt_Rminus.
    apply Rle_lt_trans with (rho_def_alt A b).
    apply rho_def_le_alt. apply Hrho.
    apply d_mag_def_le_alt.
+ intros.
  destruct Hinp as [_ [_ [_ [_ [_ bnd6]]]]].
  eapply Rle_lt_trans; last by apply bnd6.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    * rewrite Rmult_1_l. apply Rmult_le_compat_l.
      apply Rplus_le_le_0_compat. nra. by apply rho_ge_0.
      apply Rplus_le_compat.
      ++ apply f_error0_bnd. auto. admit.
      ++ admit.
         (** replace RHS by 0 **)
    * apply Rmult_le_compat_r.
      apply Rlt_le. 
      replace (1 / (1 - rho_def A b))%Re with 
              (/ (1 - rho_def A b))%Re by nra.
      apply Rinv_0_lt_compat. 
      apply Rlt_Rminus.
      apply Rle_lt_trans with (rho_def_alt A b).
      apply rho_def_le_alt. apply Hrho.
      apply Rmult_le_compat_l. nra. 
      apply d_mag_def_le_alt.
  - apply Rmult_le_compat_l. nra.
    apply x_bound_exists. admit.
*)
Admitted.

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
intros. unfold jacobi_preconditions in H.
destruct H as [HAA [HlenA [HeqAb H]]].
remember (length A).-1 as n.
unfold jacobi_preconditions_Rcompute in H.
destruct H as [Hfa [Hrho [Hdom [Hfdiv [HG1 [Hfacc [Hk [He0 [Hfx0 [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]].
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
  apply finite_is_finite.
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
      ++ apply finite_is_finite. apply Hfdiv.
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
  apply finite_is_finite.
  specialize (Hfb (@inord n i)).
  rewrite mxE in Hfb. rewrite inordK in Hfb.
  - apply Hfb.
  - rewrite Heqn prednK.
    * rewrite HeqAb. by apply /ssrnat.ltP.
    * by apply /ssrnat.ltP.
+ apply finite_is_finite.
  apply bmult_overflow_implies in Hfacc. by destruct Hfacc .
Qed.
  
  
(** finiteness of dot product **)
Lemma dotprod_finite {t: type} (v : vector t)
(Hg1: (g1 t ((length v).+1 + 1)%coq_nat (length v).+1 <= fmax t)%Re):
(forall xy : ftype t,
  In xy (rev v) ->
  is_finite (fprec t) (femax t) xy = true /\
  (let n := length (rev v) in
   (Rabs (FT2R xy) < sqrt  (fun_bnd t n))%Re)) ->
is_finite (fprec t) (femax t)
  (dotprod v v) = true.
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


Lemma is_finite_xkp1_minus_xk {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
   (m < n.+1)%coq_nat ->
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  is_finite (fprec t) (femax t)
               (BPLUS t
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0)
                  (BOPP t
                     (X_m_jacobi k x0 b A
                        (inord m) ord0))) = true.
Proof.
intros ? ? ? ? ? ? Hcond Hf0.
apply BPLUS_no_overflow_is_finite; try rewrite ?is_finite_Bopp;
try (pose proof (@jacobi_forward_error_bound _ t n);
  unfold forward_error_cond in Hcond;
  unfold rho_def in Hcond;apply H0; try (intros; apply Hcond); try apply size_cons).
unfold Bplus_no_overflow.
pose proof (@generic_round_property t 
            (FT2R
               (X_m_jacobi k.+1 x0 b A 
                  (inord m) ord0) +
             FT2R
               (BOPP t
                  (X_m_jacobi k x0 b A 
                    (inord m) ord0)))).
destruct H0 as [d [e [Hde [Hd [He H0]]]]].
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


Lemma is_finite_Bmult_res {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def A b in 
  let d_mag := d_mag_def A b in 
  (m < n.+1)%coq_nat ->
  forward_error_cond A x0 b ->
  ((0 < f_error 0 b x0 x A - d_mag * / (1 - rho))%Re) ->
  is_finite (fprec t) (femax t)
             (BMULT t (A (inord m) (inord m))
                ((X_m_jacobi k.+1 x0 b A -f
                  X_m_jacobi k x0 b A) 
                   (inord m) ord0)) = true.
Proof.
intros ? ? ? ? ? ? ? Hf0.
apply BMULT_no_overflow_is_finite.
+ unfold forward_error_cond in H0. apply H0.
+ rewrite mxE. apply Bplus_bminus_opp_implies.
  by apply is_finite_xkp1_minus_xk.
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
  rewrite Bminus_bplus_opp_equiv; try rewrite ?is_finite_Bopp;
  try (pose proof (@jacobi_forward_error_bound _ t n );
        unfold forward_error_cond in H0;
        unfold rho_def in H0; apply H2; try (intros; apply H0));
  try by apply is_finite_xkp1_minus_xk.
    pose proof (@BPLUS_accurate' _ t).
    specialize (H2 (X_m_jacobi k.+1 x0 b A 
                      (inord m) ord0)
                    (BOPP t
                      (X_m_jacobi k x0 b A 
                         (inord m) ord0))).
    specialize (H2 (is_finite_xkp1_minus_xk _ _ _ _ _ H H0 Hf0)).
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


Lemma residual_is_finite {t: type} {n:nat}
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
  is_finite (fprec t) (femax t)
    (norm2
       (rev
          (vec_to_list_float n.+1 (resid k)))) = true.
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
    apply Bplus_no_ov_is_finite.
    * pose proof (@jacobi_forward_error_bound _ t n).
      unfold forward_error_cond in Hcond.
      unfold rho_def in Hcond.
      apply H1; try (intros; apply Hcond).
    * rewrite  is_finite_Bopp. 
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
                         (BOPP t
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
    assert (is_finite (fprec t) (femax t)
               (BPLUS t
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0)
                  (BOPP t
                     (X_m_jacobi k x0 b A
                        (inord m) ord0))) = true).
    { apply is_finite_xkp1_minus_xk; try by [].
      by rewrite rev_length length_veclist in Hlenk.
    }
    rewrite Bminus_bplus_opp_equiv.
    * pose proof (@BPLUS_accurate' _ t).
      specialize (H3 (X_m_jacobi k.+1 x0 b A 
                          (inord m) ord0) 
                      (BOPP t
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
    * pose proof (@jacobi_forward_error_bound _ t n).
      unfold forward_error_cond in Hcond.
      unfold rho_def in Hcond.
      apply H3; try (intros; apply Hcond).
    * rewrite is_finite_Bopp.
      pose proof (@jacobi_forward_error_bound _ t n).
      unfold forward_error_cond in Hcond.
      unfold rho_def in Hcond.
      apply H3; try (intros; apply Hcond).
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
  assert (is_finite (fprec t) (femax t)
             (BMULT t (A (inord m) (inord m))
                ((X_m_jacobi k.+1 x0 b A -f
                  X_m_jacobi k x0 b A) 
                   (inord m) ord0)) = true).
  { apply is_finite_Bmult_res; try by [].
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
  assert (is_finite (fprec t) (femax t)
               (BPLUS t
                  (X_m_jacobi k.+1 x0 b A
                     (inord m) ord0)
                  (BOPP t
                     (X_m_jacobi k x0 b A
                        (inord m) ord0))) = true).
  { apply is_finite_xkp1_minus_xk; try by [].
     by rewrite rev_length length_veclist in Hlenk.
  }
  rewrite Bminus_bplus_opp_equiv.
  - pose proof (@BPLUS_accurate' _ t).
    specialize (H4 (X_m_jacobi k.+1 x0 b A 
                        (inord m) ord0)
                   (BOPP t
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
  - pose proof (@jacobi_forward_error_bound _ t n).
    unfold forward_error_cond in Hcond.
    unfold rho_def in Hcond.
    apply H4; try (intros; apply Hcond).
  - rewrite is_finite_Bopp.
    pose proof (@jacobi_forward_error_bound _ t n).
    unfold forward_error_cond in Hcond.
    unfold rho_def in Hcond.
    apply H4; try (intros; apply Hcond).
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
             is_finite (fprec t) (femax t) xy.1 = true /\
             is_finite (fprec t) (femax t) xy.2 = true /\
             is_finite (fprec t) (femax t)
               (BPLUS t xy.1 (BOPP t xy.2)) = true).
{ (** if the  residual is finite then 
      x_k+1 - x_k is finite
  **)
  intros. 
  pose proof (@residual_is_finite  t n A b k Hcond Hf0).
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
      assert (forall i : 'I_n.+1,
                is_finite (fprec t) (femax t) (A i i) = true) by apply Hcond.
      assert ((rho < 1)%Re) by apply Hcond.
      assert (FT2R_mat A \in unitmx). 
      { apply Hcond. }
      assert (forall i : 'I_n.+1,
              is_finite (fprec t) (femax t)
                (BDIV t (Zconst t 1) (A i i)) = true) by apply Hcond.
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
    pose proof (@residual_is_finite  t n A  b k Hcond He0).
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
  - by apply residual_is_finite .
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
                     is_finite (fprec t) (femax t) xy.1 = true /\
                     is_finite (fprec t) (femax t) xy.2 = true /\
                     is_finite (fprec t) (femax t)
                       (BMULT t xy.1 xy.2) = true).
            { intros.
              pose proof (@residual_is_finite  t n A b k Hcond He0).
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
                assert (is_finite _ _ (A1_J A (inord m) ord0) = true /\
                        is_finite _ _  ((X_m_jacobi k.+1 x0 b A -f
                                          X_m_jacobi k x0 b A) (inord m) ord0) = true).
                { apply bmult_overflow_implies  in H3.
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
destruct H as [HfA [Hrho [HinvA [Hfbdiv [HG [Hfacc [Hk [He0 [Hfx0 [HfA1_inv [HfA2 [Hfb [size_cons Hinp]]]]]]]]]]]]].
split.
+ unfold acc2. by apply finite_is_finite.
+ exists (k_min A b acc).+1. 
  repeat split.
  - by apply /ssrnat.ltP.
  - intros. apply finite_is_finite.
    apply residual_is_finite.
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
                                    rewrite  Heqrho Heqd_mag Heqe_0 HeqGamma /x0 Heqx  /acc2.
                                     assert ((1 / rho_def A b)%Re = (/ rho_def A b)%Re). { nra. }
                                     rewrite H5.
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
      unfold forward_error_cond. repeat split; try (by intros); try by (intros; apply Hinp); try apply Hrho. 
      ++  apply Hrho.
      ++ apply size_cons.
      ++ apply size_cons.
      ++ apply He0.
    * by unfold acc2. 
Qed.


Lemma jacobi_iteration_bound_lowlevel' {t: type} :
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
unfold jacobi_preconditions in H.
destruct H as [HAA [HlenA [HeqAb H]]].
apply jacobi_iteration_bound_lowlevel'.
+ by apply jacobi_precond_compute_implies_math .
+ apply HeqAb. 
+ apply HlenA.
Qed.


End WITH_NANS.