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

Section WITH_NANS.

Context {NANS: Nans}.

(** Computable definition of rho in reals **)
Definition rho_def_alt  {t: type} {n:nat} (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in   
  let R := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
              matrix_inf_norm (A2_real))%Re in
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
  let R := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
            matrix_inf_norm (A2_real))%Re in
  let delta := default_rel t in
  ((g t n.+1 * (1 + delta) + delta) *
                    (( ((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) *
                      (1 + delta) + default_abs t) *
                     vec_inf_norm b_real) +
                    (1 + g t n.+1) * g1 t n.+1 (n.+1 - 1) *
                    (1 + delta) *
                    (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) *
                     (1 + delta) + default_abs t) +
                    g1 t n.+1 (n.+1 - 1) +
                    (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * delta +
                     default_abs t) * vec_inf_norm b_real +
                    ((((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * (1 + delta) + delta) * R +
                     (((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * default_abs t +
                      default_abs t) *
                     matrix_inf_norm (A2_real)) *
                     ( ((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                       vec_inf_norm b_real * (/ (1 - R))))%Re.

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
  let Gamma := FT2R (BMULT acc acc) in
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
  (forall i j, finite (A i j)) /\
  (** constant for the contraction mapping **)
  (rho < 1)%Re /\
  (** Invertibility of A **)
  A_real \in unitmx /\
  (** Finiteness of the inverse of diagonal elements of A **)
  (forall i : 'I_n.+1, finite (BDIV (Zconst t 1) (A i i))) /\
(** Constraint on Gamma **)
  (FT2R (BMULT accuracy accuracy) >
     g1 t n.+1 (n.+1 - 1)%coq_nat +
     INR n.+1 * (1 + g t n.+1) *
     (g1 t n.+1 (n.+1 - 1)%coq_nat +
      2 * (1 + g t n.+1) * (1 + default_rel t) *
      vec_inf_norm (FT2R_mat (A1_J A)) *
      d_mag_def A b * / (1 - rho_def A b))²)%Re /\
  (** Gamma is finite **)
  finite (BMULT accuracy accuracy) /\
  (** constraint on k **)
  ((k_min A b accuracy < k)%coq_nat /\ (0 < k)%coq_nat) /\
  (** lower bound on the initial error **)
  (0 < f_error 0 b x0 x A - d_mag / (1 - rho))%Re /\
  (** finiteness of x0 **)
  (forall i : 'I_n.+1, finite (x0 i ord0)) /\
  (** finitenes of A1^{-} **)
  (forall i, finite (A1_inv_J A i ord0)) /\
  (** finiteness of A2 **)
  (forall i j, finite (A2_J A i j)) /\
  (** finitenes of b **) 
  (forall i, finite (b i ord0)) /\
  (** constraint on the dimension **)
  @size_constraint t n /\
  (** constraint on bounds for input **)
  input_bound A x0 b.


End WITH_NANS.
