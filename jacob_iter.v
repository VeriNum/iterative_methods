From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix classical_sets.
From mathcomp.analysis Require Import Rstruct reals.
Require Import dot_prod_defn generalize float_model_generic 
     inf_norm_properties lemmas matrix_vec_mult_bound matrix_matrix_mult_bound
     real_func_model_generic iter_theorem.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


(*** ||A \otimes v - A v|| <= max_i {e_i}
     |A_i \otimes v - A_i v_2| <= e_i
***)
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section WITHNANS.
Context {NANS: Nans}.

Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).

Definition A1_J {n:nat} (A: 'M[ftype Tsingle]_n.+1) : 'M[ftype Tsingle]_n.+1:=
  \matrix_(i,j) 
    (if (i==j :> nat) then (A i i) else 0%F32).



Lemma x_m_jacobi_compat {m n:nat} 
  (A: 'M[ftype Tsingle]_n.+1) (x0_f b_f : 'cV[ftype Tsingle]_n.+1):
  let inv_A1 := A1_inv_J A in 
  let A2 := A2_J  A in 
  let A1 := A1_J A in
  @X_m_generic _ _ m n x0_f b_f inv_A1 A2 = 
  @X_m_Jacobi _ n m x0_f b_f A.
Proof.
by induction m; try rewrite /= /jacobi_iter IHm.
Qed.


Lemma A_mat_decompose_compat {n:nat} (A: 'M[ftype Tsingle]_n.+1):
  let inv_A1 := A1_inv_J A in 
  let A2 := A2_J  A in 
  let A1 := A1_J A in
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  matrix_inf_norm (FT2R_mat (A +f (-f (A1 +f A2)))) <=
  matrix_inf_norm (FT2R_mat A) * d + e.
Proof.




Admitted.

Lemma A1_inv_A1_compat{n:nat} (A: 'M[ftype Tsingle]_n.+1):
  let inv_A1 := A1_inv_J A in 
  let A2 := A2_J  A in 
  let A1 := A1_J A in
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  matrix_inf_norm (FT2R_mat (A1 *f inv_A1 ) - (FT2R_mat A1) *m (FT2R_mat inv_A1)) <=
  mat_mat_mult_err_bnd A1 inv_A1.
Admitted.



Theorem jacobi_iterative_round_off_error {n:nat} :
  (1 < n.+1 /\ n.+1< (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in 
  (forall i k m n p :nat, (i < m.+1)%nat /\ (k < n.+1)%nat -> 
    (forall (a b : ftype Tsingle) (A1: 'M[ftype Tsingle]_(m.+1, n.+1))
            (A2: 'M[ftype Tsingle]_(n.+1, p.+1)),
      In (a, b)
        (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
           (vec_to_list_float n.+1 (\col_j (A2 j (inord k))))) ->
      is_finite (fprec Tsingle) (femax Tsingle) a = true /\
      is_finite (fprec Tsingle) (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re /\
      (Rabs (FT2R b) <=
       sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re))->

  forall (A: 'M[ftype Tsingle]_n.+1),
  (** ||A_1^{-1}A_2|| < 1 **)
  let inv_A1 := A1_inv_J A in 
  let A2 := A2_J  A in 
  let A1 := A1_J A in
  matrix_inf_norm (S_mat (FT2R_mat inv_A1) (FT2R_mat A2)) < 1 ->
  forall (x_l b: list (ftype Tsingle)),
  let x0 := listR_to_vecR (FT2R_list x_l) in
  let b_real := listR_to_vecR (FT2R_list b) in
  let x0_f := list_to_vec_float x_l in
  let b_f := list_to_vec_float b in
  let x := invmx (FT2R_mat A) *m b_real in
  x != 0 ->
  forall k:nat, 
  let f:= tau k x (fun m:nat => @X_m_Jacobi _ n m x0_f b_f A) inv_A1 A1 A2 b_f in
  vec_inf_norm (FT2R_mat (@X_m_Jacobi _ n k x0_f b_f A) - 
                @X_m_real_generic n k x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2)) <=
  f *  error_sum k.+1 (@matrix_inf_norm n.+1 (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))).
Proof.
intros.
rewrite -x_m_jacobi_compat.
pose proof (A_mat_decompose_compat  A). simpl in H3.
pose proof (A1_inv_A1_compat A). simpl in H4. simpl.
assert ((fun m : nat => X_m_Jacobi m x0_f b_f A) = 
         (fun m : nat => X_m_generic m x0_f b_f inv_A1 A2)).
{ apply Logic.FunctionalExtensionality.functional_extensionality.
  intros. by rewrite -x_m_jacobi_compat.
} rewrite H5.
apply (@iterative_round_off_error _ n H H0 A A1 A2 inv_A1 H1 H3 H4 _ _ H2 k).
Qed.


End WITHNANS.




