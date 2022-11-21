(*** Error bounds for matrix matrix multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Require Import dot_prod_defn generalize float_model_generic 
     inf_norm_properties lemmas matrix_vec_mult_bound matrix_matrix_mult_bound
     real_func_model_generic.

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

Definition FT2R_list (l : list (ftype Tsingle)) : list R :=  map FT2R l.


(** not entirely in correct form. need to connect A, A1^{-1}. A2 **)
Theorem iterative_round_off_error {n:nat} :
  forall (A A1 A2 inv_A1: 'M[ftype Tsingle]_n.+1),
  (** ||A_1^{-1}|| < 1 **)
  matrix_inf_norm (S_mat (FT2R_mat inv_A1) (FT2R_mat A2)) < 1 ->
  (** Relation between A, A_1, A_2 **)
  (** Relation between A_1, inv_A1 **)
  forall (x_l b: list (ftype Tsingle)),
  let x0 := listR_to_vecR (FT2R_list x_l) in
  let b_real := listR_to_vecR (FT2R_list b) in
  let x0_f := list_to_vec_float x_l in
  let b_f := list_to_vec_float b in
  exists f:R,
  forall k:nat, 
  vec_inf_norm (listR_to_vecR (FT2R_list
                (vec_to_list_float n.+1 (@X_m_generic _ _ n n x0_f b_f inv_A1 A2))) - 
                @X_m_real_generic n n x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2)) <=
  f *  error_sum k.+1 (@matrix_inf_norm n.+1 (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))).
Admitted.




End WITHNANS.