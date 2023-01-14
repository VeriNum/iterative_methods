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

(**
Definition diag_vector_mult {ty} {n:nat} (v1 v2: 'cV[ftype ty]_n.+1)
  : 'cV[ftype ty]_n.+1 :=
  \col_i (BMULT ty (nth (n.+1.-1 -i) (vec_to_list_float n.+1 v1) (Zconst ty 0))
            (nth (n.+1.-1 - i) (vec_to_list_float n.+1 v2) (Zconst ty 0))).

Definition jacobi_iter {ty} {n:nat} x0 b (A: 'M[ftype ty]_n.+1) : 
  'cV[ftype ty]_n.+1 :=
   let r := b -f ((A2_J A) *f x0) in
   diag_vector_mult (A1_inv_J A) r.
**)

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

Definition A2_J_real {n:nat} (A: 'M[R]_n.+1): 
  'M[R]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then 0%Re else A i j.

(** Define real real functional model **)
Definition x_fix {n:nat} x b (A: 'M[R]_n.+1) :
  'cV[R]_n.+1 :=
  let r := b - ((A2_J_real A) *m x) in
  diag_matrix_vec_mult_R (A1_diag A) r.

Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1)
  : 'cV[R]_n.+1:=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A_real in
  FT2R_mat x_k - x.





End WITHNANS.