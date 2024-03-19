From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

Require Import floatlib fma_floating_point_model inf_norm_properties.

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

Definition scale_ith_row {n : nat} (i : 'I_n.+1) (x : R) (A : 'M_n.+1) :=
  let Ai' := scalemx x (row i A) in 
  let A' := row' i A in 
  xrow 0 i (col_mx Ai' A').

Fixpoint scale_rows_by_diag_aux {n : nat} (A : 'M_n.+1) (i : nat) {struct i} :=
  match i with 
  | 0%nat => scale_ith_row (inord i) (1 / (A 0 0)) A 
  | S i' => let aux_res := scale_ith_row (inord i) (1 / (A (inord i) (inord i))) A in 
      scale_rows_by_diag_aux aux_res i'
  end.

Definition scale_rows_by_diag {n : nat} (A : 'M_n.+1) :=
  scale_rows_by_diag_aux A n.

Definition A : 'M_3.+1 := \matrix_(i < 4, j < 4) (i + j + 1).
Ltac easy_mat := rewrite !mxE; auto.

Fixpoint scale_AB_by_A_diag_aux {n : nat} (AB : 'M_n.+1 * 'M_n.+1) (i : nat) {struct i} :=
  let A := fst AB in 
  let B := snd AB in 
  match i with 
  | 0%nat => (scale_ith_row (inord i) (1 / (A 0 0)) A, 
      scale_ith_row (inord i) (1 / (A 0 0)) B)
  | S i' => let aux_res := 
    ( scale_ith_row (inord i) (1 / (A (inord i) (inord i))) A, 
      scale_ith_row (inord i) (1 / (A (inord i) (inord i))) B) in 
    scale_AB_by_A_diag_aux aux_res i'
  end.

(* Why is this not working? *)

(* Fail Fixpoint scale_rows_by_diag_aux_wrong {n : nat} (A : 'M_n.+1) (i : nat) {struct i} :=
  if (i =? 0)%nat then scale_ith_row (inord i) (A 0 0) A 
    else let aux_res := scale_ith_row (inord i) (A (inord i) (inord i)) A in 
        let j := i.-1 in
      scale_rows_by_diag_aux_wrong aux_res j. *)

Definition scale_AB_by_A_diag {n : nat} (A B : 'M_n.+1) :=
  scale_AB_by_A_diag_aux (A, B) n.

(* Another way to update a row? *)
Definition update_row {n : nat} (i : nat) (v : 'rV[R]_n.+1) (A : 'M[R]_n.+1)  :=
  \matrix_(x < n.+1, y < n.+1)
    (if (x == (inord i)) then (v 0 y) else (A x y)).


Definition sc_mul {m n} (A : 'M[R]_(m, n)) (c: R) (r: 'I_m) : 'M[R]_(m, n) :=
  \matrix_(i < m, j < n) if i == r then c * (A i j) else A i j. 


Definition add_mul {m n} (A : 'M[R]_(m, n)) (c : R) (r1 r2 : 'I_m) : 'M[R]_(m,n) :=
  \matrix_(i < m, j < n) if i == r2 then (A r2 j) + (c * (A r1 j)) else A i j. 










Variable n : nat.
Variable A : 'M[R]_n.

Definition B := diag_const_mx n (1%R).

(* Variable i : 'I_n.
Variable a_ii : R. *)

(* row i A : i-th row of A *)
(* row' i A : A with i-th row spliced out *)
(* xrow i1 i2 A : A with rows i1 and i2 interchanged *)


