(** This file contains definitions of and lemmas about the real 
functional model **)


From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From mathcomp.analysis Require Import Rstruct.
From mathcomp Require Import matrix all_ssreflect all_algebra ssralg ssrnum bigop.

Set Bullet Behavior "Strict Subproofs". 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import lemmas.
Import List ListNotations.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

(*** Functional model for the iterative solution ***)

(** Specialized to the Jacobi iterate for the symmetric tridiagonal
    matrix:
    (1'h^2) [2 -1 0; -1 2 -1; 0 -1 2]
**)
(** define a tridiagonal system **)
Definition A (n:nat) (h:R) := \matrix_(i<n, j<n)
   if (i==j :> nat) then (2 / h^2) %Re else
      (if ((i-j)%N==1%N :>nat) then (-1 / h^2)%Re else
            (if ((j-i)%N==1%N :>nat) then (-1/ h^2)%Re else 0)).

Definition A1 (n:nat) (h:R) := \matrix_(i < n, j < n)
      if (i == j :> nat) then (A n h) i j else 0.

Definition A2 (n:nat) (h:R) := \matrix_(i < n, j < n)
  ((A n h) i j - (A1 n h) i j).
  
Definition inv_A1 (n:nat) (h:R) := \matrix_(i < n, j < n)
      if (i == j :> nat) then (1/ (A1 n h) i j) else 0.


Definition S_mat (n:nat) (h:R) := -(inv_A1 n h) *m (A2 n h).

Definition b_real : list R := [1;1;1].


Fixpoint X_m_real (m n:nat) (x0 b: 'cV[R]_n) (h:R) : 'cV[R]_n:=
  match m with
  | O => x0
  | S p => S_mat n h *m (X_m_real p x0 b h) + inv_A1 n h *m b
  end.

Lemma X_m_real_iter {n:nat} (k: nat) (x0 b: 'cV[R]_n) (h:R) :
    let xkr := X_m_real k x0 b h in
    X_m_real k.+1 x0 b h = X_m_real 1 xkr b h.
Proof. simpl; auto. Qed.


Close Scope R_scope. 
