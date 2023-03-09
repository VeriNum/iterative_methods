From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.


Set Bullet Behavior "Strict Subproofs". 


(*** ||A \otimes v - A v|| <= max_i {e_i}
     |A_i \otimes v - A_i v_2| <= e_i
***)
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.



Fixpoint X_m_real_generic {n:nat} (m: nat) x0 b (inv_A1 A2: 'M[R]_n.+1) : 
  'cV[R]_n.+1 :=
  match m with
  | O => x0
  | S p => ((-(inv_A1 *m A2)) *m (X_m_real_generic p x0 b inv_A1 A2)) +
           (inv_A1 *m b)
  end.
