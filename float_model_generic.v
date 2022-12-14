From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
Require Import dot_prod_defn.
Set Bullet Behavior "Strict Subproofs". 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITHNANS.
Context {NANS: Nans}. 


(*** Define a coercion from a float list to a float vector **)
Definition list_to_vec_float {n:nat} 
(l : list (ftype Tsingle)): 'cV[ftype Tsingle]_n := 
\col_(i < n) (List.nth (nat_of_ord i) l 0%F32).

(** We can represent a matrix of floats using the
  mathcomp definition of matrix
**)


(** Define matrix_addition **)
Definition addmx_float {ty} {m n:nat} (A B: 'M[ftype ty]_(m,n))
  : 'M[ftype ty]_(m,n) :=
  \matrix_(i, j) (sum ty (A i j) (B i j)).

Fixpoint vec_to_list_float {ty} {n:nat} (m:nat) (v :'cV[ftype ty]_n.+1)
   : list (ftype ty) := 
   match m with 
   | O => []
   | S p => [v (@inord n p) ord0] ++ vec_to_list_float p v
   end.


(** Matrix multiplication as dot product  **)
Definition mulmx_float {ty} {m n p : nat} 
  (A: 'M[ftype ty]_(m.+1,n.+1)) (B: 'M[ftype ty]_(n.+1,p.+1)) : 
  'M[ftype ty]_(m.+1,p.+1):=
  \matrix_(i, k)
    let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
    let l2 := vec_to_list_float n.+1 (\col_(j < n.+1) B j k) in
    let l := combine l1 l2 in
    dot_prodF ty l.


(*** Example: A = [1, 2; 3, 4] ***)

Definition matrix_of_floats : 'M[ftype Tsingle]_2 := 
\matrix_(i < 2, j < 2)
   if (i == 0%N :> nat) then
    (if (j == 0%N :> nat) then 1%F32 else 2%F32) else
    (if (j == 0%N :> nat) then 3%F32 else 4%F32).



Lemma mul_mat:
  (mulmx_float  matrix_of_floats  matrix_of_floats) ord0 ord0 =
  ((1*1)%F32 + (2 * 3)%F32)%F32.
Proof.
rewrite mxE.
simpl. rewrite !mxE.
assert (@ord0 2%N == 0%N :> nat).
{ by []. } rewrite H.
assert (@inord 1 0 == 0%N :> nat).
{ by rewrite inordK. } rewrite H0.
assert (@inord 1 (1-0) == 0%N :> nat = false).
{ by rewrite inordK. } rewrite H1.
unfold dot_prodF. 
unfold prod_fixF. unfold prod, sum.
rewrite /sum_fixF //=. 
Qed.


Lemma add_mat:
  (addmx_float  matrix_of_floats  matrix_of_floats) ord0 ord0 = (1 + 1)%F32.
Proof.
rewrite mxE. unfold sum.
rewrite !mxE. 
assert (@ord0 2%N == 0%N :> nat).
{ by []. } by rewrite H. 
Qed.


Definition opp_mat {ty} {m n: nat} (A : 'M[ftype ty]_(m.+1, n.+1)) 
  : 'M[ftype ty]_(m.+1, n.+1) :=
  \matrix_(i,j) (BOPP ty (A i j)). 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).


Fixpoint X_m_generic {ty} (m n: nat) x0 b (inv_A1 A2: 'M[ftype ty]_n.+1) : 
  'cV[ftype ty]_n.+1 :=
  match m with
  | O => x0
  | S p => ((-f (inv_A1 *f A2)) *f (X_m_generic p x0 b inv_A1 A2)) +f
           (inv_A1 *f b)
  end.


(** Functional model for Jacobi iteration **)
Definition A1_inv_J {n:nat} (A: 'M[ftype Tsingle]_n.+1) : 'M[ftype Tsingle]_n.+1:=
  \matrix_(i,j) 
    (if (i==j :> nat) then (1 / (A i i))%F32 else 0%F32).



Definition A2_J {n:nat} (A: 'M[ftype Tsingle]_n.+1): 
  'M[ftype Tsingle]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then 0%F32 else A i j.



Definition jacobi_iter {n:nat} x0 b (A: 'M[ftype Tsingle]_n.+1) : 
  'cV[ftype Tsingle]_n.+1 :=
   let S_J := (-f ((A1_inv_J A) *f (A2_J A))) in 
   let f_J := ((A1_inv_J A) *f b) in 
   (S_J *f x0 +f f_J).

Fixpoint iter {A} (f : A -> A) (n:nat) (x:A) :=
  match n with 
  | O => x 
  | S n' => iter f n' (f x)
  end.


Fixpoint X_m_Jacobi  {n:nat} m x0 b (A: 'M[ftype Tsingle]_n.+1) :
  'cV[ftype Tsingle]_n.+1 :=
  match m with 
  | O => x0
  | p.+1 => jacobi_iter (X_m_Jacobi p x0 b A) b A
  end.

(*
Fixpoint X_m_Jacobi_1 (m n: nat) x0 b  (A: 'M[ftype Tsingle]_n.+1): 
  'cV[ftype Tsingle]_n.+1 :=
  match m with
  | O => x0
  | S p => let S_J := (-f ((A1_inv_J A) *f (A2_J A))) in 
           let f_J := ((A1_inv_J A) *f b) in 
           (S_J *f (X_m_Jacobi_1 p x0 b A)) +f f_J 
  end.
*)


Lemma jacobi_equiv (m n: nat) x0 b  (A: 'M[ftype Tsingle]_n.+1):
  jacobi_iter (X_m_Jacobi m x0 b A) b A =
  X_m_Jacobi m (jacobi_iter x0 b A) b A.
Proof.
induction m.
+ by simpl.
+ simpl. by rewrite IHm.
Qed.



Lemma iter_check (m n: nat) x0 b  (A: 'M[ftype Tsingle]_n.+1):
  X_m_Jacobi m x0 b A = 
  iter (fun x0 => jacobi_iter x0 b A) m x0.
Proof.
elim: m x0 => [ |m IHm] x0.
+ by simpl.
+ simpl. specialize (IHm (jacobi_iter x0 b A)).
  by rewrite -IHm jacobi_equiv. 
Qed.
  



End WITHNANS.