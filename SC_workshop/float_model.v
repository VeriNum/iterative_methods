(** This file contains the floating-point functional model for Jacobi 
iterations on a small model problem **)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.

(*** Simplified real functional model ***)

(*** A = 1 / (h^2) [ 2   -1   0 ]
                   [-1    2  -1 ]
                   [ 0   -1   2 ]

     A_1 = (h^2)/2 [ 1  0  0 ]
                   [ 0  1  0 ]
                   [ 0  0  1 ]

     A_2 = 1/(h^2) [ 0  -1  0 ]
                   [-1   0 -1 ]
                   [ 0  -1  0 ]

     S   = - (inv(A_1) * A_2)
         = (-0.5) [ 0  -1  0 ]
                  [-1   0 -1 ]
                  [ 0  -1  0 ]

    The matrix A is decomposed as A = A_1 + A_2 with A_1 diagonal and 
    A_2 (lower + upper) triangular.

    Jacobi updates are then x_{k+1} = inv(A_1) * b - inv(A_1) * (A_2) * x_{k}
                                    = inv(A_1) * b + S * x_k 

***)


Definition default_val := 0. 

Definition list_nth (n:nat) x : (ftype Tsingle) :=
  @List.nth (ftype Tsingle) n x default_val.



Definition S_mat_mul x' :=
  let x  := list_nth 0 x' in 
  let y  := list_nth 1 x' in
  let z  := list_nth 2 x' in  
  let x1 := (0 * x +  (0.5) * y + 0 * z) in
  let y1 := ((0.5) * x + 0 * y + (0.5) * z) in 
  let z1 := (0 * x + (0.5) * y + 0 * z) in 
  [x1 ; y1 ; z1]
.


Definition A1_inv_mul_b x' h:= 
  let x  := @List.nth (ftype Tsingle) 0 x' default_val in 
  let y  := @List.nth (ftype Tsingle) 1 x' default_val in
  let z  := @List.nth (ftype Tsingle) 2 x' default_val in  
  let x1 := ((0.5 * h * h ) * x +  0 * y + 0 * z) in
  let y1 := (0 * x + (0.5 *h * h ) * y + 0 * z) in 
  let z1 := (0 * x + 0 * y + (0.5 *h * h) * z) in 
  [x1 ; y1 ; z1]
.



Fixpoint vec_add (l1 l2 :list (ftype Tsingle)) : list ((ftype Tsingle)):=
  match l1, l2 with 
  | x :: tl, y::tl' => (x+y) ::vec_add tl tl'
  | _, _ => nil
end
.

Goal vec_add [1;2] [1;2] = [2;4]. unfold vec_add. Abort.


Fixpoint X_m (m : nat) x0 b h : list (ftype Tsingle):=
  match m with
  | O => x0
  | S p => 
      vec_add (S_mat_mul (X_m p x0 b h)) (A1_inv_mul_b b h)
  end
.

Definition b_float := [1;1;1].


End WITHNANS.

