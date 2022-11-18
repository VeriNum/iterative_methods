(*** Error bounds for matrix matrix multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Require Import dot_prod_defn generalize float_model_generic 
               inf_norm_properties lemmas matrix_vec_mult_bound.

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

(** Define the maximum error for matrix-matrix multiplication **)
Definition row_e_j {n:nat} (i : 'I_n.+1) (A1 A2: 'M[ftype Tsingle]_n.+1) :=
  \sum_(j < n.+1) (e_i j A1 (\col_j (A2 j i))).

Definition mat_mat_mult_err_bnd {n:nat} (A1 A2: 'M[ftype Tsingle]_n.+1):=
 bigmaxr 0%Re [seq (row_e_j i A1 A2) | i <- enum 'I_n.+1].







End WITHNANS.