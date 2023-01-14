From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
(*Require Import float_model_generic. *)
Require Import floatlib jacob_list_fun_model fma_dot_mat_model.

Require Import common fma_dot_acc float_acc_lems.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section WITHNANS.
Context {NANS: Nans}. 

Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).


Definition FT2R_mat {m n: nat} {ty} (A : 'M[ftype ty]_(m.+1, n.+1)) :
   'M[R]_(m.+1, n.+1):=
  \matrix_(i, j) FT2R (A i j).


(** Write a lemma for matrix-vector multiplication **)
Lemma matrix_vec_mult_bound {n:nat} {ty}:
  forall (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1),
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
   



End WITHNANS.