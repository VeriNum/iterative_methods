(*** Error bounds for matrix vector multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Require Import dot_prod_defn generalize float_model_generic.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 



(*** ||A \otimes v - A v|| <= max_i {e_i}
     |A_i \otimes v - A_i v_2| <= e_i
***)

Definition e_i {ty} {n:nat} (i : 'I_n.+1) 
  (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1) := 
  let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
  let l2 := vec_to_list_float n.+1 v in
  let L := combine l1 l2 in
  let rs := dot_prodR (Flist_to_Rlist_pair_abs L) in
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n in
  rs * ((1 + d)^n -1) + nr * e * (1+d)^(n-1) + e * ((1+d)^(n-1) -1) / d.


Definition mat_vec_mult_err_bnd {ty} {n:nat} 
 (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1):=
 bigmaxr 0 [seq (e_i i A v) | i <- enum 'I_n.+1].


(** Proof that that the rounding error for 
    matrix vector mult is bounded by  'mat_vec_mult_err_bnd'
**)











End WITHNANS.