(*** Error bounds for matrix matrix multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix classical_sets.
From mathcomp.analysis Require Import Rstruct reals.
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


(** Define theta_x **)

(*
Definition theta_x  {n:nat} (k:nat)
 (x_hat : nat ->'cV[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1):=
 let s:= [seq (INR (nat_of_ord i)) | i <- enum 'I_k] in
 sup [set x | x \in s].
*)

(** Since, we have a finite set, I can just use bigmaxr instead of
    sup
**)
Definition theta_x  {n:nat} (k:nat)
 (x_hat : nat ->'cV[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1) :=
 let s := [seq (vec_inf_norm (@FT2R_mat n 0%nat (x_hat (nat_of_ord i))) 
                / vec_inf_norm x)%Re | i <- enum 'I_k.+1] in
 bigmaxr 0%Re s.

Print bigmaxr.


(** Revising the bound E_3 **)
Fixpoint vec_to_list_real {n:nat} (m:nat) (v :'cV[R]_n.+1)
   : list R := 
   match m with 
   | O => []
   | S p => [v (@inord n p) ord0] ++ vec_to_list_real p v
   end.

Definition Rlist_pair_abs (L : list (R * R)) :=
  map (fun a => (Rabs (fst a), Rabs (snd a))) L.


Lemma sum_Rabs_pair_rel:
  forall (L: list (R * R)),
  0 <= sum_fixR (prod_fixR (Rlist_pair_abs L)).
Proof.
intros.
induction L.
+ simpl. apply /RleP. apply Rle_refl.
+ simpl. apply /RleP. 
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; apply Rabs_pos.
  apply /RleP. apply IHL.
Qed.


Definition e_i_real {n:nat}  (i : 'I_n.+1) (k:nat)
  (A : 'M[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1) :=
  let A_real := FT2R_mat A in 
  let l1 := vec_to_list_real n.+1 (\row_(j < n.+1) A_real i j)^T in
  let l2 := vec_to_list_real n.+1 x in
  let L := combine l1 l2 in
  dot_prodR (Rlist_pair_abs L).

Definition E_3 {n:nat} (k:nat) 
  (A : 'M[ftype Tsingle]_n.+1) (b : 'cV[ftype Tsingle]_n.+1) 
  (x_hat : nat -> 'cV[ftype Tsingle]_n.+1) (x : 'cV[R]_n.+1) :=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in
  ((theta_x k x_hat x) * bigmaxr 0%Re [seq (e_i_real i k A x) | i <- enum 'I_n.+1]
    * ((1 + d)^n.+1 -1) + nr * e * (1+d)^(n.+1 -1)%coq_nat + 
   e * ((1+d)^(n.+1-1)%coq_nat -1) / d)%Re.


Definition tau {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in 
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3_def := E_3 k S_hat b x_hat x in 
  ((matrix_inf_norm S * d + E_2 * d + E_2) * ((theta_x k x_hat x) * vec_inf_norm x) + 
  (E_3_def * d + (vec_inf_norm f) * d + E_1* d + E_3_def + E_1 + e))%Re.

(*
Definition tau {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3 := mat_vec_mult_err_bnd S_hat (x_hat k) in
  ((matrix_inf_norm S * d + E_2 * d + E_2) * ((theta_x k x_hat x) * vec_inf_norm x) + 
  (E_3 * d + (vec_inf_norm f) * d + E_1* d + E_3 + E_1 + e))%Re.
*)


Definition tau_m {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3_def := E_3 k S_hat b x_hat x in
  ((matrix_inf_norm S * d + E_2 * d + E_2) * vec_inf_norm (FT2R_mat (x_hat k)) + 
  (E_3_def * d + (vec_inf_norm f) * d + E_1* d + E_3_def + E_1 + e))%Re.


(*
Definition tau_m {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3 := mat_vec_mult_err_bnd S_hat (x_hat k) in
  ((matrix_inf_norm S * d + E_2 * d + E_2) * vec_inf_norm (FT2R_mat (x_hat k)) + 
  (E_3 * d + (vec_inf_norm f) * d + E_1* d + E_3 + E_1 + e))%Re.

*)


Lemma pow_invert_2: forall x y z :R,
  (0 < z)%Re ->  (x / z <= y)%Re -> (x <= y * z)%Re.
Proof.
intros.
replace x with (x * 1)%Re by nra.
assert (1%Re = (/z * z)%Re).
{ symmetry. apply Rinv_l. nra. } rewrite H1.
replace (x * (/z * z))%Re with ((x / z) * z)%Re by nra.
apply Rmult_le_compat_r.
+ nra.
+ nra.
Qed.


Lemma vec_norm_definite {n:nat} (v : 'cV[R]_n.+1):
  v != 0 ->
  (0 < vec_inf_norm v)%Re.
Proof.
intros.
unfold vec_inf_norm.
assert (exists i, v i 0 != 0).
{ by apply /cV0Pn. } destruct H0 as [i H0].
apply Rlt_le_trans with 
[seq Rabs (v i0 0) | i0 <- enum 'I_n.+1]`_i.
+ rewrite seq_equiv. rewrite nth_mkseq; last by []. 
  apply Rabs_pos_lt. apply /eqP. 
  by rewrite inord_val.
+ apply /RleP. apply (@bigmaxr_ler _ 0%Re [seq Rabs (v i0 0) | i0 <- enum 'I_n.+1] i).
  by rewrite size_map size_enum_ord.
Qed.

Lemma mat_err_bnd_pd {n:nat}
  (A1 A2 : 'M[ftype Tsingle]_n.+1) :
  0%Re <= mat_mat_mult_err_bnd A1 A2.
Proof.
unfold mat_mat_mult_err_bnd.
apply bigmax_le_0.
+ apply /RleP; apply Rle_refl.
+ intros. 
  rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
  unfold row_e_j.
  apply big_ge_0_ex_abstract.
  intros. apply /RleP. unfold e_i.
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.  unfold dot_prodR.
      apply sum_abs_pair_rel. apply Rge_le. apply Rge_minus. apply Rle_ge.
      apply pow_R1_Rle. rewrite -!RmultE. simpl; nra.
    * repeat apply Rmult_le_pos.
      ++ apply pos_INR.
      ++ nra.
      ++ simpl; nra.
      ++ apply pow_le . rewrite -!RmultE. simpl;nra.
  - rewrite -!RmultE. apply Rmult_le_pos.
    * apply Rmult_le_pos.
      ++ simpl;nra.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. simpl; nra.
    * simpl;nra.
Qed.


Lemma tau_bounds_tau_m {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1) :
  x != 0 ->
  (tau_m  k x x_hat inv_A1 A1 A2 b <= tau k x x_hat inv_A1 A1 A2 b)%Re.
Proof.
intros.
unfold tau_m, tau.
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
+ repeat apply Rplus_le_le_0_compat. 
  - apply Rmult_le_pos.
    * apply /RleP. apply matrix_norm_pd.
    * rewrite -RmultE. simpl;nra.
  - apply Rmult_le_pos.
    * apply /RleP. apply mat_err_bnd_pd.
    * rewrite -RmultE. simpl;nra.
  - apply /RleP. apply mat_err_bnd_pd.
+ unfold theta_x. apply pow_invert_2. 
  - by apply vec_norm_definite.
  - apply Rle_trans with
    ([seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
        vec_inf_norm x)%Re
      | i <- enum 'I_k.+1]`_k).
    * rewrite seq_equiv. rewrite nth_mkseq; last by [].
      rewrite inordK; last by []. nra.
    * apply /RleP. 
      apply (@bigmaxr_ler _ 0%Re 
              [seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
                  vec_inf_norm x)%Re| i <- enum 'I_k.+1] k).
      by rewrite size_map size_enum_ord.
Qed.


Lemma theta_x_ge_0  {n:nat} (k:nat)
 (x_hat : nat ->'cV[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1):
  x != 0 ->
 (0 <= theta_x k x_hat x)%Re.
Proof.
intros.
unfold theta_x.
apply Rle_trans with (vec_inf_norm (FT2R_mat (x_hat k)) / vec_inf_norm x)%Re.
+ apply Rmult_le_pos.
  - apply /RleP. apply vec_norm_pd.
  - apply Rlt_le, Rinv_0_lt_compat. by apply vec_norm_definite.
+ apply Rle_trans with
    ([seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
        vec_inf_norm x)%Re
      | i <- enum 'I_k.+1]`_k).
    * rewrite seq_equiv. rewrite nth_mkseq; last by [].
      rewrite inordK; last by []. nra.
    * apply /RleP. 
      apply (@bigmaxr_ler _ 0%Re 
              [seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
                  vec_inf_norm x)%Re| i <- enum 'I_k.+1] k).
      by rewrite size_map size_enum_ord.
Qed. 

Lemma mat_vec_mult_err_bnd_pd {n:nat} 
 (A: 'M[ftype Tsingle]_n.+1) (v: 'cV[ftype Tsingle]_n.+1):
 (0 <= mat_vec_mult_err_bnd A v)%Re.
Proof.
unfold mat_vec_mult_err_bnd.
apply /RleP.
apply bigmax_le_0.
+ apply /RleP. apply Rle_refl.
+ intros. rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
  unfold e_i. apply /RleP.
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.  unfold dot_prodR.
      apply sum_abs_pair_rel. apply Rge_le. apply Rge_minus. apply Rle_ge.
      apply pow_R1_Rle. rewrite -!RmultE. simpl; nra.
    * repeat apply Rmult_le_pos.
      ++ apply pos_INR.
      ++ nra.
      ++ simpl; nra.
      ++ apply pow_le . rewrite -!RmultE. simpl;nra.
  - rewrite -!RmultE. apply Rmult_le_pos.
    * apply Rmult_le_pos.
      ++ simpl;nra.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. simpl; nra.
    * simpl;nra.
Qed. 

Lemma X_m_real_iter {n:nat} (k: nat) (x0 b: 'cV[R]_n.+1) 
  (A2 inv_A1: 'M[ftype Tsingle]_n.+1) :
   let xkr := X_m_real_generic k x0 b (FT2R_mat inv_A1) (FT2R_mat A2) in
    X_m_real_generic k.+1 x0 b (FT2R_mat inv_A1) (FT2R_mat A2) = 
    X_m_real_generic 1 xkr b (FT2R_mat inv_A1) (FT2R_mat A2).
Proof. simpl; auto. Qed.


Lemma add_vec_distr {n:nat}:
  forall a b c: 'cV[R]_n,
  a - b + b - c = (a-b) + (b-c).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. by rewrite -addrA.
Qed.


Lemma add_vec_distr_1 {n:nat}:
  forall a b c: 'cV[R]_n,
  (a+b) - (b+c) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma add_vec_distr_2 {n:nat}:
  forall a b c: 'cV[R]_n,
  (a-b) + (b-c) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.


Lemma add_vec_distr_3 {n:nat}:
  forall a b c d: 'cV[R]_n,
  (a+b) - (c+d) = (a-c) + (b-d).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.



Lemma bigmax_rel_iota k (F : nat -> R) :
  (bigmaxr 0%Re [seq F i | i <- iota 0 k.+1] <=
   bigmaxr 0%Re [seq F i | i <- iota 0 k.+2]).
Proof.
apply/bigmaxr_lerP.
  by rewrite size_map size_iota.
move=> i; rewrite size_map size_iota => ilt.
have -> : seq.nth 0%Re [seq F i | i <- iota 0 k.+1] i =
          seq.nth 0%Re [seq F i | i <- iota 0 k.+2] i.
  by rewrite !(nth_map 0%nat) // ?nth_iota // ?size_iota // (leq_trans ilt).
apply: bigmaxr_ler.
by rewrite size_map size_iota (leq_trans ilt).
Qed.




Lemma bigmax_rel {k:nat} (f : nat -> R):
(bigmaxr 0%Re
  [seq (f (nat_of_ord i)) | i <- enum 'I_k.+1] <=
 bigmaxr 0%Re
   [seq (f (nat_of_ord i)) | i <- enum 'I_k.+2])%Re.
Proof.
apply /RleP.
by rewrite map_comp [in X in (_ <= X)]map_comp !val_enum_ord bigmax_rel_iota.
Qed.


Lemma theta_eq {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1):
  (theta_x k x_hat x <= theta_x k.+1 x_hat x)%Re.
Proof.
unfold theta_x.
apply (@bigmax_rel k (fun m:nat => (vec_inf_norm (FT2R_mat (x_hat m)) /
        vec_inf_norm x)%Re)).
Qed.


Lemma tau_rel {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):
  (tau k x x_hat inv_A1 A1 A2 b <= tau k.+1 x x_hat inv_A1 A1 A2 b)%Re.
Proof.
unfold tau. 
remember (/ 2 *
   bpow Zaux.radix2 (- fprec Tsingle + 1)) as d.
remember (/ 2 *
  bpow Zaux.radix2
    (3 - femax Tsingle - fprec Tsingle)) as e.
apply Rplus_le_compat.
+ apply Rmult_le_compat_l.
  - repeat apply Rplus_le_le_0_compat. 
    * apply Rmult_le_pos.
      ++ apply /RleP. apply matrix_norm_pd.
      ++ rewrite Heqd. rewrite -RmultE. simpl;nra.
    * apply Rmult_le_pos.
      ++ apply /RleP. apply mat_err_bnd_pd.
      ++ rewrite Heqd. rewrite -RmultE. simpl;nra.
    * apply /RleP. apply mat_err_bnd_pd.
  - apply Rmult_le_compat_r.
    ++ apply /RleP. apply vec_norm_pd.
    ++ apply theta_eq;nra.
+ repeat apply Rplus_le_compat.
  apply Rmult_le_compat_r; try nra.
  - rewrite Heqd. rewrite -RmultE. simpl;nra.
  - unfold E_3. rewrite -!RmultE.
    repeat apply Rplus_le_compat_r. 
    repeat apply Rmult_le_compat_r.
    * apply Rge_le. apply Rge_minus. apply Rle_ge.
      apply pow_R1_Rle. simpl;nra.
    * apply /RleP. apply bigmax_le_0.
      ++ apply /RleP. apply Rle_refl.
      ++ intros. rewrite seq_equiv. 
         rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
         unfold e_i_real.  unfold dot_prodR. 
         apply sum_Rabs_pair_rel. 
    * apply theta_eq. 
  - nra.
  - nra.
  - unfold E_3. rewrite -!RmultE.
    repeat apply Rplus_le_compat_r. 
    repeat apply Rmult_le_compat_r.
    * apply Rge_le. apply Rge_minus. apply Rle_ge.
      apply pow_R1_Rle. simpl;nra.
    * apply /RleP. apply bigmax_le_0.
      ++ apply /RleP. apply Rle_refl.
      ++ intros. rewrite seq_equiv. 
         rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
         unfold e_i_real.  unfold dot_prodR. 
         apply sum_Rabs_pair_rel. 
    * apply theta_eq.
  - nra.
  - nra.
  - nra.
  - nra.
Qed.

Lemma E_3_err_bnd_pd {n:nat} (k:nat) 
  (A : 'M[ftype Tsingle]_n.+1) (b : 'cV[ftype Tsingle]_n.+1) 
  (x_hat : nat -> 'cV[ftype Tsingle]_n.+1) (x : 'cV[R]_n.+1):
   x != 0 ->
  (0 <= E_3 k A b x_hat x)%Re.
Proof.
intros.
unfold E_3. 
repeat apply Rplus_le_le_0_compat.
+ repeat apply Rmult_le_pos.
  - by apply theta_x_ge_0.
  - apply /RleP. apply bigmax_le_0.
    * apply /RleP. apply Rle_refl.
    * intros. rewrite seq_equiv. rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H0.
      unfold e_i_real. unfold dot_prodR.
      apply sum_Rabs_pair_rel.
  - apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. rewrite -RmultE.  simpl; nra.
+ repeat apply Rmult_le_pos.
      ++ apply pos_INR.
      ++ nra.
      ++ simpl; nra.
      ++ apply pow_le . rewrite -!RmultE. simpl;nra.
+ rewrite -!RmultE. apply Rmult_le_pos.
    * apply Rmult_le_pos.
      ++ simpl;nra.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. simpl; nra.
    * simpl;nra.
Qed.


Lemma add_vec_float_le {n:nat}:
  forall (v1 v2: 'cV[ftype Tsingle]_n.+1),
  (1 < n.+1)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (forall i: nat, (i < n.+1)%nat -> 
                  boundsmap_denote (@bmap Tsingle 2%nat)
                        (vmap (v1 (inord i) 0) (v2 (inord i) 0))) ->
  (vec_inf_norm (FT2R_mat (v1 +f v2) - (FT2R_mat v1 + FT2R_mat v2)) <=
  (vec_inf_norm (FT2R_mat v1) + vec_inf_norm (FT2R_mat v2)) * d + e)%Re.
Proof.
intros.
unfold vec_inf_norm. apply bigmax_le.
+ by rewrite size_map size_enum_ord.
+ intros.
  apply Rle_trans with 
  (([seq Rabs (FT2R_mat v1 i0 0)
       | i0 <- enum 'I_n.+1]`_i + 
    [seq Rabs (FT2R_mat v2 i0 0)
       | i0 <- enum 'I_n.+1]`_i) * d + e)%Re.
  - rewrite !seq_equiv. 
    rewrite !nth_mkseq; last by rewrite size_map size_enum_ord in H1.
    * rewrite !mxE. rewrite -!RplusE -!RoppE. 
      apply Rle_trans with
      (Rabs ((FT2R (v1 (inord i) ord0)) + (FT2R (v2 (inord i) ord0))) * d + e)%Re.
      unfold d,e. rewrite -!RmultE. apply (prove_rndoff _ _ 2%nat).
      ++ lia.
      ++ apply H0. by rewrite size_map size_enum_ord in H1.
      ++ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
         -- unfold d. rewrite -RmultE. simpl;nra.
         -- apply Rabs_triang.
    * by rewrite size_map size_enum_ord in H1.
    * by rewrite size_map size_enum_ord in H1.
  - apply Rplus_le_compat_r. apply Rmult_le_compat_r.
    * unfold d. rewrite -RmultE. simpl;nra.
    * apply Rplus_le_compat.
      ++ apply /RleP. 
         apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v1 i0 0)
                       | i0 <- enum 'I_n.+1] i).
         rewrite size_map size_enum_ord.
         by rewrite size_map size_enum_ord in H1.
      ++ apply /RleP. 
         apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v2 i0 0)
                      | i0 <- enum 'I_n.+1] i).
         rewrite size_map size_enum_ord.
         by rewrite size_map size_enum_ord in H1.
Qed.


Lemma div_switch: forall (x y:R), 
  (0 < x)%Re /\ (0 < y)%Re ->
  (y <= (x + 1) * / x)%Re ->
  (x / (x + 1) <= / y)%Re.
Proof.
intros.
replace (/y)%Re with (1 * /y)%Re by nra.
assert ((x / (x + 1))%Re= ((x / (x + 1) *y) * / y)%Re).
{ assert ( ((x / (x + 1) *y) * / y)%Re = ((x / (x + 1)) * (y * /y))%Re).
  { nra. } rewrite H1. 
  assert ((y * /y)%Re = 1%Re). { rewrite Rinv_r;nra. } rewrite H2;nra.
} rewrite H1. apply Rmult_le_compat_r.
+ apply Rlt_le, Rinv_0_lt_compat. nra.
+ replace (x / (x + 1) * y)%Re with ((x  *y) * / (x + 1))%Re by nra.
  assert (1%Re = ((x+1) * / (x+1))%Re).
  { rewrite Rinv_r;nra.  } 
  assert ((x * y * / (x + 1) <= ((x+1) * / (x+1)))%Re -> (x * y * / (x + 1) <= 1)%Re).
  { by rewrite -H2. } apply H3. apply Rmult_le_compat_r.
  -  apply Rlt_le, Rinv_0_lt_compat. nra.
  - rewrite Rmult_comm.
    replace (x+1)%Re with ((x+1) * 1)%Re by nra.
    assert (1%Re = (x * / x)%Re). { rewrite Rinv_r;nra. } 
    assert (((x + 1) * 1)%Re  = (((x+1) * /x) * x)%Re). { nra. } rewrite H5.
    apply Rmult_le_compat_r; nra.
Qed.
    



(** If each element of v1 and v2 are less than
    F' / 2 * n * (1+d)^n  - 1, then it should be possible to bound
    them using the current boundsmap bounds
***)
Lemma dot_add_vec_float_le {n:nat}:
  forall (A1 A2: 'M[ftype Tsingle]_n.+1) (v1 v2: 'cV[ftype Tsingle]_n.+1),
  (1 < n.+1 /\ n.+1< (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in
  (forall i n :nat, (i < n.+1)%nat -> 
    (forall (a b : ftype Tsingle) (A: 'M[ftype Tsingle]_n.+1)
            (v: 'cV[ftype Tsingle]_n.+1),
      In (a, b)
        (combine (vec_to_list_float n.+1 (\row_j A (inord i) j)^T)
           (vec_to_list_float n.+1 v)) ->
      is_finite (fprec Tsingle) (femax Tsingle) a = true /\
      is_finite (fprec Tsingle) (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re /\
      (Rabs (FT2R b) <=
       sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re)) ->
   let S1 := A1 *f v1 in 
   let S2 := A2 *f v2 in
   (vec_inf_norm (FT2R_mat (S1 +f S2) - (FT2R_mat S1 + FT2R_mat S2)) <=
   (vec_inf_norm (FT2R_mat S1) + vec_inf_norm (FT2R_mat S2)) * d + e)%Re.
Proof.
intros.
apply add_vec_float_le.
+ lia.
+ intros.
  specialize (H0 i n). specialize (H0 H1).
  apply boundsmap_denote_i.
    2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
       repeat apply list_forall_cons; try apply list_forall_nil;
         (eexists; split; [|split;[|split]]; try reflexivity; auto;
           try unfold List.nth; try nra; auto). 
  - rewrite !mxE. apply forward_error_dot_aux.
    * rewrite  combine_length. rewrite !length_veclist. lia.
    * rewrite  combine_length. rewrite !length_veclist. lia.
    * intros. specialize (H0 a b).
      specialize (H0 A2 v2).
      remember (combine (vec_to_list_float n.+1 (\row_j A2 (inord i) j)^T)
                        (vec_to_list_float n.+1 (\col_j v2 j 0))) as L.
      assert (length L = n.+1).
      { rewrite HeqL combine_length. rewrite !length_veclist. lia. }
      rewrite H3. rewrite -/nr. 
      unfold d,e in H0. rewrite -!RmultE in H0.
      assert (In (a, b)
                 (combine (vec_to_list_float n.+1 (\row_j A2 (inord i) j)^T)
                    (vec_to_list_float n.+1 v2))).
      {  assert (v2 = (\col_j v2 j 0)).
         { apply matrixP. unfold eqrel. intros.
           assert (y = 0). { by apply ord1. } by rewrite H4 !mxE.
         } rewrite H4. by rewrite HeqL in H2.
      } specialize (H0 H4). repeat split; try apply H0.
      ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
       ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
    - apply generalize.Rabs_ineq. rewrite !mxE.
      pose proof forward_error_dot_aux.
      remember (combine (vec_to_list_float n.+1 (\row_j A2 (inord i) j)^T)
                      (vec_to_list_float n.+1 (\col_j v2 j 0))) as L.
      specialize (H2 L).
      assert (length L = n.+1).
      { rewrite HeqL combine_length. rewrite !length_veclist. lia. }
      rewrite H3 in H2.
      assert ((1 < n.+1)%coq_nat). { destruct H. apply H. }
      assert ((n.+1 < (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat).
      { destruct H. apply H5. } specialize (H2 H4 H5).
      assert  (forall a b : ftype Tsingle,
                In (a, b) L ->
                is_finite (fprec Tsingle) (femax Tsingle) a = true /\
                is_finite (fprec Tsingle) (femax Tsingle) b = true /\
                (Rabs (FT2R a) <=
                 sqrt
                   (F' / ((INR n.+1 + 1) *
                     (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                     ^ (n.+1 + 1)%coq_nat) -
                    / 2 * bpow Zaux.radix2  (3 - femax Tsingle -
                       fprec Tsingle)))%Re /\
                  (Rabs (FT2R b) <=
                   sqrt
                     (F' / ((INR n.+1 + 1) *
                       (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                       ^ (n.+1 + 1)%coq_nat) -
                      / 2 * bpow Zaux.radix2 (3 - femax Tsingle -
                         fprec Tsingle)))%Re).
      { intros. specialize (H0 a b A2 v2).
        assert (In (a, b)
                 (combine  (vec_to_list_float n.+1 (\row_j A2 (inord i) j)^T)
                    (vec_to_list_float n.+1 v2))).
        { rewrite HeqL in H6.
          assert (v2 = (\col_j v2 j 0)).
         { apply matrixP. unfold eqrel. intros.
           assert (y = 0). { by apply ord1. } by rewrite H7 !mxE.
         } by rewrite H7. 
        } specialize (H0 H7). repeat split; try apply H0.
      ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
       ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
     } specialize (H2 H6). 
     destruct H2 as [Hf2 H2].
     apply Rabs_triang_inv_impl, side_switch in H2.
     eapply Rle_trans.
     *** rewrite HeqL in H2. apply H2.
     *** rewrite -HeqL.
         apply Rle_trans with 
            (dot_prodR (Flist_to_Rlist_pair_abs L) +
                (dot_prodR (Flist_to_Rlist_pair_abs L) *
                    ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                 ^ n.+1 - 1) +
                                INR n.+1 *
                                (/ 2 *
                                 bpow Zaux.radix2
                                   (3 - femax Tsingle - fprec Tsingle)) *
                                (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                ^ (n.+1 - 1)%coq_nat +
                                / 2 *
                                bpow Zaux.radix2
                                  (3 - femax Tsingle - fprec Tsingle) *
                                ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                 ^ (n.+1 - 1)%coq_nat - 1) /
                                (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))))%Re.
          ++++ apply Rplus_le_compat_r, sum_abs_pair_le.
          ++++ assert ((dot_prodR (Flist_to_Rlist_pair_abs L) +
                                         (dot_prodR (Flist_to_Rlist_pair_abs L) *
                                          ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ n.+1 - 1) +
                                          INR n.+1 *
                                          (/ 2 *
                                           bpow Zaux.radix2
                                             (3 - femax Tsingle - fprec Tsingle)) *
                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                          ^ (n.+1 - 1)%coq_nat +
                                          / 2 *
                                          bpow Zaux.radix2
                                            (3 - femax Tsingle - fprec Tsingle) *
                                          ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ (n.+1 - 1)%coq_nat - 1) /
                                          (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))))%Re =
                                          ( dot_prodR (Flist_to_Rlist_pair_abs L) *
                                           ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ n.+1) +  INR n.+1 *
                                          (/ 2 *
                                           bpow Zaux.radix2
                                             (3 - femax Tsingle - fprec Tsingle)) *
                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                          ^ (n.+1 - 1)%coq_nat +
                                          / 2 *
                                          bpow Zaux.radix2
                                            (3 - femax Tsingle - fprec Tsingle) *
                                          ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ (n.+1 - 1)%coq_nat - 1) /
                                          (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re).
                  { nra. } rewrite H7. clear H7. rewrite /dot_prodR.
                  apply Rle_trans with 
                  (((sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))^2 * INR (length L)) *
                                  (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ^ n.+1 +
                                INR n.+1 *
                                 (/ 2 *
                                  bpow Zaux.radix2
                                    (3 - femax Tsingle - fprec Tsingle)) *
                                 (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                 ^ (n.+1 - 1)%coq_nat +
                                 / 2 *
                                 bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) *
                                 ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                  ^ (n.+1 - 1)%coq_nat - 1) /
                                 (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re.
                   ---- repeat apply Rplus_le_compat_r.  
                        apply Rmult_le_compat_r.
                        **** apply Rlt_le, x_pow_gt_0. simpl; nra.
                        **** apply (list_sum_pair L (sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)) - e))).
                             apply sqrt_pos. intros.
                             specialize (H0 (fst a) (snd a) A2 v2).
                              assert (In (a.1, a.2)
                                       (combine  (vec_to_list_float n.+1 (\row_j A2 (inord i) j)^T)
                                          (vec_to_list_float n.+1 v2))).
                              { rewrite HeqL in H7.
                                assert (v2 = (\col_j v2 j 0)).
                               { apply matrixP. unfold eqrel. intros.
                                 assert (y = 0). { by apply ord1. } by rewrite H8 !mxE.
                               } rewrite H8. destruct a; simpl;auto.
                              } specialize (H0 H8). repeat split; try apply H0. 
                  ---- assert ((sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e) ^ 2)%Re = 
                                              ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e)%Re).
                       { assert (forall x:R, (x^2)%Re = (x * x)%Re). { intros. nra. } rewrite H7.
                        apply sqrt_sqrt.
                        apply Rge_le. apply Rge_minus. apply Rle_ge.
                        apply pow_invert.
                        * apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra. 
                           apply x_pow_gt_0. unfold d; rewrite -RmultE; simpl; nra.
                           * apply Rle_trans with 
                                            (e * ((INR n.+1 + 1) * 3))%Re.
                             +++ unfold nr. repeat apply Rmult_le_compat_l.
                                  --- unfold e; rewrite -RmultE; simpl; nra.
                                  --- apply Rplus_le_le_0_compat. apply pos_INR. nra.
                                  --- apply Rlt_le. 
                                      pose proof  (delta_bound (n.+1 +1)%coq_nat).
                                      assert ( ((n.+1 + 1)%coq_nat < Z.to_nat (Z.pow_pos 2 23))%coq_nat).
                                      { destruct H. lia. } specialize (H8 H9).
                                      unfold d. rewrite -RmultE.
                                      nra.
                                      +++ replace (e * ((INR n.+1+1) * 3))%Re with ((INR n.+1 + 1) * (3 * e))%Re by nra.
                                          apply pow_invert_1.
                                          --- unfold e;rewrite -RmultE; simpl;nra.
                                          --- apply Rle_trans with 
                                                    (IZR (Z.pow_pos 2 23) + 1)%Re.
                                              *** apply Rlt_le. rewrite INR_IZR_INZ. apply Rplus_lt_compat_r. apply IZR_lt. lia.
                                              *** unfold e. rewrite -RmultE. simpl. unfold F', F_max; simpl; nra.
                        } rewrite H7 H3. 
                         assert ((((F' /2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e) *
                                               INR n.+1 *
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ n.+1 +
                                               INR n.+1 *
                                               (/ 2 *
                                                bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ (n.+1 - 1)%coq_nat +
                                               / 2 *
                                               bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) *
                                               ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                ^ (n.+1 - 1)%coq_nat - 1) /
                                               (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re = 
                                              (((((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat)) * INR n.+1 * 
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ^ n.+1) -
                                               (INR n.+1 * e * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ n.+1 - INR n.+1 *
                                               (/ 2 *
                                                bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ (n.+1 - 1)%coq_nat)) + / 2 *
                                               bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) *
                                               ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                ^ (n.+1 - 1)%coq_nat - 1) /
                                               (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re).
                         { nra. } rewrite H8. clear H8. apply Rplus_le_compat.
                         **** assert ((F' * (INR 2 - 1) / INR 2)%Re = ((F' * (INR 2 - 1) / INR 2) + 0)%Re).
                              { simpl;nra. } rewrite H8. apply Rplus_le_compat.
                              +++++ unfold d. rewrite -RmultE.
                                    remember (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))%Re as de.
                                    unfold nr. 
                                    assert (((F'/2) / ((INR n.+1 + 1) * de ^ (n.+1 + 1)%coq_nat) *
                                                            INR n.+1 * de ^ n.+1)%Re = 
                                                          (((F'/2) * (de ^ n.+1 / de ^ (n.+1 + 1)%coq_nat)) * 
                                                           (INR n.+1 / (INR n.+1 + 1)))%Re).
                                    { assert (((F'/2) / ((INR n.+1 + 1) * de ^ (n.+1 + 1)%coq_nat) *
                                                            INR n.+1 * de ^ n.+1)%Re = 
                                                            ((F'/2) * / ((INR n.+1 + 1) * de ^ (n.+1 + 1)%coq_nat) * 
                                                              INR n.+1 * de ^ n.+1)%Re).
                                      { nra. } rewrite H9. clear H9.
                                      assert ((/ ((INR n.+1 + 1) * de ^ (n.+1 + 1)%coq_nat))%Re  = 
                                                           (/ (INR n.+1 + 1) * / (de ^ (n.+1 + 1)%coq_nat))%Re).
                                      { rewrite Rinv_mult_distr. nra. 
                                        assert ( (0 < INR n.+1 + 1)%Re ->  (INR n.+1 + 1)%Re <> 0%Re).
                                        { nra. } apply H9. apply Rplus_lt_0_compat. apply lt_0_INR. lia.
                                        nra. 
                                        assert ((0 < de ^ (n.+1 + 1)%coq_nat)%Re ->  (de ^ (n.+1 + 1)%coq_nat)%Re <> 0%Re).
                                        { nra. } apply H9. apply pow_lt. rewrite Heqde;simpl;nra.
                                      } rewrite H9. nra.
                                    } rewrite H9. 
                                    assert ((F' * (INR 2 - 1) / INR 2)%Re = ((F'/2) * 1)%Re).
                                    { simpl;nra. } rewrite H10. apply Rmult_le_compat.
                                    ----- apply Rmult_le_pos. unfold F',F_max;simpl;nra. 
                                          apply Rmult_le_pos. apply pow_le. rewrite Heqde;simpl;nra.
                                          apply Rlt_le, Rinv_0_lt_compat. apply pow_lt.
                                          rewrite Heqde;simpl;nra.
                                    ----- apply Rmult_le_pos. apply pos_INR. apply Rlt_le.
                                          apply Rinv_0_lt_compat. apply Rplus_lt_0_compat.
                                          apply lt_0_INR. lia. nra.
                                    ----- assert (((F'/2) * (de ^ n.+1 / de ^ (n.+1 + 1)%coq_nat) <= (F'/2) * 1)%Re ->
                                                               ((F'/2) * (de ^ n.+1 / de ^ (n.+1 + 1)%coq_nat) <= (F'/2))%Re).
                                          { nra. } apply H11. apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                                          assert (1%Re = (de ^ (n.+1 + 1)%coq_nat */ de ^ (n.+1 + 1)%coq_nat)%Re).
                                          { rewrite Rinv_r. nra.
                                            assert ((0 < de ^ (n.+1 + 1)%coq_nat)%Re -> (de ^ (n.+1 + 1)%coq_nat)%Re <> 0%Re).
                                            { nra. } apply H12. apply pow_lt. rewrite Heqde;simpl;nra.
                                          } rewrite H12. apply Rmult_le_compat_r.
                                          apply Rlt_le, Rinv_0_lt_compat,pow_lt. rewrite Heqde;simpl;nra.
                                          apply Rle_pow. rewrite Heqde;simpl;nra. lia.
                                    ----- assert (1%Re = ((INR n.+1 +1) */ (INR n.+1 + 1))%Re).
                                          { rewrite Rinv_r. nra.
                                            assert ((0 < (INR n.+1 + 1)%Re)%Re ->(INR n.+1 + 1)%Re <> 0%Re).
                                            { nra. } apply H11. apply Rplus_lt_0_compat. apply lt_0_INR;lia. nra.
                                          }
                                          assert ((INR n.+1 / (INR n.+1 + 1) <= (INR n.+1 + 1) / (INR n.+1 + 1))%Re ->
                                                  (INR n.+1 / (INR n.+1 + 1) <= 1)%Re). { nra. } apply H12.
                                          apply Rmult_le_compat_r. apply Rlt_le, Rinv_0_lt_compat.
                                          apply Rplus_lt_0_compat. apply lt_0_INR;lia. nra. nra.
                            +++++ unfold e. rewrite -RmultE.
                                  assert ((INR n.+1 *
                                                          (/ 2 *
                                                           bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                          ^ n.+1 -
                                                          INR n.+1 *
                                                          (/ 2 *
                                                           bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                          ^ (n.+1 - 1)%coq_nat)%Re = 
                                                          ((INR n.+1 *  (/ 2 *
                                                           bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                          ^ (n.+1 - 1)%coq_nat * (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re)).
                                   { assert (n.+1 = S ((n.+1 - 1)%coq_nat)). { lia. } 
                                     assert ((INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ n.+1 -
                                                             INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ (n.+1 - 1)%coq_nat)%Re = 
                                                           (INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ S ((n.+1 - 1)%coq_nat) -
                                                             INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ (n.+1 - 1)%coq_nat)%Re).
                                      { by rewrite -H9. } rewrite H10. clear H10.
                                      assert ((INR n.+1 *
                                                           (/ 2 *
                                                            bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                           (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                           ^ (n.+1 - 1)%coq_nat.+1)%Re = 
                                                          (INR n.+1 *
                                                           (/ 2 *
                                                            bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                           (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                           ^ (n.+1 - 1)%coq_nat * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re).
                                                 { simpl. nra. } rewrite H10. clear H10. nra. 
                                } rewrite H9. clear H9. apply Rge_le. apply Ropp_0_le_ge_contravar .
                                repeat apply Rmult_le_pos.
                                ----- apply pos_INR.
                                ----- nra.
                                ----- simpl;nra.
                                ----- apply pow_le . simpl; nra.
                                ----- nra.
                                ----- simpl;nra.
                        **** remember (/ 2 *
                                                        bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle))%Re as ee.
                                           remember  ( / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))%Re as de.
                                           assert ((ee * ((1 + de) ^ (n.+1 - 1)%coq_nat - 1) / de)%Re = 
                                                    (((1 + de) ^ (n.+1 - 1)%coq_nat - 1) * (ee / de))%Re).
                             { nra. } rewrite H8.
                             assert ( (2 * ee / de)%Re = (2 * (ee / de))%Re).
                             { nra. } rewrite H9. apply Rmult_le_compat_r.
                             rewrite Heqde Heqee;simpl;nra.
                             apply Rlt_le. rewrite Heqde. apply (delta_bound (n.+1 - 1)%coq_nat).
                             lia.
  - rewrite !mxE. apply forward_error_dot_aux.
    * rewrite  combine_length. rewrite !length_veclist. lia.
    * rewrite  combine_length. rewrite !length_veclist. lia.
    * intros. specialize (H0 a b).
      specialize (H0 A1 v1).
      remember (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
                        (vec_to_list_float n.+1 (\col_j v1 j 0))) as L.
      assert (length L = n.+1).
      { rewrite HeqL combine_length. rewrite !length_veclist. lia. }
      rewrite H3. rewrite -/nr. 
      unfold d,e in H0. rewrite -!RmultE in H0.
      assert (In (a, b)
                 (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
                    (vec_to_list_float n.+1 v1))).
      {  assert (v1 = (\col_j v1 j 0)).
         { apply matrixP. unfold eqrel. intros.
           assert (y = 0). { by apply ord1. } by rewrite H4 !mxE.
         } rewrite H4. by rewrite HeqL in H2.
      } specialize (H0 H4). repeat split; try apply H0.
      ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
       ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
   - apply generalize.Rabs_ineq. rewrite !mxE.
     pose proof forward_error_dot_aux.
      remember (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
                      (vec_to_list_float n.+1 (\col_j v1 j 0))) as L.
      specialize (H2 L).
      assert (length L = n.+1).
      { rewrite HeqL combine_length. rewrite !length_veclist. lia. }
      rewrite H3 in H2.
      assert ((1 < n.+1)%coq_nat). { destruct H. apply H. }
      assert ((n.+1 < (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat).
      { destruct H. apply H5. } specialize (H2 H4 H5).
      assert  (forall a b : ftype Tsingle,
                In (a, b) L ->
                is_finite (fprec Tsingle) (femax Tsingle) a = true /\
                is_finite (fprec Tsingle) (femax Tsingle) b = true /\
                (Rabs (FT2R a) <=
                 sqrt
                   (F' / ((INR n.+1 + 1) *
                     (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                     ^ (n.+1 + 1)%coq_nat) -
                    / 2 * bpow Zaux.radix2  (3 - femax Tsingle -
                       fprec Tsingle)))%Re /\
                  (Rabs (FT2R b) <=
                   sqrt
                     (F' / ((INR n.+1 + 1) *
                       (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                       ^ (n.+1 + 1)%coq_nat) -
                      / 2 * bpow Zaux.radix2 (3 - femax Tsingle -
                         fprec Tsingle)))%Re).
      { intros. specialize (H0 a b A1 v1).
        assert (In (a, b)
                 (combine  (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
                    (vec_to_list_float n.+1 v1))).
        { rewrite HeqL in H6.
          assert (v1 = (\col_j v1 j 0)).
         { apply matrixP. unfold eqrel. intros.
           assert (y = 0). { by apply ord1. } by rewrite H7 !mxE.
         } by rewrite H7. 
        } specialize (H0 H7). repeat split; try apply H0.
      ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
       ++ apply Rle_trans with 
         (sqrt ((F' / 2) /
         ( (nr + 1) * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
          ^ (n.+1 + 1)%coq_nat) -
         / 2 *  bpow Zaux.radix2 (3 - femax Tsingle -  fprec Tsingle)))%Re.
         -- apply H0.
         -- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
            apply Rmult_le_compat_r.
            ** apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat.
               +++ apply Rplus_lt_0_compat. unfold nr. apply lt_0_INR;lia. nra.
               +++ apply pow_lt. simpl;nra.
            ** unfold F',F_max;simpl;nra.
     } specialize (H2 H6). 
     destruct H2 as [Hf2 H2].
     apply Rabs_triang_inv_impl, side_switch in H2.
     eapply Rle_trans.
     *** rewrite HeqL in H2. apply H2.
     *** rewrite -HeqL.
         apply Rle_trans with 
            (dot_prodR (Flist_to_Rlist_pair_abs L) +
                (dot_prodR (Flist_to_Rlist_pair_abs L) *
                    ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                 ^ n.+1 - 1) +
                                INR n.+1 *
                                (/ 2 *
                                 bpow Zaux.radix2
                                   (3 - femax Tsingle - fprec Tsingle)) *
                                (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                ^ (n.+1 - 1)%coq_nat +
                                / 2 *
                                bpow Zaux.radix2
                                  (3 - femax Tsingle - fprec Tsingle) *
                                ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                 ^ (n.+1 - 1)%coq_nat - 1) /
                                (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))))%Re.
          ++++ apply Rplus_le_compat_r, sum_abs_pair_le.
          ++++ assert ((dot_prodR (Flist_to_Rlist_pair_abs L) +
                                         (dot_prodR (Flist_to_Rlist_pair_abs L) *
                                          ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ n.+1 - 1) +
                                          INR n.+1 *
                                          (/ 2 *
                                           bpow Zaux.radix2
                                             (3 - femax Tsingle - fprec Tsingle)) *
                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                          ^ (n.+1 - 1)%coq_nat +
                                          / 2 *
                                          bpow Zaux.radix2
                                            (3 - femax Tsingle - fprec Tsingle) *
                                          ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ (n.+1 - 1)%coq_nat - 1) /
                                          (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))))%Re =
                                          ( dot_prodR (Flist_to_Rlist_pair_abs L) *
                                           ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ n.+1) +  INR n.+1 *
                                          (/ 2 *
                                           bpow Zaux.radix2
                                             (3 - femax Tsingle - fprec Tsingle)) *
                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                          ^ (n.+1 - 1)%coq_nat +
                                          / 2 *
                                          bpow Zaux.radix2
                                            (3 - femax Tsingle - fprec Tsingle) *
                                          ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                           ^ (n.+1 - 1)%coq_nat - 1) /
                                          (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re).
                  { nra. } rewrite H7. clear H7. rewrite /dot_prodR.
                  apply Rle_trans with 
                  (((sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))^2 * INR (length L)) *
                                  (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ^ n.+1 +
                                INR n.+1 *
                                 (/ 2 *
                                  bpow Zaux.radix2
                                    (3 - femax Tsingle - fprec Tsingle)) *
                                 (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                 ^ (n.+1 - 1)%coq_nat +
                                 / 2 *
                                 bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) *
                                 ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                  ^ (n.+1 - 1)%coq_nat - 1) /
                                 (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re.
                   ---- repeat apply Rplus_le_compat_r.  
                        apply Rmult_le_compat_r.
                        **** apply Rlt_le, x_pow_gt_0. simpl; nra.
                        **** apply (list_sum_pair L (sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)) - e))).
                             apply sqrt_pos. intros.
                             specialize (H0 (fst a) (snd a) A1 v1).
                              assert (In (a.1, a.2)
                                       (combine  (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
                                          (vec_to_list_float n.+1 v1))).
                              { rewrite HeqL in H7.
                                assert (v1 = (\col_j v1 j 0)).
                               { apply matrixP. unfold eqrel. intros.
                                 assert (y = 0). { by apply ord1. } by rewrite H8 !mxE.
                               } rewrite H8. destruct a; simpl;auto.
                              } specialize (H0 H8). repeat split; try apply H0. 
                  ---- assert ((sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e) ^ 2)%Re = 
                                              ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e)%Re).
                       { assert (forall x:R, (x^2)%Re = (x * x)%Re). { intros. nra. } rewrite H7.
                        apply sqrt_sqrt.
                        apply Rge_le. apply Rge_minus. apply Rle_ge.
                        apply pow_invert.
                        * apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra. 
                           apply x_pow_gt_0. unfold d; rewrite -RmultE; simpl; nra.
                           * apply Rle_trans with 
                                            (e * ((INR n.+1 + 1) * 3))%Re.
                             +++ unfold nr. repeat apply Rmult_le_compat_l.
                                  --- unfold e; rewrite -RmultE; simpl; nra.
                                  --- apply Rplus_le_le_0_compat. apply pos_INR. nra.
                                  --- apply Rlt_le. 
                                      pose proof  (delta_bound (n.+1 +1)%coq_nat).
                                      assert ( ((n.+1 + 1)%coq_nat < Z.to_nat (Z.pow_pos 2 23))%coq_nat).
                                      { destruct H. lia. } specialize (H8 H9).
                                      unfold d. rewrite -RmultE.
                                      nra.
                                      +++ replace (e * ((INR n.+1+1) * 3))%Re with ((INR n.+1 + 1) * (3 * e))%Re by nra.
                                          apply pow_invert_1.
                                          --- unfold e;rewrite -RmultE; simpl;nra.
                                          --- apply Rle_trans with 
                                                    (IZR (Z.pow_pos 2 23) + 1)%Re.
                                              *** apply Rlt_le. rewrite INR_IZR_INZ. apply Rplus_lt_compat_r. apply IZR_lt. lia.
                                              *** unfold e. rewrite -RmultE. simpl. unfold F', F_max; simpl; nra.
                        } rewrite H7 H3. 
                         assert ((((F' /2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e) *
                                               INR n.+1 *
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ n.+1 +
                                               INR n.+1 *
                                               (/ 2 *
                                                bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ (n.+1 - 1)%coq_nat +
                                               / 2 *
                                               bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) *
                                               ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                ^ (n.+1 - 1)%coq_nat - 1) /
                                               (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re = 
                                              ((((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat)) * INR n.+1 * 
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ^ n.+1) -
                                               ((INR n.+1 * e * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ n.+1 - INR n.+1 *
                                               (/ 2 *
                                                bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                               (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                               ^ (n.+1 - 1)%coq_nat) - / 2 *
                                               bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) *
                                               ((1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                ^ (n.+1 - 1)%coq_nat - 1) /
                                               (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))))%Re).
                         { nra. } rewrite H8. clear H8.
                         assert ( (F' / (INR 2 *
                                    (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))^ 2))%Re = 
                                  (((F' / 2) * /
                                    (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))^ 2))%Re).
                         { remember (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))%Re as de.
                           replace (INR 2) with 2%Re by (simpl;nra).
                           replace (F' / (2 * (1 + de) ^ 2))%Re with (F' * / (2 * (1 + de) ^ 2))%Re by nra.
                           rewrite Rinv_mult_distr. nra. nra. rewrite Heqde;simpl;nra.
                         } rewrite H8. clear H8. apply Rplus_le_compat.
                     **** unfold d. rewrite -RmultE.
                          remember (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))%Re as de.
                          unfold nr.
                          assert (((F' / 2) /
                                     ((nr + 1) * de ^ (n.+1 + 1)%coq_nat) *
                                     INR n.+1 * de ^ n.+1)%Re = 
                                   ((F'/2) * ( (INR n.+1 / (nr +1)) * / de))%Re).
                          { assert (((F' / 2) /
                                     ((nr + 1) * de ^ (n.+1 + 1)%coq_nat) *
                                     INR n.+1 * de ^ n.+1)%Re = ((F' / 2) */
                                     ((nr + 1) * de ^ (n.+1 + 1)%coq_nat) *
                                     INR n.+1 * de ^ n.+1)%Re). { nra. } rewrite H8. clear H8.
                            rewrite Rinv_mult_distr.
                            + assert ((F' / 2 *
                                         (/ (nr + 1) * / de ^ (n.+1 + 1)%coq_nat) *
                                         INR n.+1 * de ^ n.+1)%Re = 
                                      ((F'/2) * ((INR n.+1 / (nr+1)) * (de ^ n.+1 */ de ^ (n.+1 + 1)%coq_nat)))%Re).
                              { nra. } rewrite H8. clear H8.
                              assert ((de ^ n.+1 */ de ^ (n.+1 + 1)%coq_nat)%Re = / de).
                              { rewrite pow_add. rewrite Rinv_mult_distr.
                                assert ((de ^ n.+1 * (/ de ^ n.+1 * / de ^ 1))%Re = 
                                         ((de ^ n.+1 * / de ^ n.+1) * / de ^ 1)%Re).
                                { nra. } rewrite H8. rewrite Rinv_r. rewrite pow_1. nra.
                                apply pow_nonzero. rewrite Heqde;simpl;nra.
                                apply pow_nonzero. rewrite Heqde;simpl;nra.
                                rewrite pow_1. rewrite Heqde;simpl;nra.
                              } rewrite H8. nra.
                            + assert ((0 < nr +1)%Re -> (nr + 1)%Re <> 0%Re).
                              { nra. } apply H8. apply Rplus_lt_0_compat. unfold nr.
                              apply lt_0_INR;lia. nra.
                            + apply pow_nonzero. rewrite Heqde;simpl;nra.
                         } rewrite H8. apply Rmult_le_compat_l.
                         unfold F',F_max;simpl;nra.
                         fold nr. simpl. rewrite Rmult_1_r. rewrite Rinv_mult_distr.
                         apply Rmult_le_compat_r. rewrite Heqde;simpl;nra.
                         apply div_switch. split;try (rewrite Heqde;simpl;nra).
                         unfold nr. apply lt_0_INR;lia.
                         assert ( ((nr + 1) * / nr)%Re = (1 + /nr)%Re).
                         { rewrite Rmult_plus_distr_r. rewrite Rinv_r. nra.
                           unfold nr. apply not_0_INR. lia.
                         } rewrite H9. rewrite Heqde. apply Rplus_le_compat_l.
                         replace (/nr)%Re with (1 * /nr)%Re by nra.
                         replace (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))%Re with 
                                  ( (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) * 1)%Re by nra.
                         assert (1%Re = (nr * /nr)%Re).
                         { rewrite Rinv_r. nra. unfold nr. apply not_0_INR. lia. }
                         once rewrite H10.
                         assert ((/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1) *
                                    (nr * / nr))%Re = 
                                 (((/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) * nr) * /nr)%Re).
                         { nra. } rewrite H11.  apply Rmult_le_compat_r.
                         apply Rlt_le, Rinv_0_lt_compat. unfold nr. apply lt_0_INR;lia.
                         rewrite -H10. unfold nr.
                         apply Rle_trans with 
                         ((/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) *
                          INR (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%Re.
                         apply Rmult_le_compat_l. simpl;nra.
                         apply le_INR. lia. rewrite minus_INR.
                         rewrite INR_IZR_INZ. 
                        assert ((Z.of_nat (Z.to_nat (Z.pow_pos 2 23))) = Z.pow_pos 2 23).
                        { lia. } rewrite H12. simpl;nra. lia.
                        rewrite Heqde. simpl;nra.
                        rewrite Heqde. simpl;nra.
                   **** unfold e. rewrite -RmultE.
                                  assert ((INR n.+1 *
                                                          (/ 2 *
                                                           bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                          ^ n.+1 -
                                                          INR n.+1 *
                                                          (/ 2 *
                                                           bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                          ^ (n.+1 - 1)%coq_nat)%Re = 
                                                          ((INR n.+1 *  (/ 2 *
                                                           bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                          (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                          ^ (n.+1 - 1)%coq_nat * (/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re)).
                                   { assert (n.+1 = S ((n.+1 - 1)%coq_nat)). { lia. } 
                                     assert ((INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ n.+1 -
                                                             INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ (n.+1 - 1)%coq_nat)%Re = 
                                                           (INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ S ((n.+1 - 1)%coq_nat) -
                                                             INR n.+1 *
                                                             (/ 2 *
                                                              bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                             (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                             ^ (n.+1 - 1)%coq_nat)%Re).
                                      { by rewrite -H8. } rewrite H9. clear H9.
                                      assert ((INR n.+1 *
                                                           (/ 2 *
                                                            bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                           (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                           ^ (n.+1 - 1)%coq_nat.+1)%Re = 
                                                          (INR n.+1 *
                                                           (/ 2 *
                                                            bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)) *
                                                           (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
                                                           ^ (n.+1 - 1)%coq_nat * (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)))%Re).
                                                 { simpl. nra. } rewrite H9. clear H9. nra. 
                                } rewrite H8. clear H8.
                                match goal with |-context [(- (?a - ?b) <= _ )%Re]=>
                                  replace (- (a - b))%Re with (-a + b)%Re by nra
                                end.
                                match goal with |-context [(_ <= ?a)%Re]=>
                                  replace a with (0+a)%Re by nra
                                end. apply Rplus_le_compat.
                                apply Rge_le. apply Ropp_0_le_ge_contravar .
                                ***** repeat apply Rmult_le_pos.
                                      ----- apply pos_INR.
                                      ----- nra.
                                      ----- simpl;nra.
                                      ----- apply pow_le . simpl; nra.
                                      ----- nra.
                                      ----- simpl;nra.
                                ***** remember (/ 2 *
                                                        bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle))%Re as ee.
                                           remember  ( / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))%Re as de.
                                           assert ((ee * ((1 + de) ^ (n.+1 - 1)%coq_nat - 1) / de)%Re = 
                                                    (((1 + de) ^ (n.+1 - 1)%coq_nat - 1) * (ee / de))%Re).
                                       { nra. } rewrite H8.
                                       assert ( (2 * ee / de)%Re = (2 * (ee / de))%Re).
                                       { nra. } rewrite H9. apply Rmult_le_compat_r.
                                       rewrite Heqde Heqee;simpl;nra.
                                       apply Rlt_le. rewrite Heqde. apply (delta_bound (n.+1 - 1)%coq_nat).
                                       lia.
Qed.                   





(** not entirely in correct form. need to connect A, A1^{-1}. A2 **)
Theorem iterative_round_off_error {n:nat} :
  (1 < n.+1 /\ n.+1< (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in 
  (forall i k m n p :nat, (i < m.+1)%nat /\ (k < n.+1)%nat -> 
    (forall (a b : ftype Tsingle) (A1: 'M[ftype Tsingle]_(m.+1, n.+1))
            (A2: 'M[ftype Tsingle]_(n.+1, p.+1)),
      In (a, b)
        (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
           (vec_to_list_float n.+1 (\col_j (A2 j (inord k))))) ->
      is_finite (fprec Tsingle) (femax Tsingle) a = true /\
      is_finite (fprec Tsingle) (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re /\
      (Rabs (FT2R b) <=
       sqrt ((F'/2) / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re))->

  forall (A A1 A2 inv_A1: 'M[ftype Tsingle]_n.+1),
  (** ||A_1^{-1}A_2|| < 1 **)
  matrix_inf_norm (S_mat (FT2R_mat inv_A1) (FT2R_mat A2)) < 1 ->
  (** Relation between A, A_1, A_2 **)
  matrix_inf_norm (FT2R_mat (A +f (-f (A1 +f A2)))) <=
  matrix_inf_norm (FT2R_mat A) * d + e ->
  (** Relation between A_1, inv_A1 **)
  matrix_inf_norm (FT2R_mat (A1 *f inv_A1 ) - (FT2R_mat A1) *m (FT2R_mat inv_A1)) <=
  mat_mat_mult_err_bnd A1 inv_A1 ->
  forall (x_l b: list (ftype Tsingle)),
  let x0 := listR_to_vecR (FT2R_list x_l) in
  let b_real := listR_to_vecR (FT2R_list b) in
  let x0_f := list_to_vec_float x_l in
  let b_f := list_to_vec_float b in
  let x := invmx (FT2R_mat A) *m b_real in
  x != 0 ->
  forall k:nat, 
  let f:= tau k x (fun m:nat => @X_m_generic _ _ m n x0_f b_f inv_A1 A2) inv_A1 A1 A2 b_f in
  vec_inf_norm (FT2R_mat (@X_m_generic _ _ k n x0_f b_f inv_A1 A2) - 
                @X_m_real_generic n k x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2)) <=
  f *  error_sum k.+1 (@matrix_inf_norm n.+1 (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))).
Proof.
intros.
induction k.
+ assert (FT2R_mat (X_m_generic 0 x0_f b_f inv_A1 A2) -
           X_m_real_generic 0 x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2) = 0).
  { unfold X_m_real_generic, X_m_generic. apply matrixP. unfold eqrel.
    intros. rewrite !mxE. 
    destruct (nat_of_ord x1);
    ( unfold FT2R_list; simpl;
    rewrite -map_nth; simpl; apply /eqP; by rewrite subr_eq0).
  } rewrite H5. simpl. 
  rewrite /tau /error_sum //=. simpl in d, e. fold d e.
  rewrite big_ord_recr //= big_ord0 add0r expr0 mulr1.
  rewrite vec_inf_norm_0_is_0. apply /RleP.
  repeat apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos.
    * repeat apply Rplus_le_le_0_compat.
      ++ apply Rmult_le_pos.
         -- apply /RleP. apply matrix_norm_pd.
         -- unfold d;simpl. rewrite -RmultE. nra.
      ++ apply Rmult_le_pos.
         -- apply /RleP. apply mat_err_bnd_pd.
         -- unfold d;simpl. rewrite -RmultE. nra.
      ++ apply /RleP. apply mat_err_bnd_pd.
    * apply Rmult_le_pos. 
      ++ by apply theta_x_ge_0.
      ++ apply /RleP. apply vec_norm_pd.
  - apply Rmult_le_pos.
    ++  by apply E_3_err_bnd_pd .
    ++ unfold d;simpl. rewrite -RmultE. nra.
  - apply Rmult_le_pos.
    ++ apply /RleP. apply vec_norm_pd.
    ++ unfold d;simpl. rewrite -RmultE. nra.
  - apply Rmult_le_pos.
    ++ apply mat_vec_mult_err_bnd_pd .
    ++ unfold d;simpl. rewrite -RmultE. nra.
  - repeat apply Rmult_le_pos.
    ++ by apply theta_x_ge_0.
    ++ apply /RleP. apply bigmax_le_0.
        * apply /RleP. apply Rle_refl.
        * intros. rewrite seq_equiv. 
          rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H6.
          unfold e_i_real. unfold dot_prodR.
          apply sum_Rabs_pair_rel.
    ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. rewrite -RmultE. simpl; nra.
  - repeat apply Rmult_le_pos.
    ++ apply pos_INR.
    ++ nra.
    ++ simpl; nra.
    ++ apply pow_le . rewrite -!RmultE. simpl;nra.
  - repeat apply Rmult_le_pos.
    ++ nra.
    ++ simpl;nra.
    ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. rewrite -RmultE. simpl; nra.
    ++ rewrite -RmultE. simpl;nra.
  - apply mat_vec_mult_err_bnd_pd .
  - unfold e;simpl. rewrite -RmultE. nra.
+ (** Induction step **)
  set (xkr := (X_m_real_generic k x0 b_real (FT2R_mat inv_A1)(FT2R_mat A2))) in *.
  assert (X_m_real_generic k.+1 x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2) = 
          X_m_real_generic 1 xkr b_real (FT2R_mat inv_A1) (FT2R_mat A2)) by 
  apply X_m_real_iter.
  set (xkf := FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2)) in *.
  set (xkpf := FT2R_mat (X_m_generic k.+1 x0_f b_f inv_A1 A2)).
  assert (xkpf - X_m_real_generic k.+1 x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2) = 
          xkpf - X_m_real_generic 1 xkf b_real (FT2R_mat inv_A1) (FT2R_mat A2) + 
          X_m_real_generic 1 xkf b_real (FT2R_mat inv_A1) (FT2R_mat A2) - 
          X_m_real_generic 1 xkr b_real (FT2R_mat inv_A1) (FT2R_mat A2)).
  { rewrite H5. apply vec_sum_simpl. } rewrite H6.
  apply /RleP. eapply Rle_trans.
  - apply /RleP. by apply cs_ineq_vec_inf_norm. 
  - rewrite -RmultE. 
    assert (error_sum k.+2
         (matrix_inf_norm
            (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))) = 
      (1 + (matrix_inf_norm
            (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))) * 
          error_sum k.+1
             (matrix_inf_norm
                (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))))%Re).
    { rewrite !error_sum_equiv. rewrite -error_sum_aux2.
      by rewrite addrC.
    } rewrite H7.
    rewrite Rmult_plus_distr_l. 
    apply Rplus_le_compat.
    * unfold xkpf. simpl.
      remember (-f (inv_A1 *f A2)) as S_hat.
      remember (S_mat (FT2R_mat inv_A1) (FT2R_mat A2)) as Sm.
      assert (FT2R_mat
                (S_hat *f X_m_generic k x0_f b_f inv_A1 A2 +f inv_A1 *f b_f) -
                (Sm *m xkf + FT2R_mat inv_A1 *m b_real) = 
              ((FT2R_mat
                (S_hat *f X_m_generic k x0_f b_f inv_A1 A2 +f inv_A1 *f b_f) - 
               (FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) +
                FT2R_mat (inv_A1 *f b_f))) +
               ((FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) +
                FT2R_mat (inv_A1 *f b_f)) - (Sm *m xkf + FT2R_mat inv_A1 *m b_real)))).
      { by rewrite add_vec_distr_2. } rewrite H8.
      eapply Rle_trans.
      ++ apply /RleP. apply triang_ineq.
      ++ rewrite -RplusE.
         assert ((FT2R_mat
                      (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) +
                  FT2R_mat (inv_A1 *f b_f)) - (Sm *m xkf + FT2R_mat inv_A1 *m b_real) = 
                  (FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) - 
                   Sm *m xkf) + (FT2R_mat (inv_A1 *f b_f) - FT2R_mat inv_A1 *m b_real)).
         { apply add_vec_distr_3. } rewrite H9. clear H8 H9. 
         apply Rle_trans with 
         (vec_inf_norm
           (FT2R_mat
              (S_hat *f
               X_m_generic k x0_f b_f inv_A1 A2 +f
               inv_A1 *f b_f) -
            (FT2R_mat
               (S_hat *f
                X_m_generic k x0_f b_f inv_A1 A2) +
             FT2R_mat (inv_A1 *f b_f))) +
         (vec_inf_norm
           (FT2R_mat
              (S_hat *f
               X_m_generic k x0_f b_f inv_A1 A2) -
            Sm *m xkf) +
          vec_inf_norm (FT2R_mat (inv_A1 *f b_f) -
                          FT2R_mat inv_A1 *m b_real)))%Re.
         -- apply Rplus_le_compat_l. apply /RleP. apply triang_ineq.
         -- assert (FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) - Sm *m xkf =
                    (FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) - 
                     (FT2R_mat S_hat *m FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2))) +
                    (FT2R_mat S_hat *m FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2) -
                     Sm *m FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2))). 
            { by rewrite add_vec_distr_2. } rewrite H8.
            apply Rle_trans with
            (((vec_inf_norm (FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2)) +
              vec_inf_norm (FT2R_mat (inv_A1 *f b_f)))* d + e) +
            ((vec_inf_norm
              (FT2R_mat (S_hat *f X_m_generic k x0_f b_f inv_A1 A2) -
               FT2R_mat S_hat *m FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2)) +
             vec_inf_norm 
              ((FT2R_mat S_hat *m FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2) -
                  Sm *m FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2)))) +
             vec_inf_norm (FT2R_mat (inv_A1 *f b_f) - FT2R_mat inv_A1 *m b_real)))%Re.
            ** apply Rplus_le_compat.
               +++ apply dot_add_vec_float_le. lia. intros.
                   specialize (H0 i 0%nat n0 n0 0%nat).
                   assert ((i < n0.+1)%nat /\ (0 < n0.+1)%nat).
                   {  split; try apply H9. apply ltn0Sn . } 
                   specialize (H0 H11). specialize (H0 a b0 A0 v).
                   assert (v = \col_j v j (inord 0)).
                   { apply matrixP. unfold eqrel. intros. rewrite !mxE. 
                     assert (y = 0). { by apply ord1. } rewrite H12.
                     assert (@inord 0 0 = 0). { apply ord1. } by rewrite H13.
                   } rewrite H12 in H10. specialize (H0 H10). apply H0.  
               +++ apply Rplus_le_compat_r. apply /RleP. apply triang_ineq.
            ** rewrite -mulmxBl.
               apply Rle_trans with
               ((vec_inf_norm
                    (FT2R_mat
                       (S_hat *f
                        X_m_generic k x0_f b_f inv_A1 A2)) +
                  vec_inf_norm (FT2R_mat (inv_A1 *f b_f))) *
                 d + e +
                 (vec_inf_norm
                    (FT2R_mat
                       (S_hat *f
                        X_m_generic k x0_f b_f inv_A1 A2) -
                     FT2R_mat S_hat *m FT2R_mat
                                         (X_m_generic k
                                            x0_f b_f inv_A1
                                            A2)) +
                  matrix_inf_norm (FT2R_mat S_hat - Sm) * 
                  vec_inf_norm
                    (FT2R_mat
                       (X_m_generic k x0_f b_f inv_A1 A2)) +
                  vec_inf_norm
                    (FT2R_mat (inv_A1 *f b_f) -
                     FT2R_mat inv_A1 *m b_real)))%Re.
               +++ repeat apply Rplus_le_compat_l, Rplus_le_compat_r.
                   apply Rplus_le_compat_l. apply /RleP. apply submult_prop.
               +++ 








 admit.

    * simpl. 
      assert (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkf +
                FT2R_mat inv_A1 *m b_real -
                (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr +
                 FT2R_mat inv_A1 *m b_real) = 
               (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkf) -
               (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr)).
      { assert ((S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr +
                 FT2R_mat inv_A1 *m b_real) = 
                FT2R_mat inv_A1 *m b_real + 
                S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr).
        { by rewrite addrC. } rewrite H8. clear H8.
        by rewrite add_vec_distr_1.
      } rewrite H8. clear H8.
      rewrite -mulmxBr.
      eapply Rle_trans.
      ++ apply /RleP. apply submult_prop.
      ++ rewrite -RmultE.
         match goal with |-context[( _ <= ?a * (?b * ?c))%Re]=>
          replace (a * (b * c))%Re with (b * (a * c))%Re by nra
         end. apply Rmult_le_compat_l.
         -- apply /RleP. apply matrix_norm_pd.
         -- eapply Rle_trans.
            ** apply /RleP. apply IHk.
            ** rewrite -RmultE. apply Rmult_le_compat_r.
               +++ apply /RleP. apply error_sum_ge_0.
                   apply matrix_norm_pd.
               +++ apply tau_rel.       
Admitted.




End WITHNANS.