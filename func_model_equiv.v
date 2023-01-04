From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
Require Import dot_prod_defn float_model_generic.
Require Import floatlib jacob_list_fun_model.
Set Bullet Behavior "Strict Subproofs". 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITHNANS.
Context {NANS: Nans}. 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).


Definition jacobi_iter {n:nat} x0 b (A: 'M[ftype Tsingle]_n.+1) : 
  'cV[ftype Tsingle]_n.+1 :=
   let r := b +f (-f ((A2_J A) *f x0)) in
   (A1_inv_J A) *f r.


Definition X_m_jacobi {n:nat} m x0 b (A: 'M[ftype Tsingle]_n.+1) :
  'cV[ftype Tsingle]_n.+1 :=
   Nat.iter m  (fun x0 => jacobi_iter x0 b A) x0.


(** Define a relation between the list list definition of matrix
    and mathcomp definition of matrix
**)

Print List.nth.



Definition matrix_inj {t} (A: matrix t) n  : 'M[ftype t]_n:=
    \matrix_(i < n, j < n) 
     nth j (nth i A [::]) (Zconst t 0).


(** Check **)
Definition A_check : (matrix Tsingle) :=  
  [[1%F32 ; 2%F32]; [3%F32 ; 4%F32]].

Check A_check.

Definition A_1 : 'M[ftype Tsingle]_2 :=
  \matrix_(i < 2, j < 2)
   if (i == 0%N :> nat) then
    (if (j == 0%N :> nat) then 1%F32 else 2%F32) else
    (if (j == 0%N :> nat) then 3%F32 else 4%F32).

(*
Lemma matrix_equiv_check:
  matrix_inj A_check = A_1.
Proof.
apply /matrixP. unfold eqrel. 
assert (length A_check = 2%nat).
{ by []. } 
intros. rewrite !mxE //=.
case: x. intros.
+ simpl. destruct m.
  - simpl.
    case: y. intros.
    simpl. destruct m.
    * by simpl.
    * simpl. destruct m.
      ++ by [].
      ++ rewrite H in i0. admit.
 - simpl. 
   case: y. intros.
   simpl. destruct m0.
   * simpl. destruct m.
     ++ by simpl.
     ++ admit.
   * simpl. destruct m.
     ++ simpl.
 *)

Definition vector_inj {t} (v: vector t) n  : 'cV[ftype t]_n :=
   \col_(i < n) nth i v (Zconst t 0).


(***
vector_sub b
  (matrix_vector_mult (remove_diag A) x_n) =
vec_to_list_float size.+1
  (\col_j0 (b_v +f
            -f
            (A2_J A_v *f
             vector_inj x_n size.+1)) j0 j)
***)

Lemma vector_sub_equiv (v1 v2: vector Tsingle) :
  (0 < length (combine v1 v2))%nat ->
  let size := (length (combine v1 v2)).-1 in
  let v1_v := vector_inj v1 size.+1 in 
  let v2_v := vector_inj v2 size.+1 in 
  rev (vector_sub v1 v2) = 
  vec_to_list_float size.+1 (\col_j (v1_v +f (-f v2_v)) j ord0).
Proof.
intros.
apply nth_ext with 0%F32 0%F32.
+ admit.
+ intros. simpl.  
  induction n.
  - simpl. rewrite !mxE /=.
    unfold vector_sub, map2, uncurry.
    (*assert (0%F32 = (fun p : ftype Tsingle * ftype Tsingle
                         => let (x, y) := p in (x - y)%F32)
                     (Zconst Tsingle 0, Zconst Tsingle 0)).
    { admit. } once rewrite H1.
    Print map_nth. 
*)
    rewrite (@map_nth _ _ _ _ (Zconst Tsingle 0, Zconst Tsingle 0) _).
    rewrite combine_nth.
    admit.
    admit.
  - simpl.




Print map.
apply (nth_ext.

remember (combine v1 v2) as L.
induction L.
+ by simpl in H.  
+ simpl. rewrite IHL. rewrite /v1_v /v2_v.
  assert (size.+1 = (length L).-1.+1).
  { rewrite /size. simpl.




 destruct L.
+ by simpl in H.
+ 





Lemma func_model_equiv (A: matrix Tsingle) (b: vector Tsingle) (x: vector Tsingle) (n: nat) :
  let size := (length A).-1 in  
  let x_v := vector_inj x size.+1 in 
  let b_v := vector_inj b size.+1 in 
  let A_v := matrix_inj A size.+1 in 
  vector_inj (jacobi_n A b x n) size.+1 = @X_m_jacobi size n x_v b_v A_v.
Proof.
intros.
induction n.
+ apply /matrixP. unfold eqrel.
  intros. by rewrite !mxE /=.  
+ simpl. rewrite -IHn.
  apply /matrixP. unfold eqrel.
  move=> i j.
  rewrite !mxE. 
  unfold jacob_list_fun_model.jacobi_iter.
  remember (jacobi_n A b x n) as x_n.
  assert ((vector_sub b
           (matrix_vector_mult (remove_diag A) x_n))  = 
          (vec_to_list_float size.+1
              (\col_j0 (b_v +f
                        -f (A2_J A_v *f vector_inj x_n size.+1)) j0 j))).
  { unfold vector_sub.



  remember  (combine
     (vec_to_list_float size.+1 (\row_j0 A1_inv_J A_v i j0)^T)
     (vec_to_list_float size.+1
        (\col_j0 (b_v +f -f
                  (A2_J A_v *f vector_inj x_n size.+1)) j0 j))) as L.
  unfold diagmatrix_vector_mult.


  Print diagmatrix_vector_mult.
  Print dot_prodF.


unfold dot_prodF. sum_fixF.
   
elim: n x0  => [ |n IHn ] x0.
+ by rewrite /= /x_v !mxE /=. 
+ simpl. unfold jacobi_iter.




End WITHNANS.