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

Definition list_to_vec_float {ty} {n:nat} 
(l : list (ftype ty)): 'cV[ftype ty]_n := 
\col_(i < n) (List.nth (nat_of_ord i) l (Zconst ty 0)).


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

Lemma nth_vec_to_list_float {ty} {n:nat} i m (v :'cV[ftype ty]_n.+1) d:
  (i < m)%nat ->
  nth (m.-1 -i) (@vec_to_list_float _ n m v) d = v (@inord n i) ord0.
Proof.
intros.
elim: m i H => [ | m IHm] i H.
+ by [].
+ simpl.
  rewrite leq_eqVlt in H.
  assert ((i == m) \/ (i < m)%nat).
  { by apply /orP. } destruct H0.
  - assert (i = m). { by apply /eqP. }
    rewrite H1. simpl.
    assert ((m - m)%nat = 0%N). 
    { apply /eqP. rewrite subn_eq0. by []. } by rewrite H2 /=.
  - assert (nth (m.-1 - i) (vec_to_list_float m v)
                d = v (inord i) ord0).
    { by apply IHm. } 
    rewrite -H1. rewrite -[in RHS]predn_sub.
    rewrite -subn_gt0 in H0. rewrite -predn_sub in H1.
    by destruct (m - i)%nat.
Qed.



(** Matrix multiplication as dot product  **)
Definition mulmx_float {ty} {m n p : nat} 
  (A: 'M[ftype ty]_(m.+1,n.+1)) (B: 'M[ftype ty]_(n.+1,p.+1)) : 
  'M[ftype ty]_(m.+1,p.+1):=
  \matrix_(i, k)
    let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
    let l2 := vec_to_list_float n.+1 (\col_(j < n.+1) B j k) in
    @dotprod ty l1 l2.


Definition opp_mat {ty} {m n: nat} (A : 'M[ftype ty]_(m.+1, n.+1)) 
  : 'M[ftype ty]_(m.+1, n.+1) :=
  \matrix_(i,j) (BOPP ty (A i j)). 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).

Print BDIV.

(** Functional model for Jacobi iteration **)
Definition A1_inv_J {ty} {n:nat} (A: 'M[ftype ty]_n.+1) : 'M[ftype ty]_n.+1:=
  \matrix_(i,j) 
    (if (i==j :> nat) then (BDIV ty (Zconst ty 1) (A i i)) else (Zconst ty 0)).

Definition A2_J {ty} {n:nat} (A: 'M[ftype ty]_n.+1): 
  'M[ftype ty]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then (Zconst ty 0) else A i j.

Definition jacobi_iter {ty} {n:nat} x0 b (A: 'M[ftype ty]_n.+1) : 
  'cV[ftype ty]_n.+1 :=
   let r := b +f (-f ((A2_J A) *f x0)) in
   (A1_inv_J A) *f r.


Definition X_m_jacobi {ty} {n:nat} m x0 b (A: 'M[ftype ty]_n.+1) :
  'cV[ftype ty]_n.+1 :=
   Nat.iter m  (fun x0 => jacobi_iter x0 b A) x0.



Definition matrix_inj {t} (A: matrix t) m n  : 'M[ftype t]_(m,n):=
    \matrix_(i < m, j < n) 
     nth j (nth i A [::]) (Zconst t 0).


Definition vector_inj {t} (v: vector t) n  : 'cV[ftype t]_n :=
   \col_(i < n) nth i v (Zconst t 0).

(*
Lemma vector_sub_equiv {ty} (v1 v2: vector ty) :
  (0 < length (combine v1 v2))%nat ->
  let size := (length (combine v1 v2)).-1 in
  let v1_v := vector_inj v1 size.+1 in 
  let v2_v := vector_inj v2 size.+1 in 
  rev (vector_sub v1 v2) = 
  vec_to_list_float size.+1 (\col_j (v1_v +f (-f v2_v)) j ord0).
Proof.
intros.
apply nth_ext with (Zconst ty 0) (Zconst ty 0).
+ admit.
+ intros. rewrite rev_nth.
  assert ( length (vector_sub v1 v2) = size.+1).
  { unfold size. rewrite prednK. admit. by []. } rewrite H1.
  induction n.
  - simpl. rewrite !mxE /=.
    unfold vector_sub, map2, uncurry.
    (*assert (0%F32 = (fun p : ftype Tsingle * ftype Tsingle
                         => let (x, y) := p in (x - y)%F32)
                     (Zconst Tsingle 0, Zconst Tsingle 0)).
    { admit. } once rewrite H1.
    Print map_nth. 
*)
    rewrite (@map_nth _ _ _ _ (Zconst ty 0, Zconst ty 0) _).
    rewrite combine_nth. 
    assert ((size - 0)%coq_nat = size). { lia. } rewrite H2.
    rewrite inordK.  
    unfold sum. admit.
    by [].
    admit.
  - simpl. rewrite -IHn.
  - admit.
Admitted.

*)

Print BFMA.
Print map.
Print fold_left.

(*
Lemma fold_left_pick {ty} i f (l: list ((ftype ty) * (ftype ty))) :
  ( i < length l)%nat ->
  (nth i (f (fst l) (snd l) (Zconst ty 0)) (Zconst ty 0)) <> (Zconst ty 0) ->
  (forall j, (j < length l)%nat -> j <> i -> (nth j (f (fst l) (snd l) (Zconst ty 0)) (Zconst ty 0)) = (Zconst ty 0)) -> 
  fold_left (fun l s => f (fst l) (snd l) s) l (Zconst ty 0)  = nth i (f (fst l) (snd l) (Zconst ty 0)) (Zconst ty 0).
Proof.
intros.
induction l.
+ by simpl in H.
+ simpl. destruct i.
  - simpl. simpl in H0. admit.
  - admit.
Admitted.
*)

Print BFMA.

(*
Lemma dotprod_diag {ty}  (A: matrix ty) (v: vector ty):
  let size := (length A).-1 in
  forall (i: 'I_size.+1),
  let A_v := matrix_inj A size.+1 size.+1 in  
  dotprod
  (vec_to_list_float size.+1
     (\row_j0 A1_inv_J A_v i j0)^T) v = 
  BFMA 
  (nth (nat_of_ord i) (vec_to_list_float size.+1 (\row_j0 A1_inv_J A_v i j0)^T) (Zconst ty 0) )
  (nth (nat_of_ord i) v (Zconst ty 0) ) (Zconst ty 0).
Proof.
intros.
unfold dotprod.
rewrite (@fold_left_pick ty _ 
         (fun (s : ftype ty) (x12 : ftype ty * ftype ty)
            => BFMA x12.1 x12.2 s) (combine
     (vec_to_list_float size.+1
        (\row_j0 A1_inv_J A_v i j0)^T) v)_ .

*)


Lemma dotprod_diag {ty} (v1 v2: vector ty) i :
  length v1 = length v2 ->
  (i < length v1)%nat -> 
  nth i v1 (Zconst ty 0) <> (Zconst ty 0) ->
  (forall j , (j < length v1)%nat -> j <> i -> nth j v1 (Zconst ty 0) = Zconst ty 0) ->
  dotprod v1 v2 = 
  BMULT ty (nth i v1 (Zconst ty 1)) (nth i v2 (Zconst ty 0)).
Proof.
intros.
unfold dotprod.



Admitted.


Lemma length_veclist {ty} {n m:nat} (v: 'cV[ftype ty]_n.+1):
  length (@vec_to_list_float _ n m v) = m.
Proof.
induction m.
+ simpl. auto.
+ simpl. by rewrite IHm.
Qed.

(*
Lemma dotprod_diag {ty} (v1 v2: vector ty) i:
  dotprod v1 v2 =
  BMULT 
  (nth i v1 (Zconst ty 0) (nth i v2 (Zconst ty 0).

*)


(***
BMULT ty
  (nth i
     (invert_diagmatrix (diag_of_matrix A))
     (Zconst ty 0))
  (nth i
     (vector_sub b
        (matrix_vector_mult (remove_diag A)
           x_n)) (Zconst ty 0)) =
BMULT ty
  (BDIV ty (Zconst ty 1)
     (nth i (nth i A []) (Zconst ty 0)))
***)

Import jacob_list_fun_model.Experiment.

Lemma A1_invert_equiv {ty} (A : matrix ty) i: 
  (i < length A)%coq_nat ->
  nth i
     (invert_diagmatrix (diag_of_matrix A))
     (Zconst ty 1) =
  BDIV ty (Zconst ty 1)
     (nth i (nth i A []) (Zconst ty 0)).
Proof.
intros.
assert (nth i (invert_diagmatrix (diag_of_matrix A))
            (Zconst ty 1) = 
        BDIV ty (Zconst ty 1) (nth i (diag_of_matrix A) (Zconst ty 1))).
{ rewrite -[in RHS]map_nth. unfold invert_diagmatrix.
  assert ((BDIV ty (Zconst ty 1) (Zconst ty 1)) = (Zconst ty 1)).
  { admit. } rewrite H0. 
  (*Unable to unify
 "@nth (ftype ty) i
    (@map (ftype ty) (ftype ty)
       (@BDIV NANS ty (Zconst ty 1))
       (@diag_of_matrix ty A)) 
    (Zconst ty 1)"
with
 "@nth (ftype ty) i
    (@map (ftype ty) (ftype ty)
       (@BDIV FPCompCert.nans ty
          (Zconst ty 1))
       (@diag_of_matrix ty A)) 
    (Zconst ty 1)".
*)
admit.
 } rewrite H0.
unfold diag_of_matrix.  rewrite nth_map_seq.
by unfold matrix_index.
by unfold matrix_rows_nat.
Admitted.




Lemma func_model_equiv {ty} (A: matrix ty) (b: vector ty) (x: vector ty) (n: nat) :
  let size := (length A).-1 in  
  let x_v := vector_inj x size.+1 in 
  let b_v := vector_inj b size.+1 in 
  let A_v := matrix_inj A size.+1 size.+1 in
  length b = length A -> 
  vector_inj (jacobi_n A b x n) size.+1 = @X_m_jacobi ty size n x_v b_v A_v.
Proof.
intros.
induction n.
+ apply /matrixP. unfold eqrel.
  intros. by rewrite !mxE /=.  
+ simpl. rewrite -IHn.
  apply /matrixP. unfold eqrel.
  move=> i j.
  rewrite !mxE. 
  remember (jacobi_n A b x n) as x_n.
  (*nth i
  (map
     (fun p : ftype ty * ftype ty =>
      let (x0, y) := p in BMULT ty x0 y)
     (combine
        (invert_diagmatrix
           (diag_of_matrix A))
        (vector_sub b
           (matrix_vector_mult
              (remove_diag A) x_n))))
  (Zconst ty 0)
*)
  assert (nth i
            (jacob_list_fun_model.jacobi_iter
               (invert_diagmatrix (diag_of_matrix A))
               (remove_diag A) b x_n)
            (Zconst ty 0) = BMULT ty
              (nth i
                 (invert_diagmatrix (diag_of_matrix A))
                 (Zconst ty 1))
              (nth i
                 (vector_sub b
                    (matrix_vector_mult (remove_diag A)
                       x_n)) (Zconst ty 0))).
  { unfold jacob_list_fun_model.jacobi_iter.
    unfold diagmatrix_vector_mult, map2, uncurry.
    assert (Zconst ty 0 = BMULT ty (Zconst ty 1) (Zconst ty 0)).
    { admit. } rewrite H0.
    admit.
  } rewrite H0. 
  assert (dotprod (vec_to_list_float size.+1
                      (\row_j0 A1_inv_J A_v i j0)^T) 
          (vec_to_list_float size.+1
               (\col_j0 (b_v +f
                         -f (A2_J A_v *f vector_inj x_n size.+1)) j0 j)) = 
          BMULT ty (nth (size.+1.-1 - (nat_of_ord i)) (vec_to_list_float size.+1
                      (\row_j0 A1_inv_J A_v i j0)^T) (Zconst ty 1))
          (nth (size.+1.-1 - (nat_of_ord i)) (vec_to_list_float size.+1
               (\col_j0 (b_v +f
                         -f (A2_J A_v *f vector_inj x_n size.+1)) j0 j)) (Zconst ty 0))).
  { rewrite (@dotprod_diag _ _ _ (size.+1.-1 - (nat_of_ord i))); try by [].
    + by rewrite !length_veclist.
    + rewrite length_veclist. rewrite ltn_subLR. simpl. admit.
      simpl. apply ltnSE, ltn_ord.
    + rewrite nth_vec_to_list_float. rewrite !mxE /=.
      assert (i == @inord size i :> nat ). { by rewrite inord_val. }
      rewrite H1. admit. apply ltn_ord.
    + intros. 
      admit.
  } 
  assert ((let l1 :=
             vec_to_list_float size.+1
               (\row_j0 A1_inv_J A_v i j0)^T in
           let l2 :=
             vec_to_list_float size.+1
               (\col_j0 (b_v +f
                         -f
                         (A2_J A_v *f
                          vector_inj x_n size.+1)) j0
                          j) in
           dotprod l1 l2) = 
           dotprod (vec_to_list_float size.+1
                      (\row_j0 A1_inv_J A_v i j0)^T) 
          (vec_to_list_float size.+1
               (\col_j0 (b_v +f
                         -f (A2_J A_v *f vector_inj x_n size.+1)) j0 j))).
   { by []. } rewrite H2 H1. clear H2 H1.
   rewrite A1_invert_equiv.
   - rewrite nth_vec_to_list_float.
     * rewrite !mxE.
       assert (i == @inord size i :> nat ). { by rewrite inord_val. }
       rewrite H1. 
       rewrite nth_vec_to_list_float.
       ++ rewrite !mxE.
          unfold vector_sub, map2, uncurry,sum.
          unfold matrix_vector_mult. unfold dotprod.
(*
  - unfold invert_diagmatrix, vector_sub, map2.
    rewrite !map_length combine_length.
    unfold matrix_vector_mult. rewrite !map_length !seq_length.
    unfold matrix_rows_nat. by rewrite H;lia.
*)
Admitted.

End WITHNANS.