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


Definition vec_to_list_float_1 {ty} {n:nat} (m:nat) (v :'cV[ftype ty]_n.+1) := 
  rev (vec_to_list_float m v). 


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
    let l1 := vec_to_list_float_1 n.+1 (\row_(j < n.+1) A i j)^T in
    let l2 := vec_to_list_float_1 n.+1 (\col_(j < n.+1) B j k) in
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


Lemma fold_left_for_list {ty} (L: list (ftype ty * ftype ty)) i f:
  (i < length L)%nat -> 
  (forall j , (j < length L)%nat -> j <> i -> nth j (map (fun L => fst L) L) (Zconst ty 0) = (Zconst ty 0)) ->
  fold_left f L (Zconst ty 0) = f (Zconst ty 0) (nth i L (Zconst ty 0, Zconst ty 0)) .
Proof.
intros.
induction L.
+ by simpl in H.
+ simpl. admit.
Admitted.







Lemma dotprod_diag {ty} (v1 v2: vector ty) i :
  length v1 = length v2 ->
  (i < length v1)%nat -> 
  (forall j , (j < length v1)%nat -> j <> i -> nth j v1 (Zconst ty 0) = Zconst ty 0) ->
  dotprod v1 v2 = 
  BMULT ty (nth i v1 (Zconst ty 1)) (nth i v2 (Zconst ty 0)).
Proof.
intros.
unfold dotprod.
(** try skipn and firstn **)
assert (fold_left
            (fun (s : ftype ty) (x12 : ftype ty * ftype ty)
             => BFMA x12.1 x12.2 s) (combine v1 v2)
            (Zconst ty 0)  = 
        (fun (s : ftype ty) (x12 : ftype ty * ftype ty)
             => BFMA x12.1 x12.2 s) (Zconst ty 0)
         (nth i (combine v1 v2) (Zconst ty 0, Zconst ty 0))).
{ rewrite (@fold_left_for_list  _ _ i _); try by [].
  + rewrite combine_length. by rewrite H.



rewrite (@fold_left_for_list _ (combine v1 v2) i  _ ).






Admitted.


Lemma length_veclist {ty} {n m:nat} (v: 'cV[ftype ty]_n.+1):
  length (@vec_to_list_float _ n m v) = m.
Proof.
induction m.
+ simpl. auto.
+ simpl. by rewrite IHm.
Qed.


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


Lemma v_equiv {ty} (v: vector ty) size:
  length v = size.+1 -> 
  v = rev (vec_to_list_float size.+1
          (\col_j0 vector_inj v size.+1 j0 ord0)).
Proof.
intros. 
apply nth_ext with (Zconst ty 0) (Zconst ty 0).
+ rewrite rev_length length_veclist. by []. 
+ intros. rewrite rev_nth length_veclist.
  assert ((size.+1 - n.+1)%coq_nat = (size.+1.-1 - n)%coq_nat).
  { by []. } rewrite H1.
  rewrite nth_vec_to_list_float.
  - rewrite !mxE /=. rewrite inordK. 
    * by [].
    * rewrite -H. by apply /ssrnat.ltP.
  - rewrite -H. by apply /ssrnat.ltP.
  - by rewrite -H. 
Qed.


Lemma A2_equiv {ty} (A: matrix ty) size i :
  length A = size.+1 ->
  (i < size.+1)%coq_nat ->
  let A_v := matrix_inj A size.+1 size.+1 in
  nth i
     (matrix_by_index (matrix_rows_nat A)
        (matrix_rows_nat A)
        (fun i0 j : nat =>
         if is_left (Nat.eq_dec i0 j)
         then Zconst ty 0
         else matrix_index A i0 j)) [] =
  rev (vec_to_list_float size.+1
     (\row_j0 A2_J A_v (inord i) j0)^T).
Proof.
intros.
apply nth_ext with (Zconst ty 0) (Zconst ty 0).
+ rewrite rev_length length_veclist. 
  unfold matrix_by_index. rewrite nth_map_seq.
  - rewrite map_length. rewrite seq_length. by unfold matrix_rows_nat.
  - unfold matrix_rows_nat. by rewrite H. 
+ intros.
  rewrite rev_nth length_veclist.
  assert ((size.+1 - n.+1)%coq_nat = (size.+1.-1 - n)%coq_nat).
  { by []. } rewrite H2.
  rewrite nth_vec_to_list_float.
  - rewrite !mxE. unfold matrix_by_index.
    rewrite nth_map_seq.
    * rewrite nth_map_seq.
      ++ rewrite !inordK.
         -- unfold is_left.
            case: (Nat.eq_dec i n). 
            ** intros. rewrite a //=. 
               assert (n == n :>nat = true). 
               { by apply /eqP. }
               by rewrite H3.
            ** intros.
               assert ( i == n :> nat = false). { by apply /eqP. }
               rewrite H3. by unfold matrix_index. 
         -- rewrite /matrix_by_index nth_map_seq in H1.
            ** rewrite map_length seq_length /matrix_rows_nat H in H1.
               by apply /ssrnat.ltP.
            ** unfold matrix_rows_nat. by rewrite H. 
         -- by apply /ssrnat.ltP.
      ++ rewrite /matrix_by_index nth_map_seq in H1.
         -- rewrite map_length seq_length /matrix_rows_nat H in H1.
            by rewrite /matrix_rows_nat H.
         -- unfold matrix_rows_nat. by rewrite H.
    * unfold matrix_rows_nat. by rewrite H.
  - rewrite /matrix_by_index nth_map_seq in H1.
    -- rewrite map_length seq_length /matrix_rows_nat H in H1.
       by apply /ssrnat.ltP.
    -- unfold matrix_rows_nat. by rewrite H.
  - rewrite /matrix_by_index nth_map_seq in H1.
    -- by rewrite map_length seq_length /matrix_rows_nat H in H1.
    -- unfold matrix_rows_nat. by rewrite H.
Qed.

Lemma combine_rev {ty} (v1 v2: vector ty):
  (combine (rev v1) (rev v2)) = rev (combine v1 v2).
Proof.
Admitted.



Lemma dotprod_rev_equiv {ty} (v1 v2: vector ty):
  dotprod (rev v1) (rev v2) = dotprod v1 v2.
Proof.
unfold dotprod.
assert ((combine (rev v1) (rev v2)) = rev (combine v1 v2)).
{ admit. } rewrite H. 
(** with the vec_to_float_list, I am actually implementing a
    fold right model
**)
Admitted.



Lemma residual_equiv {ty} (v: vector ty) (A: matrix ty) i:
  (0 < length A)%nat ->
  let size := (length A).-1 in   
  let A_v := matrix_inj A size.+1 size.+1 in
  length A = length v ->
  (i < length A)%nat ->
  nth i (matrix_vector_mult (remove_diag A) v) (Zconst ty 0) = 
  dotprod (vec_to_list_float size.+1
              (\row_j0 A2_J A_v (inord i) j0)^T)
           (vec_to_list_float size.+1
              (\col_j0 vector_inj v size.+1 j0 ord0)).
Proof.
intros.
assert (nth i (matrix_vector_mult (remove_diag A) v)
          (Zconst ty 0) = 
        dotprod 
        (nth i (matrix_by_index (matrix_rows_nat A)
                  (matrix_rows_nat A)
                  (fun i0 j : nat =>
                   if Nat.eq_dec i0 j
                   then Zconst ty 0
                   else matrix_index A i0 j)) [])
        v).
{ unfold matrix_by_index. rewrite nth_map_seq.
  unfold matrix_vector_mult.
  rewrite (@map_nth _ _ _ _ [] _ ).
  unfold remove_diag.
  unfold matrix_by_index. rewrite nth_map_seq.
  + rewrite (@map_ext _ _ _ (fun j : nat =>
      if is_left (Nat.eq_dec i j)
      then Zconst ty 0
      else matrix_index A i j)); try by [].
    intros. unfold is_left.
    by case: (Nat.eq_dec i a).
  + unfold matrix_rows_nat. by apply /ssrnat.ltP.
  + unfold matrix_rows_nat. by apply /ssrnat.ltP.
} rewrite H2. clear H2. 
assert (v = rev (vec_to_list_float size.+1
          (\col_j0 vector_inj v size.+1 j0 ord0))).
{ apply v_equiv. rewrite -H0. rewrite /size.
  by rewrite prednK.
}
rewrite [in LHS]H2.
rewrite (@A2_equiv _ _ size _).


unfold matrix_vector_mult. 
unfold remove_diag.
Check ((matrix_by_index (matrix_rows_nat A)
        (matrix_rows_nat A)
        (fun i0 j : nat =>
         if Nat.eq_dec i0 j
         then Zconst ty 0
         else matrix_index A i0 j))).
Check (nth i A []).
unfold A2_J.
Admitted.

Lemma plus_minus_eqiv {ty} (x y : ftype ty):
  BPLUS ty x (BOPP ty y) = BMINUS ty x y.
Proof.
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
  { assert (nth i
            (jacob_list_fun_model.jacobi_iter
               (invert_diagmatrix (diag_of_matrix A))
               (remove_diag A) b x_n)
            (Zconst ty 0) = 
            nth i
            (jacob_list_fun_model.jacobi_iter
               (invert_diagmatrix (diag_of_matrix A))
               (remove_diag A) b x_n)
            (BMULT ty (Zconst ty 1) (Zconst ty 0))).
    { assert (Zconst ty 0 = BMULT ty (Zconst ty 1) (Zconst ty 0)).
      { admit. } rewrite [in LHS]H0. reflexivity.
    } rewrite H0.
    unfold jacob_list_fun_model.jacobi_iter.
    unfold diagmatrix_vector_mult, map2, uncurry.
    Check ((fun p : ftype ty * ftype ty =>
      let (x0, y) := p in BMULT ty x0 y)).
    Search BMULT.

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
     * assert (nth i
                   (vector_sub b
                      (matrix_vector_mult (remove_diag A) x_n))
                   (Zconst ty 0) = 
               BMINUS ty (nth i b (Zconst ty 0))
                    (nth i  (matrix_vector_mult (remove_diag A)
                            x_n) (Zconst ty 0))).
       { unfold vector_sub, map2, uncurry. 
         rewrite (@map_nth _ _ _ _ (Zconst ty 0, Zconst ty 0) _ ).
         rewrite combine_nth. 
         (*Unable to unify
             "@BMINUS NANS ty
                (@nth (ftype ty) i b (Zconst ty 0))
                (@nth (ftype ty) i
                   (@matrix_vector_mult ty
                      (@remove_diag ty A) x_n) 
                   (Zconst ty 0))"
            with
             "@BMINUS FPCompCert.nans ty
                (@nth (ftype ty) i b (Zconst ty 0))
                (@nth (ftype ty) i
                   (@matrix_vector_mult ty
                      (@remove_diag ty A) x_n) 
                   (Zconst ty 0))". *)
       admit. } rewrite H1. 
       rewrite !mxE.
       assert (i == @inord size i :> nat ). { by rewrite inord_val. }
       rewrite H2. 
       rewrite nth_vec_to_list_float.
       ++ rewrite !mxE. unfold sum. rewrite residual_equiv.
          rewrite inordK.
          -- rewrite -/size. rewrite -/A_v.
             rewrite plus_minus_eqiv. 
             assert (j = ord0). { apply ord1. } rewrite H3.
             reflexivity. 
          -- admit.
          -- admit.
       ++ admit.
     * admit.
  - admit.
(*
  - unfold invert_diagmatrix, vector_sub, map2.
    rewrite !map_length combine_length.
    unfold matrix_vector_mult. rewrite !map_length !seq_length.
    unfold matrix_rows_nat. by rewrite H;lia.
*)
Admitted.

End WITHNANS.