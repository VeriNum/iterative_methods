Require Import vcfloat.VCFloat.
Require Import floatlib.
Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Require Import fma_floating_point_model.

Section WITH_NANS.

Context {NANS: Nans}.

Definition diagmatrix t := list (ftype t).

Definition invert_diagmatrix {t} (v: diagmatrix t) : diagmatrix t :=
   map (BDIV (Zconst t 1)) v.

Definition diagmatrix_vector_mult {t}: diagmatrix t -> vector t -> vector t :=
  map2 BMULT.

Definition diagmatrix_matrix_mult {t} (v: diagmatrix t) (m: matrix t) : matrix t :=
  map2 (fun d => map (BMULT d)) v m.
  
Definition diag_of_matrix {t: type} (m: matrix t) : diagmatrix t :=
  map (fun i => matrix_index m i i) (seq 0 (matrix_rows_nat m)).

Definition remove_diag {t} (m: matrix t) : matrix t :=
 matrix_by_index (matrix_rows_nat m) (matrix_rows_nat m)
  (fun i j => if Nat.eq_dec i j then Zconst t 0 else matrix_index m i j).

Definition matrix_of_diag {t} (d: diagmatrix t) : matrix t :=
 matrix_by_index (length d) (length d)
  (fun i j => if Nat.eq_dec i j then nth i d (Zconst t 0) else Zconst t 0).

Definition jacobi_iter {t: type} (A1: diagmatrix t) (A2: matrix t) (b: vector t) (x: vector t) : vector t :=
   diagmatrix_vector_mult (invert_diagmatrix A1) (vector_sub b (matrix_vector_mult A2 x)).

Definition jacobi_residual {t: type} (A1: diagmatrix t) (A2: matrix t) (b: vector t) (x: vector t) : vector t :=
   diagmatrix_vector_mult A1 (vector_sub (jacobi_iter A1 A2 b x) x).


Definition going {t} (s acc: ftype t) := 
   andb (Binary.is_finite (fprec t) (femax t) s) (BCMP Lt false s acc).


Fixpoint iter_stop {t} {A} (norm2: A -> ftype t) (residual: A -> A) (f : A -> A) (n:nat) (acc: ftype t) (x:A) :=
 let y := f x in 
 let s := norm2 (residual x) in 
 match n with
 | O => (s, x)
 | S n' => if going s acc
                then iter_stop norm2 residual f n' acc y
                else (s,x)
  end.

Definition jacobi_n {t: type} (A: matrix t) (b: vector t) (x: vector t) (n: nat) : vector t :=
   let A1 := diag_of_matrix  A in 
   let A2 := remove_diag A in 
   Nat.iter n (jacobi_iter A1 A2 b) x.

Definition dist2 {t: type} (x y: vector t) := norm2 (vector_sub x y).

Definition jacobi {t: type} (A: matrix t) (b: vector t) (x: vector t) (acc: ftype t) (n: nat) :
         ftype t * vector t :=
   let A1 := diag_of_matrix  A in 
   let A2 := remove_diag A in 
   iter_stop norm2 (jacobi_residual A1 A2 b) (jacobi_iter A1 A2 b) (Nat.pred n) acc x.

End WITH_NANS.


Module Experiment.
(***************** Some sanity checks about diag_of_matrix and matrix_of_diag ***)

(* This turned out to be much lengthier than I expected.    I had to devel
  a whole theory of extensional matrices.  It started to feel like I was
  recapitulating all of MathComp.  My conclusion
  is that all of these lemmas should be done at the MathComp level
  and not at the list-of-lists level.  None of these lemmas are needed
  by the VST proofs, for example. *)

Section WITH_NANS.
Context {NANS: Nans}.

Local Ltac inv H := inversion H; clear H; subst.

Lemma length_diag_of_matrix: forall {t} (m: matrix t),
   matrix_cols_nat m (matrix_rows_nat m) ->
   length (diag_of_matrix m) = matrix_rows_nat m.
Proof.
 intros.
 unfold diag_of_matrix.
 rewrite map_length. rewrite seq_length. auto.
Qed.

Lemma rows_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_rows_nat (matrix_of_diag v) = length v.
Proof.
intros.
unfold matrix_of_diag.
apply matrix_by_index_rows.
Qed.

Lemma cols_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_cols_nat (matrix_of_diag v) (length v).
Proof.
intros.
unfold matrix_of_diag.
apply matrix_by_index_cols.
Qed.

Lemma diag_of_matrix_of_diag:
  forall {t} (d: diagmatrix t),
  diag_of_matrix (matrix_of_diag d) = d.
Proof.
intros.
unfold diag_of_matrix, matrix_of_diag.
apply (all_nth_eq (Zconst t 0));
rewrite map_length, seq_length, matrix_by_index_rows. auto.
intros.
set (f := fun _ => _).
transitivity (nth i (map f (seq 0 (length d))) (f (length d))).
f_equal. subst f. simpl.
unfold matrix_by_index.
unfold matrix_index.
do 2 (rewrite nth_overflow; auto).
simpl; lia.
rewrite map_length. rewrite seq_length. lia.
rewrite map_nth.
rewrite seq_nth by auto.
simpl.
subst f. simpl.
rewrite matrix_by_index_index by auto.
destruct (Nat.eq_dec i); try contradiction; auto.
Qed.

Lemma Forall_diag_of_matrix {t}: forall (P: ftype t -> Prop) (m: matrix t),
 matrix_cols_nat m (matrix_rows_nat m) ->
 Forall (Forall P) m -> Forall P (diag_of_matrix m).
Proof.
intros.
apply Forall_map.
apply Forall_seq.
intros.
red in H.
unfold matrix_index.
unfold matrix_rows_nat in *.
rewrite Forall_nth in H0.
specialize (H0 i nil ltac:(lia)).
rewrite Forall_nth in H0.
apply (H0 i (Zconst t 0)).
rewrite Forall_forall in H.
specialize (H (nth i m nil)).
rewrite H. lia.
apply nth_In. lia.
Qed.

Lemma matrix_binop_by_index:
  forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->  
  Forall2 (Forall2 feq) (map2 (map2 op) m1 m2)
  (matrix_by_index (matrix_rows_nat m1) cols (fun i j => op (matrix_index m1 i j) (matrix_index m2 i j))).


Ltac ind_des m1 :=
  match goal with
  | [ |- forall j, _ -> forall l, _] => induction m1; destruct j,l; simpl; intros
  | [ |- forall m2, _ ] => induction m1; destruct m2; simpl; intros
  end.
  
Proof.
intros.
apply (matrix_extensionality _ _ cols); auto.
-
rewrite matrix_by_index_rows.
clear H0 H1.
revert m2 H; ind_des m1 ; inv H; auto.

f_equal; eauto.
-
clear H.
revert m2 H1; ind_des H0; constructor.

inv H1.
unfold uncurry, map2.
rewrite map_length.
rewrite combine_length.
rewrite H4. apply  Nat.min_id.
apply IHForall.
inv H1; auto.
-
apply matrix_by_index_cols.
-
intros.
 assert (matrix_rows_nat (map2 (map2 op) m1 m2) = matrix_rows_nat m1). {
  clear - H. revert m2 H; ind_des m1; inv H; f_equal; eauto.
 }
 rewrite H4 in *.
 rewrite matrix_by_index_index; auto.
 revert m2 H H1 i H2 H4; ind_des m1; inv H.

 + lia.
 + destruct i; simpl.
   * clear IHm1.
       unfold matrix_index.
       unfold map2 at 1. unfold combine. simpl.
       unfold map2.
       inv H0. inv H1.
       clear - H3 H5.
       revert j H3 l H5; ind_des a; inv H5; auto.
       inv H3. inv H3.
       simpl in H3.
       eapply IHa; eauto. lia.
   *  unfold matrix_add.
     change (map2 (map2 ?f) (a::m1) (l::m2)) with (map2 f a l :: map2 (map2 f) m1 m2).
      repeat change (matrix_index (?x::?y) (S i) j) with (matrix_index y i j).
     inv H1. inv H0.
     eapply IHm1; eauto. lia.
Qed.

Lemma matrix_rows_nat_remove_diag: forall {t} (m: matrix t),
    matrix_cols_nat m (matrix_rows_nat m) ->
  matrix_rows_nat m = matrix_rows_nat (remove_diag m).
Proof.
 intros.
 symmetry;
 apply matrix_by_index_rows.
Qed.

Lemma matrix_rows_nat_matrix_binop:
 forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t),
 matrix_rows_nat m1 = matrix_rows_nat m2 ->
 matrix_rows_nat (map2 (map2 op) m1 m2) = matrix_rows_nat m1.
Proof.
intros.
unfold matrix_rows_nat in *.
unfold map2.
rewrite map_length.
rewrite combine_length.
lia.
Qed.

Lemma matrix_cols_nat_matrix_binop:
 forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
 matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
 matrix_cols_nat (map2 (map2 op) m1 m2) cols.
Proof.
induction m1; destruct m2; simpl; intros.
1,2,3: constructor.
inv H.
inv H0.
unfold map2 at 1.
unfold combine; fold (combine m1 m2).
simpl.
constructor; auto.
unfold map2. rewrite map_length.
rewrite combine_length; lia.
apply IHm1; auto.
Qed.

Lemma matrix_cols_nat_matrix_unop:
 forall {t} (op: ftype t -> ftype t) (m: matrix t) cols,
 matrix_cols_nat m cols ->
 matrix_cols_nat (map (map op) m) cols.
Proof.
induction 1; constructor.

rewrite map_length. auto.
apply IHForall.
Qed.

Lemma matrix_cols_nat_remove_diag: forall {t} (m: matrix t),
    matrix_cols_nat m (matrix_rows_nat m) ->
  matrix_cols_nat (remove_diag m) (matrix_rows_nat m).
Proof.
intros.
 apply matrix_by_index_cols.
Qed.

Local Open Scope nat.

Lemma matrix_index_diag:
 forall {t} (d: diagmatrix t) i j,
   i < length d -> j < length d ->
   matrix_index (matrix_of_diag d) i j =
    if (Nat.eq_dec i j) then nth i d (Zconst t 0) else Zconst t 0.
Proof.
intros.
unfold matrix_of_diag.
apply matrix_by_index_index; auto.
Qed.

Lemma binop_matrix_index:
 forall {t} (f: ftype t -> ftype t -> ftype t)
  (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
  forall i j, i < matrix_rows_nat m1 -> j < cols ->
  matrix_index (map2 (map2 f) m1 m2) i j =
  f (matrix_index m1 i j) (matrix_index m2 i j).
Proof.
unfold matrix_rows_nat.
induction m1; destruct m2; simpl; intros; inv H.
simpl in H2. lia.
inv H0.
inv H1.
destruct i.
unfold matrix_index. simpl.
unfold map2.
clear - H3 H4.
revert j H3 l H4; induction a; destruct l,j; simpl; intros; inv H4; auto.
1,2,3: simpl in H3. 1,2 : lia.
apply IHa; auto. lia.
apply (IHm1 m2 (length a)); auto. lia.
Qed.

Ltac  diag_matrix_len := rewrite length_diag_of_matrix; auto.
Ltac  matrix_rows_len := try (rewrite matrix_by_index_rows); try (diag_matrix_len).
Lemma remove_plus_diag: forall {t} (m: matrix t),
   matrix_cols_nat m (matrix_rows_nat m) ->
   Forall (Forall finite) m ->
   Forall2 (Forall2 feq) (matrix_add  (matrix_of_diag (diag_of_matrix m)) (remove_diag m)) m.
Proof.
intros.
apply matrix_extensionality with (cols := matrix_rows_nat m); auto.
unfold matrix_add.
rewrite matrix_rows_nat_matrix_binop.
1,2: unfold matrix_of_diag; matrix_rows_len.
unfold remove_diag. rewrite matrix_by_index_rows; auto.
apply matrix_cols_nat_matrix_binop.
replace (matrix_rows_nat m) with (length (diag_of_matrix m)).
apply matrix_by_index_cols.
diag_matrix_len.
apply matrix_by_index_cols.
unfold matrix_add at 1. 
rewrite matrix_rows_nat_matrix_binop.
2:{ unfold matrix_of_diag. rewrite matrix_by_index_rows.
    unfold remove_diag. matrix_rows_len.
}
unfold matrix_of_diag at 1.
matrix_rows_len; matrix_rows_len.
intros.
unfold matrix_add.
rewrite binop_matrix_index with (cols := matrix_rows_nat m); auto.
unfold matrix_of_diag, remove_diag.
rewrite !matrix_by_index_index; auto.
destruct (Nat.eq_dec i j).
unfold diag_of_matrix.
rewrite nth_map_seq; auto.
subst j.
apply BPLUS_0_r.
eapply matrix_index_prop; eauto.
apply BPLUS_0_l.
eapply matrix_index_prop; eauto.
1,2 : diag_matrix_len.
unfold matrix_of_diag, remove_diag.
rewrite !matrix_by_index_rows; auto.
diag_matrix_len.
replace (matrix_rows_nat m) with (length (diag_of_matrix m)).
apply matrix_by_index_cols.
diag_matrix_len.
apply matrix_by_index_cols.
unfold matrix_of_diag.
matrix_rows_len.
Qed.
End WITH_NANS.
End Experiment.

