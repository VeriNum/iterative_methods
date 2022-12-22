Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import Iterative.floatlib.
Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".

Definition matrix t := list (list (ftype t)).
Definition vector t := list (ftype t).
Definition diagmatrix t := list (ftype t).

Definition invert_diagmatrix {t} (v: diagmatrix t) : diagmatrix t :=
   map (BDIV t (Zconst t 1)) v.

Definition norm2 {t} (v: vector t) := dotprod v v.

Definition map2 {A B C: Type} (f: A -> B -> C) al bl :=
  map (uncurry f) (List.combine al bl).

Definition opp_matrix {t:type} (m: matrix t) : matrix t :=
  map (map (BOPP t)) m.

Definition matrix_add {t} : matrix t -> matrix t -> matrix t :=
  map2 (map2 (BPLUS t)).

Definition diagmatrix_vector_mult {t}: diagmatrix t -> vector t -> vector t :=
  map2 (BMULT t).

Definition diagmatrix_matrix_mult {t} (v: diagmatrix t) (m: matrix t) : matrix t :=
  map2 (fun d => map (BMULT t d)) v m.
  
Definition matrix_matrix_mult {t: type} (m1 m2: matrix t) : matrix t :=
  map (matrix_vector_mult m1) m2.

Definition vector_add {t:type} (v1 v2 : vector t) :=
  map2 (BPLUS t) v1 v2.

Definition vector_sub {t:type} (v1 v2 : vector t) :=
  map2 (BMINUS t) v1 v2.

Definition matrix_index {t} (m: matrix t) (i j: nat) :=
 nth j (nth i m nil) (Zconst t 0).

Definition matrix_by_index {t} (rows cols: nat) 
          (f: nat -> nat -> ftype t) : matrix t :=
     map (fun i => map (f i) (seq 0 cols)) (seq 0 rows).

Definition matrix_rows_nat {t} (m: matrix t) := length m.

Definition matrix_cols_nat {t} (m: matrix t) cols :=
    Forall (fun r => length r = cols) m.

Definition diag_of_matrix {t: type} (m: matrix t) : diagmatrix t :=
  map (fun i => matrix_index m i i) (seq 0 (matrix_rows_nat m)).

Definition remove_diag {t} (m: matrix t) : matrix t :=
 matrix_by_index (matrix_rows_nat m) (matrix_rows_nat m)
  (fun i j => if Nat.eq_dec i j then Zconst t 0 else matrix_index m i j).

Definition matrix_of_diag {t} (d: diagmatrix t) : matrix t :=
 matrix_by_index (length d) (length d)
  (fun i j => if Nat.eq_dec i j then nth i d (Zconst t 0) else Zconst t 0).

Definition jacobi_iter {t: type} (A1inv: diagmatrix t) (A2: matrix t) (b: vector t) (x: vector t) : vector t :=
   diagmatrix_vector_mult A1inv (vector_sub b (matrix_vector_mult A2 x)).

Fixpoint iter_stop {t} {A} (dist2: A -> A -> ftype t) (f : A -> A) (n:nat) (acc: ftype t) (x:A) :=
  match n with 
  | O => x 
  | S n' => let y := f x in
                 let d := dist2 x y in
                 if BCMP t Lt true d acc then y
                 else iter_stop dist2 f n' acc y
  end.

Definition jacobi {t: type} (A: matrix t) (b: vector t) (x: vector t) (acc: ftype t) (n: nat) : vector t :=
   let A1 := diag_of_matrix  A in 
   let A1inv := invert_diagmatrix A1 in
   let A2 := remove_diag A in 
   let dist2 x y := norm2 (vector_sub x y) in 
   iter_stop dist2 (jacobi_iter A1inv A2 b) n acc x.

Definition old_jacobi_iter {t: type} x0 b (A1: diagmatrix t) (A2: matrix t) : vector t :=
  let S_J :=  opp_matrix (diagmatrix_matrix_mult A1 A2) in
  let f_J := diagmatrix_vector_mult A1 b in
  vector_add (matrix_vector_mult S_J x0) f_J.

Module Experiment.
(***************** Some sanity checks about diag_of_matrix and matrix_of_diag ***)

(* This turned out to be much lengthier than I expected.    I had to devel
  a whole theory of extensional matrices.  It started to feel like I was
  recapitulating all of MathComp.  My conclusion
  is that all of these lemmas should be done at the MathComp level
  and not at the list-of-lists level.  None of these lemmas are needed
  by the VST proofs, for example. *)

Local Ltac inv H := inversion H; clear H; subst.

Definition matrix_eqv {t} : matrix t -> matrix t -> Prop :=
  Forall2 (Forall2 float_eqv).

Lemma matrix_eqv_refl {t: type} : reflexive _ (@matrix_eqv t).
Proof.
intro m.
induction m; constructor; auto.
induction a; constructor; auto.
Qed.

Lemma matrix_eqv_sym {t: type} : symmetric _ (@matrix_eqv t).
Proof.
red.
unfold matrix_eqv.
induction x; destruct y; intros; inv H; constructor; auto.
clear - H3.
induction H3; constructor; auto.
symmetry; auto.
Qed.

Lemma matrix_eqv_trans {t: type} : transitive _ (@matrix_eqv t).
Proof.
red.
unfold matrix_eqv.
induction x; destruct y,z; intros; inv H; inv H0; constructor; auto.
clear - H3 H4.
revert a H4; induction H3; intros; inv H4; constructor; auto.
etransitivity; eauto.
eauto.
Qed.

Add Parametric Relation {t: type}: (matrix t) (@matrix_eqv t)
  reflexivity proved by matrix_eqv_refl
  symmetry proved by matrix_eqv_sym
  transitivity proved by matrix_eqv_trans
   as matrix_eqv_rel.

Lemma matrix_by_index_rows:
  forall {t} rows cols (f: nat -> nat -> ftype t),
  matrix_rows_nat (matrix_by_index rows cols f) = rows.
Proof.
intros.
unfold matrix_by_index, matrix_rows_nat.
rewrite map_length. rewrite seq_length. auto.
Qed.

Local Open Scope nat.

Lemma matrix_by_index_cols:
  forall {t} rows cols (f: nat -> nat -> ftype t),
  matrix_cols_nat (matrix_by_index rows cols f) cols.
Proof.
intros.
unfold matrix_by_index, matrix_cols_nat.
pose (k := 0). change (seq 0 rows) with (seq k rows).
clearbody k. revert k; induction rows; intros; constructor; auto.
rewrite map_length, seq_length. auto.
Qed.

Lemma nth_map_seq:
  forall {A} (f: nat -> A) d (i n: nat), i < n -> nth i (map f (seq 0 n)) d = f i.
Proof.
intros.
assert (i < n) by lia.
clear H.
transitivity (f (i+0)); [ | f_equal; lia].
set (k := 0 ) in *.
clearbody k.
revert k i H0; induction n; simpl; intros.
destruct i; auto; lia.
destruct i.
destruct k; auto; lia.
rewrite (IHn (S k) i).
f_equal; lia.
lia.
Qed.


Lemma matrix_by_index_index:
  forall {t} rows cols (f: nat -> nat -> ftype t) i j,
   i < rows -> j < cols ->
   matrix_index (matrix_by_index rows cols f) i j = f i j.
Proof.
 intros.
 unfold matrix_index, matrix_by_index.
 rewrite nth_map_seq; auto.
 rewrite nth_map_seq; auto.
Qed.

Lemma matrix_extensionality_strong: 
  forall {t} (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
  (forall i j, i < matrix_rows_nat m1 -> j < cols ->
        matrix_index m1 i j = matrix_index m2 i j) ->
    m1 = m2.
Proof.
 induction m1; destruct m2; simpl; intros; inv H; auto.
 inv H0. inv H1.
 f_equal.
 clear - H3 H2.
 specialize (H2 O).
 unfold matrix_index in H2. simpl in H2.
 revert l H3 H2; induction a; destruct l; simpl; intros; inv H3; f_equal; auto.
 apply (H2 O); try lia.
 apply IHa; auto. intros j ? ?. apply (H2 (S j)); try lia.
 eapply IHm1; eauto.
 intros i j ? ?. apply (H2 (S i) j); lia.
Qed.

Lemma matrix_extensionality: 
  forall {t} (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
  (forall i j, i < matrix_rows_nat m1 -> j < cols ->
        float_eqv (matrix_index m1 i j) (matrix_index m2 i j)) ->
  matrix_eqv m1 m2.
Proof.
 unfold matrix_eqv.
 induction m1; destruct m2; simpl; intros; inv H; auto.
 inv H0. inv H1.
 constructor. 
 clear - H3 H2.
 specialize (H2 O).
 unfold matrix_index in H2. simpl in H2.
 revert l H3 H2; induction a; destruct l; simpl; intros; inv H3; auto.
 constructor.
 apply (H2 O); try lia.
 apply IHa; auto. intros j ? ?. apply (H2 (S j)); try lia.
 eapply IHm1; eauto.
 intros i j ? ?. apply (H2 (S i) j); lia.
Qed.

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

Lemma Forall_map: forall  {A B} (P: B -> Prop) (f: A -> B) (al: list A),
  Forall (Basics.compose P f) al ->
  Forall P (map f al).
Proof.
induction 1; constructor; auto.
Qed.

Lemma Forall_seq: forall (P: nat -> Prop) (lo n: nat),
  (forall i, lo <= i < lo+n -> P i) ->
  Forall P (seq lo n).
Proof.
intros.
revert lo H; induction n; simpl; intros; constructor.
apply H. lia.
apply IHn; intros.
apply H; lia.
Qed.

Lemma Forall_diag_of_matrix {t}: forall (P: ftype t -> Prop) (m: matrix t),
 matrix_cols_nat m (matrix_rows_nat m) ->
 Forall (Forall P) m -> Forall P (diag_of_matrix m).
Proof.
intros.
apply Forall_map.
apply Forall_seq.
intros.
red.
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

Lemma BPLUS_BOPP_diag: 
  forall {t} (x: ftype t), finite x -> BPLUS t x (BOPP t x) = Zconst t 0.
Proof.
intros.
destruct x,s; inv H; try reflexivity;
unfold BPLUS, BOPP, BINOP, Binary.Bplus, Binary.Bopp, Binary.BSN2B,
   BinarySingleNaN.binary_normalize, BinarySingleNaN.binary_normalize,
   BinarySingleNaN.binary_normalize; simpl;
 unfold BinarySingleNaN.binary_normalize, BinarySingleNaN.Fplus_naive,
  SpecFloat.cond_Zopp;
replace (_ + _)%Z with 0%Z by lia; reflexivity.
Qed.

Lemma all_nth_eq:
 forall {A} d (al bl: list A),
  length al = length bl ->
  (forall i, i < length al -> nth i al d = nth i bl d) -> 
  al=bl.
Proof.
induction al; destruct bl; simpl; intros; try discriminate; f_equal.
apply (H0 0 ltac:(lia)).
apply IHal.
lia.
intros.
apply (H0 (S i)). lia.
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
rewrite nth_overflow; auto.
rewrite nth_overflow; auto.
simpl; lia.
rewrite map_length. rewrite seq_length. lia.
rewrite map_nth.
rewrite seq_nth by auto.
simpl.
subst f. simpl.
rewrite matrix_by_index_index by auto.
destruct (Nat.eq_dec i); try contradiction; auto.
Qed.

Lemma matrix_binop_by_index:
  forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->  
  matrix_eqv (map2 (map2 op) m1 m2)
  (matrix_by_index (matrix_rows_nat m1) cols (fun i j => op (matrix_index m1 i j) (matrix_index m2 i j))).
Proof.
intros.
apply (matrix_extensionality _ _ cols); auto.
-
rewrite matrix_by_index_rows.
clear H0 H1.
revert m2 H; induction m1; destruct m2; simpl; intros; inv H; auto.
f_equal; eauto.
-
clear H.
revert m2 H1; induction H0; destruct m2; simpl; intros; constructor.
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
  clear - H. revert m2 H; induction m1; destruct m2; simpl; intros; inv H; f_equal; eauto.
 }
 rewrite H4 in *.
 rewrite matrix_by_index_index; auto.
 revert m2 H H1 i H2 H4; induction m1; destruct m2; simpl; intros; inv H.
 + lia.
 + destruct i; simpl.
   * clear IHm1.
       unfold matrix_index.
       unfold map2 at 1. unfold combine. simpl.
       unfold map2.
       inv H0. inv H1.
       clear - H3 H5.
       revert j H3 l H5; induction a; destruct j,l; simpl; intros; inv H5; auto.
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
constructor.
constructor.
constructor.
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
induction 1.
constructor.
constructor.
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

Lemma matrix_index_prop:
 forall {t} (P: ftype t -> Prop) (m: matrix t) (cols i j : nat), 
    matrix_cols_nat m cols ->
    Forall (Forall P) m -> 
    i < matrix_rows_nat m -> j < cols ->
    P (matrix_index m i j).
Proof.
induction m; intros.
inv H1.
inv H0.
simpl in H1.
inv H.
unfold matrix_index.
destruct i; simpl.
clear - H2 H5.
revert j H2; induction H5; intros.
inv H2.
destruct j; simpl; auto.
apply IHForall. simpl in H2; lia.
eapply IHm; eauto.
lia.
Qed.

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
simpl in H3; lia. simpl in H3; lia.
simpl in H3. apply IHa; auto. lia.
apply (IHm1 m2 (length a)); auto.
lia.
Qed.

Lemma remove_plus_diag: forall {t} (m: matrix t),
   matrix_cols_nat m (matrix_rows_nat m) ->
   Forall (Forall finite) m ->
   matrix_eqv (matrix_add  (matrix_of_diag (diag_of_matrix m)) (remove_diag m)) m.
Proof.
intros.
apply matrix_extensionality with (cols := matrix_rows_nat m); auto.
unfold matrix_add.
rewrite matrix_rows_nat_matrix_binop.
unfold matrix_of_diag.
rewrite matrix_by_index_rows.
apply length_diag_of_matrix; auto.
unfold matrix_of_diag.
rewrite matrix_by_index_rows.
rewrite length_diag_of_matrix; auto.
unfold remove_diag.
rewrite matrix_by_index_rows; auto.
apply matrix_cols_nat_matrix_binop.
replace (matrix_rows_nat m) with (length (diag_of_matrix m)).
apply matrix_by_index_cols.
apply length_diag_of_matrix; auto.
apply matrix_by_index_cols.
unfold matrix_add at 1.
rewrite matrix_rows_nat_matrix_binop.
2:{ unfold matrix_of_diag. rewrite matrix_by_index_rows.
    unfold remove_diag.  rewrite matrix_by_index_rows.
    apply length_diag_of_matrix; auto.
}
unfold matrix_of_diag at 1.
rewrite matrix_by_index_rows; auto.
rewrite length_diag_of_matrix; auto.
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
rewrite length_diag_of_matrix; auto.
rewrite length_diag_of_matrix; auto.
unfold matrix_of_diag, remove_diag.
rewrite !matrix_by_index_rows; auto.
apply length_diag_of_matrix; auto.
replace (matrix_rows_nat m) with (length (diag_of_matrix m)).
apply matrix_by_index_cols.
apply length_diag_of_matrix; auto.
apply matrix_by_index_cols.
unfold matrix_of_diag.
rewrite matrix_by_index_rows; auto.
rewrite length_diag_of_matrix; auto.
Qed.

End Experiment.

