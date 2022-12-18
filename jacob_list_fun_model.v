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

Definition dotprod {t: type} (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2)  (Zconst t 0).

Definition matrix_vector_mult {t: type} (m: matrix t) (v: vector t) : vector t :=
      map (fun row => dotprod row v) m.

Definition map2 {A B C: Type} (f: A -> B -> C) al bl :=
  map (uncurry f) (List.combine al bl).


Function diag_of_matrix {t: type} (m: matrix t) {measure length m} : diagmatrix t :=
  match m with
  | (x::r)::m' => x :: diag_of_matrix (map (@tl (ftype t)) m')
  | _ => nil
  end.
Proof. intros. subst. simpl. rewrite map_length. constructor. Qed.

Arguments diag_of_matrix {t} m : rename.

Fixpoint matrix_of_diag {t} (d: diagmatrix t) :=
 match d with
 | x::r => (x :: map (fun _ => Zconst t 0) r)::map (cons (Zconst t 0))(matrix_of_diag r)
 | nil => nil
 end.

Definition opp_matrix {t:type} (m: matrix t) : matrix t :=
  map (map (BOPP t)) m.

Definition matrix_add {t} : matrix t -> matrix t -> matrix t :=
  map2 (map2 (BPLUS t)).

Definition remove_diag {t} (m: matrix t) : matrix t :=
 matrix_add m (opp_matrix (matrix_of_diag (diag_of_matrix m))).

Definition diagmatrix_vector_mult {t}: diagmatrix t -> vector t -> vector t :=
  map2 (BMULT t).

Definition diagmatrix_matrix_mult {t} (v: diagmatrix t) (m: matrix t) : matrix t :=
  map2 (fun d => map (BMULT t d)) v m.
  
Definition matrix_cols {t} (m: matrix t) cols :=
    Forall (fun r => length r = cols) m.

Definition matrix_rows {t} (m: matrix t) : nat := length m.

Definition matrix_matrix_mult {t: type} (m1 m2: matrix t) : matrix t :=
  map (matrix_vector_mult m1) m2.

Definition vector_add {t:type} (v1 v2 : vector t) :=
  map2 (BPLUS t) v1 v2.

Definition vector_sub {t:type} (v1 v2 : vector t) :=
  map2 (BMINUS t) v1 v2.

Definition jacobi_iter {t: type} (A1inv: diagmatrix t) (A2: matrix t) (b: vector t) (x: vector t) : vector t :=
   diagmatrix_vector_mult A1inv (vector_sub b (matrix_vector_mult A2 x)).

Fixpoint iter {A} (f : A -> A) (n:nat) (x:A) :=
  match n with 
  | O => x 
  | S n' => iter f n' (f x)
  end.

Definition jacobi {t: type} (A: matrix t) (b: vector t) (x: vector t) (n: nat) : vector t :=
   let A1 := diag_of_matrix  A in 
   let A1inv := invert_diagmatrix A1 in
   let A2 := matrix_add A (opp_matrix (matrix_of_diag A1)) in
   iter (jacobi_iter A1inv A2 b) n x.

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

Lemma BPLUS_0_l: forall t x, finite x -> 
      float_eqv (BPLUS t (Zconst t 0) x) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.
Lemma BPLUS_0_r: forall t x, finite x -> 
      float_eqv (BPLUS t x (Zconst t 0)) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma finite_0: forall t,  finite (Zconst t 0).
Proof.
intros; apply I.
Qed.

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

Lemma Zlength_diag_of_matrix: forall {t} (m: matrix t),
   matrix_cols m (matrix_rows m) ->
   length (diag_of_matrix m) = matrix_rows m.
Proof.
 intros.
 unfold matrix_cols, matrix_rows in *.
remember (length m) as n.
revert m Heqn H; 
induction n; intros; destruct m; inv Heqn; rewrite diag_of_matrix_equation.
reflexivity.
inv H.
destruct l. inv H2.
simpl in H2|-*.
f_equal.
rewrite IHn; clear IHn; auto.
symmetry; apply map_length.
clear - H3.
set (k := length m) in *; clearbody k.
induction H3; constructor.
destruct x; simpl in *; try lia.
apply IHForall.
Qed.

Lemma rows_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_rows (matrix_of_diag v) = length v.
Proof.
induction v.
reflexivity.
unfold matrix_rows in *.
simpl.
rewrite map_length. f_equal; auto.
Qed.

Lemma cols_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_cols (matrix_of_diag v) (length v).
Proof.
induction v.
constructor.
constructor.
simpl. f_equal. apply map_length.
fold (matrix_of_diag v).
induction IHv. constructor. constructor; auto.
simpl; auto.
Qed.
 
Lemma Forall_diag_of_matrix {t}: forall (P: ftype t -> Prop) (m: matrix t),
 Forall (Forall P) m -> Forall P (diag_of_matrix m).
Proof.
intros.
remember (length m) as n.
revert m Heqn H; induction n; destruct m; simpl; intros; inv Heqn;
  rewrite diag_of_matrix_equation.
constructor.
inv H.
destruct l; constructor; inv H2; auto.
apply IHn.
symmetry; apply map_length.
clear - H3.
induction H3.
constructor.
constructor; auto.
clear - H.
destruct x; simpl; auto.
inv H; auto.
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
replace (_ + _) with 0 by lia; reflexivity.
Qed.

Lemma diag_of_matrix_of_diag:
  forall {t} (d: diagmatrix t),
  diag_of_matrix (matrix_of_diag d) = d.
Proof.
induction d; simpl; intros; rewrite diag_of_matrix_equation; auto.
f_equal; auto.
rewrite map_map. simpl.
etransitivity; [ | apply IHd].
f_equal.
clear.
induction (matrix_of_diag _).
reflexivity.
simpl.
f_equal; auto.
Qed.

Definition matrix_index {t} (m: matrix t) (i j: nat) :=
 nth j (nth i m nil) (Zconst t 0).

Open Scope nat.

Lemma matrix_extensionality: 
  forall {t} (m1 m2: matrix t) cols,
  matrix_rows m1 = matrix_rows m2 ->
  matrix_cols m1 cols -> matrix_cols m2 cols ->
  (forall i j, i < matrix_rows m1 -> j < cols ->
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

Definition matrix_by_index {t} (rows cols: nat) 
          (f: nat -> nat -> ftype t) : matrix t :=
     map (fun i => map (f i) (seq 0 cols)) (seq 0 rows).

Lemma matrix_by_index_rows:
  forall {t} rows cols (f: nat -> nat -> ftype t),
  matrix_rows (matrix_by_index rows cols f) = rows.
Proof.
intros.
unfold matrix_by_index, matrix_rows.
rewrite map_length. rewrite seq_length. auto.
Qed.

Lemma matrix_by_index_cols:
  forall {t} rows cols (f: nat -> nat -> ftype t),
  matrix_cols (matrix_by_index rows cols f) cols.
Proof.
intros.
unfold matrix_by_index, matrix_cols.
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

Lemma matrix_binop_by_index:
  forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
  matrix_rows m1 = matrix_rows m2 ->
  matrix_cols m1 cols -> matrix_cols m2 cols ->  
  matrix_eqv (map2 (map2 op) m1 m2)
  (matrix_by_index (matrix_rows m1) cols (fun i j => op (matrix_index m1 i j) (matrix_index m2 i j))).
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
 assert (matrix_rows (map2 (map2 op) m1 m2) = matrix_rows m1). {
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

Lemma matrix_rows_remove_diag: forall {t} (m: matrix t),
    matrix_cols m (matrix_rows m) ->
  matrix_rows m = matrix_rows (remove_diag m).
Proof.
 intros.
 unfold matrix_rows in *.
 unfold remove_diag.
 unfold matrix_add.
 unfold map2 at 1. rewrite map_length.
 rewrite combine_length.
 unfold opp_matrix.
 rewrite map_length.
 change (length (matrix_of_diag ?x)) with (matrix_rows (matrix_of_diag x)).
 rewrite rows_matrix_of_diag.
 rewrite Zlength_diag_of_matrix.
 unfold matrix_rows. lia.
 auto.
Qed.

Lemma matrix_cols_matrix_binop:
 forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
 matrix_cols m1 cols -> matrix_cols m2 cols ->
 matrix_cols (map2 (map2 op) m1 m2) cols.
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

Lemma matrix_cols_matrix_unop:
 forall {t} (op: ftype t -> ftype t) (m: matrix t) cols,
 matrix_cols m cols ->
 matrix_cols (map (map op) m) cols.
Proof.
induction 1.
constructor.
constructor.
rewrite map_length. auto.
apply IHForall.
Qed.


Lemma matrix_cols_remove_diag: forall {t} (m: matrix t),
    matrix_cols m (matrix_rows m) ->
  matrix_cols (remove_diag m) (matrix_rows m).
Proof.
intros.
unfold remove_diag.
apply matrix_cols_matrix_binop; auto.
apply matrix_cols_matrix_unop; auto.
rewrite <- Zlength_diag_of_matrix by auto.
apply cols_matrix_of_diag.
Qed.

Lemma matrix_index_prop:
 forall {t} (P: ftype t -> Prop) (m: matrix t) (cols i j : nat), 
    matrix_cols m cols ->
    Forall (Forall P) m -> 
    i < matrix_rows m -> j < cols ->
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
   matrix_index (matrix_of_diag d) i j =
    if (Nat.eq_dec i j) then nth i d (Zconst t 0) else Zconst t 0.
Proof.
unfold matrix_index.
induction d; intros.
destruct i,j; simpl; auto.
destruct (Nat.eq_dec i j); auto.
destruct i,j; simpl; auto.
-
clear.
revert j; induction d; destruct j; simpl; auto.
-
clear.
revert i; induction (matrix_of_diag d); destruct i; simpl; auto.
-
transitivity (nth j (nth i (matrix_of_diag d) []) (Zconst t 0)).
clear.
revert i; induction (matrix_of_diag d); destruct i,j; simpl; auto.
rewrite IHd.
destruct (Nat.eq_dec i j); auto.
Qed.

Lemma matrix_index_diag':
 forall {t} (m: matrix t),
    matrix_cols m (matrix_rows m) ->
   forall i, 
   matrix_index m i i = nth i (diag_of_matrix m) (Zconst t 0).
Proof.
intros.
remember (matrix_rows m) as N.
unfold matrix_index.
revert m HeqN H i; induction N; destruct m,i; intros; inv HeqN; 
 simpl; rewrite diag_of_matrix_equation; simpl; auto.
destruct l. auto.
simpl. auto.
destruct l; simpl; auto.
inv H.
inv H2.
inv H.
simpl in H2.
erewrite  <- IHN; clear IHN.
clear.
replace (@nil (ftype t)) with (tl (@nil (ftype t))).
rewrite map_nth.
simpl.
destruct (nth i m nil); auto.
destruct i; auto.
auto.
unfold matrix_rows. rewrite map_length; auto.
clear - H3.
set (N := matrix_rows m) in *; clearbody N.
induction H3; constructor. destruct x; inv H; auto.
auto.
Qed.

Lemma remove_plus_diag: forall {t} (m: matrix t),
   matrix_cols m (matrix_rows m) ->
   Forall (Forall finite) m ->
   matrix_eqv (matrix_add  (matrix_of_diag (diag_of_matrix m)) (remove_diag m)) m.
Proof.
intros.
unfold matrix_add.
rewrite matrix_binop_by_index with (cols := matrix_rows m).
 2: rewrite <- matrix_rows_remove_diag by auto;
   rewrite rows_matrix_of_diag, Zlength_diag_of_matrix; auto.
2: rewrite <- Zlength_diag_of_matrix by auto; 
   apply cols_matrix_of_diag.
2: apply matrix_cols_remove_diag; auto.
rewrite rows_matrix_of_diag.
rewrite Zlength_diag_of_matrix by auto.
apply matrix_extensionality with (cols := matrix_rows m); auto.
apply matrix_by_index_rows.
apply matrix_by_index_cols.
rewrite matrix_by_index_rows. 
intros.
rewrite matrix_by_index_index by auto.
rewrite matrix_index_diag.
unfold remove_diag, matrix_add.
(* . . . and on and on . . . *)
Abort.
