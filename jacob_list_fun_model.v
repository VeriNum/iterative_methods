Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.


Set Bullet Behavior "Strict Subproofs".

Definition BFMA {NAN: Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.

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
    Forall (fun r => Zlength r = cols) m.

Definition matrix_rows {t} (m: matrix t) : Z := Zlength m.

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

(***************** Some sanity checks about diag_of_matrix and matirx_of_diag ***)

Parameter finite: forall {t}, ftype t -> Prop.
Parameter float_eqv: forall {t}, ftype t -> ftype t -> Prop.
Axiom BPLUS_0_l: forall t x, finite x -> 
      float_eqv (BPLUS t (Zconst t 0) x) x.
Axiom BPLUS_0_r: forall t x, finite x -> 
      float_eqv (BPLUS t x (Zconst t 0)) x.
Axiom finite_0: forall t,  finite (Zconst t 0).
Axiom BPLUS_BOPP: forall {t} x f, finite x -> finite f -> float_eqv (BPLUS t x (BPLUS t f (BOPP t x))) f.

Definition matrix_eqv {t} : matrix t -> matrix t -> Prop :=
  Forall2 (Forall2 float_eqv).

Lemma Zlength_diag_of_matrix: forall {t} (m: matrix t),
   matrix_cols m (matrix_rows m) ->
   Zlength (diag_of_matrix m) = matrix_rows m.
Proof.
 intros.
 unfold matrix_cols, matrix_rows in *.
 assert (Forall (fun r => Z.le (Zlength m) (Zlength r)) m). {
   forget (Zlength m) as a. induction H; constructor; auto; try list_solve. 
} clear H.
Admitted. 

Lemma rows_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_rows (matrix_of_diag v) = Zlength v.
Proof.
induction v.
reflexivity.
unfold matrix_rows in *.
simpl.
list_solve.
Qed.

Lemma cols_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_cols (matrix_of_diag v) (Zlength v).
Proof.
induction v.
constructor.
constructor.
list_solve.
fold (matrix_of_diag v).
induction IHv. constructor. constructor; auto.
list_solve.
Qed.
 
Lemma Forall_diag_of_matrix {t}: forall (P: ftype t -> Prop) (m: matrix t),
 Forall (Forall P) m -> Forall P (diag_of_matrix m).
Admitted.

Lemma remove_plus_diag: forall {t} (m: matrix t),
   matrix_cols m (matrix_rows m) ->
   Forall (Forall finite) m ->
   matrix_eqv (matrix_add  (matrix_of_diag (diag_of_matrix m)) (remove_diag m)) m.
Proof.
intros * H3 H.
pose proof (Zlength_diag_of_matrix m H3).
pose proof (rows_matrix_of_diag (diag_of_matrix m)).
pose proof (cols_matrix_of_diag (diag_of_matrix m)).
unfold remove_diag.
assert (Forall finite (diag_of_matrix m)) by (apply Forall_diag_of_matrix; auto).
assert (Forall (Forall finite) (matrix_of_diag (diag_of_matrix m))). {
 clear - H4.
 forget (diag_of_matrix m) as d.
 induction H4. constructor.
 constructor; auto. constructor; auto. clear; induction l; constructor; auto.
 apply finite_0.
 fold (matrix_of_diag l).
 induction IHForall. constructor; auto.
 constructor. constructor; auto. apply finite_0.
 auto.
}
forget (Zlength (diag_of_matrix m)) as N.
set (d := matrix_of_diag _) in *.
clear H4. clearbody d.
rewrite H0 in H1.
rewrite <- H0 in H3.
clear H0.
revert d H1 H2 H5; induction m; destruct d; simpl; intros.
constructor.
elimtype False; clear - H1; unfold matrix_rows in *; list_solve.
elimtype False; clear - H1; unfold matrix_rows in *; list_solve.
inv H5.
inv H2.
inv H.
inv H3.
assert (matrix_rows d = matrix_rows m) 
  by (clear - H1; unfold matrix_rows in *; list_solve).
constructor.
-
clear - H4 H6 H2.
revert a H4 H2; induction H6; destruct a; intros. constructor.
elimtype False; list_solve.
elimtype False; list_solve.
inv H4.
constructor; auto.
unfold uncurry.
apply BPLUS_BOPP; auto.
apply IHForall; auto.
clear - H2; list_solve.
-
apply IHm; auto.
Qed.

