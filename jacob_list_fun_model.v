Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.


Set Bullet Behavior "Strict Subproofs".

Definition BFMA {NAN: Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.

Definition matrix t := list (list (ftype t)).
Definition vector t := list (ftype t).

Definition dotprod {t: type} (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2)  (Zconst t 0).

Definition matrix_vector_mult {t: type} (m: matrix t) (v: vector t) : vector t :=
      map (fun row => dotprod row v) m.

Definition matrix_cols {t} (m: matrix t) cols :=
    Forall (fun r => Zlength r = cols) m.

Definition matrix_rows {t} (m: matrix t) : Z := Zlength m.


Definition matrix_matrix_mult {t: type} (m1 m2: matrix t) : matrix t :=
  map (fun col => matrix_vector_mult m1 col) m2.


Definition opp_matrix {t:type} (m: matrix t) : matrix t :=
  map (fun row => map (fun x => BOPP t x) row) m.

Definition vector_add {t:type} (v1 v2 : vector t) :=
  map (fun s => BPLUS t (fst s) (snd s)) (List.combine v1 v2).


Definition jacobi_iter {t: type} x0 b (A1 A2: matrix t) : vector t :=
  let S_J :=  opp_matrix (matrix_matrix_mult A1 A2) in
  let f_J := matrix_vector_mult A1 b in
  vector_add (matrix_vector_mult S_J x0) f_J.
  


Fixpoint iter {A} (f : A -> A) (n:nat) (x:A) :=
  match n with 
  | O => x 
  | S n' => iter f n' (f x)
  end.


