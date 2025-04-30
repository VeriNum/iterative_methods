Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse_model build_csr distinct.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.


#[export] Declare Instance M: MallocAPD.

Definition coord_le {t} (a b : Z*Z*ftype t) : Prop :=
  fst (fst a) < fst (fst b) 
 \/ fst (fst a) = fst (fst b) /\ snd (fst a) <= snd (fst b).

(*
Definition coord_lt {t} (a b : Z*Z*ftype t) : Prop :=
  fst (fst a) < fst (fst b) 
 \/ fst (fst a) = fst (fst b) /\ snd (fst a) < snd (fst b).
*)

Definition coord_leb {t} (a b : Z*Z*ftype t) : bool :=
  orb (fst (fst a) <? fst (fst b))
       (andb (fst (fst a) =? fst (fst b)) (snd (fst a) <=? snd (fst b))).

(*
Definition coord_ltb {t} (a b : Z*Z*ftype t) : bool :=
  orb (fst (fst a) <? fst (fst b))
       (andb (fst (fst a) =? fst (fst b)) (snd (fst a) <? snd (fst b))).
*)

Lemma reflect_coord_le {t} a b : reflect (@coord_le t a b) (@coord_leb t a b).
Proof.
destruct (coord_leb a b) eqn:?H; [constructor 1 | constructor 2];
 unfold coord_le, coord_leb in *; lia.
Qed.

(*

Lemma reflect_coord_lt {t} a b : reflect (@coord_lt t a b) (@coord_ltb t a b).
Proof.
destruct (coord_ltb a b) eqn:?H; [constructor 1 | constructor 2];
 unfold coord_lt, coord_ltb in *; lia.
Qed.
*)

Instance CoordBO {t}: BoolOrder (@coord_le t) := 
  {| test := coord_leb; test_spec := reflect_coord_le |}.

Instance CoordPO {t: type}: PreOrder (@coord_le t).
Proof.
constructor.
- intro. unfold complement, coord_le; simpl. lia.
- intros ? ? ? *. unfold coord_le; simpl; lia.
Qed.

Instance CoordBPO {t: type}: BPO.BoolPreOrder (@coord_le t) :=
 {| BPO.BO := CoordBO; BPO.PO := CoordPO |}.

Lemma Permutation_Zlength:
  forall {A} {al bl: list A}, Permutation al bl -> Zlength al = Zlength bl.
Proof.
intros. rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
Qed.


Definition t_coo := Tstruct _coo_matrix noattr.

Definition coo_rep (sh: share) (coo: coo_matrix Tdouble) (p: val) : mpred :=
 EX (maxn: Z) (rp cp vp : val), 
 !! (0 <= Zlength (coo_entries coo) <= maxn /\ maxn <= Int.max_signed 
     /\ 0 <= coo_rows coo < Int.max_signed 
     /\ 0 <= coo_cols coo < Int.max_signed /\ coo_matrix_wellformed coo) &&
  data_at sh t_coo (rp, (cp, (vp, (Vint (Int.repr (Zlength (coo_entries coo))), (Vint (Int.repr maxn), 
                     (Vint (Int.repr (coo_rows coo)), 
                     (Vint (Int.repr (coo_cols coo))))))))) p *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (fst (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) rp *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (snd (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) cp *
  data_at sh (tarray tdouble maxn)
    (map (fun e => Vfloat (snd e)) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) vp.

Definition add_to_coo {t} (coo: coo_matrix t) (i j: Z) (v: ftype t): coo_matrix t :=
 {| coo_rows := coo_rows coo ;
    coo_cols := coo_cols coo ;
    coo_entries := coo_entries coo ++ [(i,j,v)]
  |}.

Definition add_to_coo_matrix_spec :=
 DECLARE _add_to_coo_matrix
 WITH sh: share, p : val, i: Z, j: Z, x: ftype Tdouble, coo: coo_matrix Tdouble
 PRE [ tptr t_coo, tuint, tuint, tdouble ]
   PROP (writable_share sh; 0 <= i < Int.max_unsigned; 0 <= j < Int.max_unsigned) 
   PARAMS ( p; Vint (Int.repr i); Vint (Int.repr j); Vfloat x) 
   SEP (coo_rep sh coo p)
 POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (coo_rep sh (add_to_coo coo i j x) p).


Definition swap_spec :=
 DECLARE _swap
 WITH sh: share, coo: coo_matrix Tdouble, p: val, a: Z, b: Z
 PRE [ tptr t_coo, tuint, tuint ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo;
         0 <= a < Zlength (coo_entries coo);
         0 <= b < Zlength (coo_entries coo))
    PARAMS( p; Vint (Int.repr a); Vint (Int.repr b))
    SEP (coo_rep sh coo p)
 POST [ tvoid ]
   EX coo': coo_matrix Tdouble,
    PROP(coo_rows coo' = coo_rows coo; 
         coo_cols coo' = coo_cols coo;
         coo_entries coo' = 
          upd_Znth a (upd_Znth b (coo_entries coo) 
                        (Znth a (coo_entries coo))) 
                 (Znth b (coo_entries coo)))
    RETURN( )
    SEP (coo_rep sh coo' p).

Definition coo_quicksort_spec :=
 DECLARE _coo_quicksort
 WITH sh: share, coo: coo_matrix Tdouble, p: val, base: Z, n: Z
 PRE [ tptr t_coo, tuint, tuint ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo;
         0 <= base; base <= base+n <= Zlength (coo_entries coo))
    PARAMS( p; Vint (Int.repr base); Vint (Int.repr n))
    SEP (coo_rep sh coo p)
 POST [ tvoid ]
   EX coo': coo_matrix Tdouble,
    PROP(coo_matrix_equiv coo coo'; 
         sorted coord_le (sublist base (base+n) (coo_entries coo')))
    RETURN( )
    SEP (coo_rep sh coo' p).

Definition coo_count_spec :=
 DECLARE _coo_count
 WITH sh: share, coo: coo_matrix Tdouble, p: val
 PRE [ tptr t_coo ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo;
         sorted coord_le (coo_entries coo))
    PARAMS( p )
    SEP (coo_rep sh coo p)
 POST [ tuint ]
    PROP()
    RETURN( Vint (Int.repr (count_distinct (coo_entries coo))) )
    SEP (coo_rep sh coo p).

Definition t_csr := Tstruct _csr_matrix noattr.

Definition csr_rep' sh (csr: csr_matrix Tdouble) (v: val) (ci: val) (rp: val) (p: val) :=
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp.

Definition csr_rep (sh: share) (csr: csr_matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val,
  csr_rep' sh csr v ci rp p.

Definition csr_token' (csr: csr_matrix Tdouble) (p: val) : mpred :=
 EX v: val, EX ci: val, EX rp: val,
    csr_rep' Ews csr v ci rp p -*
    (csr_rep' Ews csr v ci rp p
     * (spec_malloc.malloc_token Ews t_csr p *
        spec_malloc.malloc_token Ews (tarray tdouble (Zlength (csr_vals csr))) v *
        spec_malloc.malloc_token Ews (tarray tuint (Zlength (csr_vals csr))) ci *
        spec_malloc.malloc_token Ews (tarray tuint (csr_rows csr + 1)) rp)).

Definition csr_token (m: matrix Tdouble) (p: val) : mpred :=
 EX (csr: csr_matrix Tdouble) (H: csr_to_matrix csr m), csr_token' csr p.

Definition coo_to_csr_matrix_spec :=
 DECLARE _coo_to_csr_matrix
 WITH sh: share, coo: coo_matrix Tdouble, p: val, gv: globals
 PRE [ tptr t_coo ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo)
    PARAMS( p )
    GLOBALS (gv)
    SEP (coo_rep sh coo p; mem_mgr gv)
 POST [ tptr t_csr ]
   EX coo': coo_matrix Tdouble, EX csr: csr_matrix Tdouble, EX m: matrix Tdouble, EX q: val,
    PROP(coo_matrix_equiv coo coo'; coo_to_matrix coo m; csr_to_matrix csr m)
    RETURN( q )
    SEP (coo_rep sh coo' p; csr_rep Ews csr q; csr_token m q; mem_mgr gv).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:Ctypes.type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition Build_CSR_ASI : funspecs := [ 
   surely_malloc_spec;
   coo_count_spec; swap_spec; coo_quicksort_spec; 
   add_to_coo_matrix_spec; coo_to_csr_matrix_spec ].


