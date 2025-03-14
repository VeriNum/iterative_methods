Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse_model build_csr.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.


#[export] Declare Instance M: MallocAPD.

Definition coord_le {t} (a b : Z*Z*ftype t) : Prop :=
  fst (fst a) < fst (fst b) 
 \/ fst (fst a) = fst (fst b) /\ snd (fst a) < snd (fst b).

Inductive sorted {A} (le: A -> A -> Prop): list A -> Prop := 
| sorted_nil:
    sorted le nil
| sorted_1: forall x,
    sorted le (x::nil)
| sorted_cons: forall x y l,
     le x y -> sorted le (y::l) -> sorted le (x::y::l).

Lemma sorted_app:
  forall {A} {le: A->A->Prop} (TRANS: transitive A le)
    pivot al bl,
    sorted le al -> sorted le bl ->
    Forall (fun x => le x pivot) al ->
    Forall (le pivot) bl ->
    sorted le (al++bl).
Proof.
intros.
induction H.
simpl; auto.
simpl.
inv H1. inv H5.
inv H0.
constructor.
inv H2.
constructor.
apply TRANS with pivot; auto.
constructor.
inv H2.
constructor.
apply TRANS with pivot; auto.
constructor; auto.
simpl.
constructor; auto.
apply IHsorted.
inv H1; auto.
Qed.

Lemma sorted_app_e3:
  forall {A} {le: A->A->Prop} (TRANS: transitive A le)
    pivot al bl,
    sorted le (al++[pivot]++bl) ->
    sorted le al /\ sorted le bl /\ 
    Forall (fun x => le x pivot) al /\
    Forall (le pivot) bl.
Proof.
 intros.
 induction al.
 simpl in *.
 split. constructor.
 induction bl; inv  H. repeat constructor.
 spec IHbl. destruct bl; inv H4; constructor; auto. 
 eapply TRANS; eassumption.
 split3; auto. destruct IHbl as [? [? ?]]; constructor; auto.
 inv H. destruct al; inv H2. destruct al; inv H1.
 simpl in IHal. spec IHal; auto.
 destruct IHal as [_ [? [_ ?]]].
 split3. constructor. auto. split; auto.
 spec IHal; auto.
 destruct IHal as [? [? [? ?]]].
 split3; auto. constructor; auto.
 split; auto.
 constructor; auto.
 apply TRANS with a0; auto.
 inv H1; auto.
Qed.

Lemma Permutation_Zlength:
  forall {A} {al bl: list A}, Permutation al bl -> Zlength al = Zlength bl.
Proof.
intros. rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
Qed.


Definition t_csr := Tstruct _csr_matrix noattr.

Definition csr_rep (sh: share) (mval: matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val, EX csr,
  !! csr_rep_aux mval csr &&
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (matrix_rows mval)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (matrix_rows mval + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp.

Definition t_coo := Tstruct _coo_matrix noattr.

Definition coo_rep (sh: share) (coo: coo_matrix Tdouble) (p: val) : mpred :=
 EX (r c n maxn: Z) (rp cp vp : val), 
 !! (0 <= n <= maxn /\ maxn <= Int.max_signed /\ 0 <= r <= Int.max_signed /\
       0 <= c <= Int.max_signed /\ coo_matrix_wellformed coo) &&
  data_at sh t_coo (rp, (cp, (vp, (Vint (Int.repr n), (Vint (Int.repr maxn), 
                     (Vint (Int.repr r), (Vint (Int.repr c)))))))) p *
  data_at sh (tarray tint maxn)
    (map (fun e => Vint (Int.repr (fst (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-n)) rp *
  data_at sh (tarray tint maxn)
    (map (fun e => Vint (Int.repr (snd (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-n)) cp *
  data_at sh (tarray tint maxn)
    (map (fun e => Vfloat (snd e)) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-n)) vp.

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
 POST [ tdouble ]
   EX coo': coo_matrix Tdouble, EX m: matrix Tdouble, EX q: val,
    PROP(coo_matrix_equiv coo coo'; coo_to_matrix coo m)
    RETURN( q )
    SEP (coo_rep sh coo' p; csr_rep Ews m q).


Definition coo_to_csr_matrix_spec :=
 DECLARE _coo_to_csr_matrix
 WITH sh: share, coo: coo_matrix Tdouble, p: val, gv: globals
 PRE [ tptr t_coo ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo)
    PARAMS( p )
    GLOBALS (gv)
    SEP (coo_rep sh coo p; mem_mgr gv)
 POST [ tdouble ]
   EX coo': coo_matrix Tdouble, EX m: matrix Tdouble, EX q: val,
    PROP(coo_matrix_equiv coo coo'; coo_to_matrix coo m)
    RETURN( q )
    SEP (coo_rep sh coo' p; csr_rep Ews m q; mem_mgr gv).



Definition Build_CSR_ASI : funspecs := [ 
   coo_to_csr_matrix_spec ].


