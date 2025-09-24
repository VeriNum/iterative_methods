Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse_model build_csr2 distinct.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[export] Declare Instance M: MallocAPD.

Check data_at.

Compute reptype (Tarray (Tstruct  _rowcol noattr) 10 noattr).

Print coo_matrix_wellformed.
Print int.

Definition intpair_to_valpair (a : int * int) : val * val :=
  match a with 
  | (x, y) => (Vint x, Vint y)
  end.

Definition intpair_to_Zpair (a : int * int) : Z * Z :=
  match a with 
  | (x, y) => (Int.intval x, Int.intval y)
  end.

Definition swap_spec :=
 DECLARE _swap
 WITH sh: share, coog: list (int * int), p: val, a: Z, b: Z
 PRE [ tptr (Tstruct _rowcol noattr), tuint, tuint ]
    PROP(writable_share sh;
         (* coo_matrix_wellformed coo; *)
         0 <= a < Zlength coog;
         0 <= b < Zlength coog)
    PARAMS( p; Vint (Int.repr a); Vint (Int.repr b))
    SEP (data_at sh (Tarray (Tstruct  _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog) p)
 POST [ tvoid ]
    PROP ()
    RETURN( )
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair (upd_Znth a (upd_Znth b coog (Znth a coog)) (Znth b coog))) p).

(* compare with the one in the repo that's verified *)
Definition coo_quicksort_spec :=
 DECLARE _coo_quicksort
 WITH sh: share, coog: list (int * int), p: val, base: Z, n: Z
 PRE [ tptr (Tstruct _rowcol noattr), tuint, tuint ]
    PROP(writable_share sh;
         (* coo_matrix_wellformed coo; *)
         0 <= base; base <= base+n <= Zlength coog)
    PARAMS( p; Vint (Int.repr base); Vint (Int.repr n))
    SEP (data_at sh (Tarray (Tstruct  _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog) p)
 POST [ tvoid ]
   EX coog': list (int * int),
    PROP(Permutation coog coog'; 
         sorted coord2_le (map intpair_to_Zpair (sublist base (base+n) coog')))
    RETURN( )
    SEP (data_at sh (Tarray (Tstruct  _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog') p).

Definition coo_count_spec :=
 DECLARE _coo_count
 WITH sh: share, coog: list (int * int), p: val
 PRE [ tptr (Tstruct _rowcol noattr) ]
    PROP(writable_share sh;
         (* coo_matrix_wellformed coo; *)
         sorted coord2_le (map intpair_to_Zpair coog))
    PARAMS( p )
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog) p)
 POST [ tuint ]
    PROP()
    RETURN( Vint (Int.repr (count_distinct (map intpair_to_Zpair coog))) )
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog) p).

Definition start_coo_shell_spec :=
  DECLARE _start_coo_shell
  WITH sh : share, n : int 
  PRE [tuint]
    PROP ()
    PARAMS (Vint n)
    SEP ()
  POST [tptr (Tstruct _rowcol noattr)]
    EX p : val,
    PROP ()
    RETURN (p)
    SEP (data_at_ sh (Tarray (Tstruct _rowcol noattr) (Int.intval n) noattr) p)
    .

Definition add_to_coo_shell_spec :=
  DECLARE _add_to_coo_shell 
  WITH sh : share, coog : list (int * int), p : val, r : int, c : int, n : Z
  PRE [tptr (Tstruct _rowcol noattr), tuint, tuint, tuint]
    PROP ()
    PARAMS (p)
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) n noattr) (map intpair_to_valpair coog ++ Zrepeat (Vundef, Vundef) (n - Zlength coog)) p)
  POST [tvoid]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) 
    (map intpair_to_valpair coog ++ [intpair_to_valpair (r, c)] ++ (Zrepeat (Vundef, Vundef) (n - Zlength coog - 1))) p ).



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

(* Just copied here so that I don't have to compile everything *)
Definition coog_upto (i : Z) (coog : coog_matrix) :=
  Build_coog_matrix (coog_rows coog) (coog_cols coog) (sublist 0 i (coog_entries coog)).

Definition cd_upto_coog (i : Z) (coog : coog_matrix) : Z :=
  count_distinct (sublist 0 i (coog_entries coog)).

Definition entries_correspond_coog {t} (coog : coog_matrix) (csr : csr_matrix t) :=
  forall h,
  0 <= h < Zlength (coog_entries coog) ->
  let '(r, c) := Znth h (coog_entries coog) in 
  let k := cd_upto_coog (h + 1) coog - 1 in 
    Znth r (csr_row_ptr csr) <= k < Znth (r + 1) (csr_row_ptr csr) /\
    Znth k (csr_col_ind csr) = c.

Definition no_extra_zeros_coog {t} (coog : coog_matrix) (csr : csr_matrix t) :=
  forall r k, 0 <= r < coog_rows coog ->
    Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) ->
    let c := Znth k (csr_col_ind csr) in 
    In (r, c) (coog_entries coog).

Inductive coog_csr {t} (coog : coog_matrix) (csr : csr_matrix t) : Prop :=
  build_coog_csr : forall 
    (coog_csr_rows : coog_rows coog = csr_rows csr)
    (coog_csr_cols : coog_cols coog = csr_cols csr)
    (coog_csr_vals : Zlength (csr_vals csr) = count_distinct (coog_entries coog))
    (coog_csr_entries : entries_correspond_coog coog csr)
    (coog_csr_zeros : no_extra_zeros_coog coog csr),
    coog_csr coog csr.
(* End of copied code *)

Definition coo_shell_to_csr_shell_spec :=
  DECLARE _coo_shell_to_csr_shell
  WITH sh : share, coog : list (int * int), p : val, rows : int, cols : int, gv : globals
  PRE [tptr (Tstruct _rowcol noattr), tuint, tuint, tuint]
    PROP (  )
    PARAMS (p; (Vint (Int.repr (Zlength coog))); (Vint rows); (Vint cols))
    GLOBALS (gv) 
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog) p; mem_mgr gv)
  POST [tptr (Tstruct _csr_matrix noattr)]
    EX coog' : list (int * int), 
    EX csr : csr_matrix Tdouble,
    EX q : val,
    PROP (Permutation coog coog'; 
      coog_csr (Build_coog_matrix (Int.intval rows) (Int.intval cols) (map intpair_to_Zpair coog)) csr)
    RETURN (q)
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map intpair_to_valpair coog') p;
      csr_rep Ews csr q;
      mem_mgr gv).