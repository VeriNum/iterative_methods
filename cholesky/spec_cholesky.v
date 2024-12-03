Require Import VST.floyd.proofauto.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Import FPCore FPCompCert.
From Cholesky Require Import cholesky_model cholesky.
Require Import Cholesky.cholesky.
(*From libValidSDP Require cholesky_infnan.*)

Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog: funspecs := [sqrt_spec; sqrtf_spec].

Definition N : Z := proj1_sig (opaque_constant 1000).
Definition N_eq : N=1000 := proj2_sig (opaque_constant _).
Hint Rewrite N_eq : rep_lia.

Definition matrix := tarray (tarray tdouble N) N.
Definition matrixf := tarray (tarray tfloat N) N.

Definition cholesky_spec {NAN: Nans}:=
 DECLARE _cholesky
 WITH rsh: share, sh: share, n: Z, A: (Z -> Z -> ftype Tdouble), a: val, r: val
 PRE [ tuint , tptr (tarray tdouble N), tptr (tarray tdouble N) ]
    PROP (readable_share rsh; writable_share sh; 0 <= n <= N)
    PARAMS ( Vint (Int.repr n); a; r)
    SEP (data_at rsh matrix (lists_of_fun N (done_to_n (Vfloat oo float_of_ftype) n A)) a;
         data_at_ sh matrix r)
 POST [ tvoid ]
   EX R: Z -> Z -> ftype Tdouble,
    PROP (cholesky_jik_spec n A R)
    RETURN ()
    SEP (data_at rsh matrix (lists_of_fun N (done_to_n (Vfloat oo float_of_ftype) n A)) a;
         data_at sh matrix (lists_of_fun N (done_to_n (Vfloat oo float_of_ftype) n R)) r).

Definition choleskyf_spec {NAN: Nans}:=
 DECLARE _choleskyf
 WITH rsh: share, sh: share, n: Z, A: (Z -> Z -> ftype Tsingle), a: val, r: val
 PRE [ tuint , tptr (tarray tfloat N), tptr (tarray tfloat N) ]
    PROP (readable_share rsh; writable_share sh; 0 <= n <= N)
    PARAMS ( Vint (Int.repr n); a; r)
    SEP (data_at rsh matrixf (lists_of_fun N (done_to_n (Vsingle oo @float_of_ftype Tsingle _)  n A)) a;
         data_at_ sh matrixf r)
 POST [ tvoid ]
   EX R: Z -> Z -> ftype Tsingle,
    PROP (cholesky_jik_spec n A R)
    RETURN ()
    SEP (data_at rsh matrixf (lists_of_fun N (done_to_n (Vsingle oo @float_of_ftype Tsingle _)  n A)) a;
         data_at sh matrixf (lists_of_fun N (done_to_n (Vsingle oo @float_of_ftype Tsingle _)  n R)) r).

