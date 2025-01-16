Require Import vcfloat.FPStdLib.

Definition BFMA {NAN: FPCore.Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE.

