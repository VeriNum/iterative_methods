COQC = coqc
COQDEO=coqdep
VCFLOAT_LOC=../vcfloat/vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat 

target: _CoqProject lemmas.vo float_model.vo real_model.vo vcfloat_lemmas.vo inf_norm_properties.vo model_mat_lemmas.vo local_float_error.vo global_float_error.vo     
	

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

clean:
	rm -f *.vo *.vok *.vos *.glob 
