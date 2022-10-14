COQC = coqc
COQDEO=coqdep
VCFLOAT_LOC=../vcfloat/vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat 

all: _CoqProject specific_matrix_lemmas.vo infinity_norm_properties.vo float_model.vo lemmas.vo error_real.vo vcfloat_lemmas.vo  error_float.vo  

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

clean:
	rm -f *.vo *.vok *.vos *.glob 
