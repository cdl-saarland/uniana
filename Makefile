EXTRA_DIR:=coqdocjs/extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(shell find . -name '*.v' -a ! -name 'X_*.v' -a ! -name '*\#*.v') #$(wildcard *.v */*.v */*/*.v)
VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

ifeq (,$(VS_IN_PROJ)) # if VS_IN_PROJ is empty, i.e. there are no *.v ressources listed in COQ_PROJ
VS_OTHER := $(VS) # we use all *.v files found by VS
else
VS := $(VS_IN_PROJ) # otw use the ressources listed in COQ_PROJ 
endif

.PHONY: clean all force cleancoqmake

all: html

uniana.tar: all
	rm -f *.vo */*.vo */*/*.vo
	rm -f *.glob */*.glob */*/*.glob 
	rm -f *.aux */*.aux */*/*.aux
	rm -f *~ */*~ */*/*~
	rm -f *\#* */*\#* */*/*\#*
	tar -czvf $@ Uniana.v Unchanged.v cfg _CoqProject external infra tcfg Unchanged.v util coqdocjs disj eval html Makefile README Uniana.v uniana.pdf

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@ # $@ calls 'clean' in the makefile COQMAKEFILE
	@$(MAKE) cleancoqmake

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html

cleancoqmake:
	@rm -f $(COQMAKEFILE)
	@rm -f $(COQMAKEFILE).conf # added by me

$(COQMAKEFILE): $(COQ_PROJ) $(VS)
	coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;
