EXTRA_DIR:=../coqdocjs/extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(wildcard *.v */*.v */*/*.v)
#$(shell find . -name '*.v' -a ! -name 'X_*.v' -a ! -name '*\#*.v')
VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

ifeq (,$(VS_IN_PROJ)) # if VS_IN_PROJ is empty, i.e. there are no *.v ressources listed in COQ_PROJ
VS_OTHER := $(VS) # we use all *.v files found by VS
else
VS := $(VS_IN_PROJ) # otw use the ressources listed in COQ_PROJ
endif

.PHONY: clean all force cleancoqmake

all:
	rm -fr html
	$(MAKE) html

uniana.tar: all
	mkdir uniana
	mkdir uniana/theories
	cp -r Uniana.v Unchanged.v cfg _CoqProject external infra tcfg Unchanged.v util disj eval Makefile Uniana.v uniana/theories
	cp -r ../coqdocjs ../README.md html uniana
	rm -f uniana/theories/*.vo uniana/theories/*/*.vo uniana/theories/*/*/*.vo
	rm -f uniana/theories/*.glob uniana/theories/*/*.glob uniana/theories/*/*/*.glob
	rm -f uniana/theories/*.aux uniana/theories/*/*.aux uniana/theories/*/*/*.aux
	rm -f uniana/theories/.*.aux uniana/theories/*/.*.aux uniana/theories/*/*/.*.aux
	rm -f uniana/theories/*~ uniana/theories/*/*~ uniana/theories/*/*/*~
	rm -f uniana/theories/*\#* uniana/theories/*/*\#* uniana/theories/*/*/*\#*
	rm -f $@
	bsdtar cfv $@ uniana/
	rm -r uniana
# TODO: automate removals

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@ # $@ calls 'clean' in the makefile COQMAKEFILE
	@$(MAKE) cleancoqmake

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html
# TODO: automatically only include "interesting files in toc"

cleancoqmake:
	@rm -f $(COQMAKEFILE)
	@rm -f $(COQMAKEFILE).conf # added by me

$(COQMAKEFILE): $(COQ_PROJ) $(VS)
	coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

#%: $(COQMAKEFILE) force
#	@$(MAKE) -f $(COQMAKEFILE) $@
force: clean
	@$(MAKE) all
