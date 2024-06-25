all: theory
.PHONY: all

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
.PHONY: clean

install: CoqMakefile
	+@make -f CoqMakefile install
.PHONY: install

uninstall: CoqMakefile
	+@make -f CoqMakefile uninstall
.PHONY: uninstall

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
force: ;
all: theory

# Do not forward these files
Makefile _CoqProject: ;

html-clean:
	rm -rf docs
	rm -rf hacspec
	rm -rf ssprove

html-hacspec:
	rm -rf hacspec
	cp -r ${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/Hacspec hacspec
	cd hacspec && \
	mkdir docs && \
	coqdoc --html --interpolate --parse-comments \
		--toc \
		--external mathcomp https://math-comp.github.io/htmldoc_2_1_0/ \
		-R . Hacspec \
		-d docs `find . -name "*.v" ! -wholename "./_opam/*"`

html-ssprove:
	rm -rf ssprove
	mkdir ssprove
	cp -r ${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/Crypt ssprove/crypt
	cp -r ${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/Mon ssprove/mon
	cp -r ${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/Relational ssprove/relational
	cd ssprove && \
	mkdir docs && \
	coqdoc --html --interpolate --parse-comments \
		--toc \
		--external mathcomp https://math-comp.github.io/htmldoc_2_1_0/ \
		-R crypt Crypt \
		-R mon Mon \
		-R relational Relational \
		-d docs `find . -name "*.v" ! -wholename "./_opam/*"`

html: all html-hacspec html-ssprove
	rm -rf docs
	mkdir docs
	coqdoc --html --interpolate --parse-comments \
		--with-header extra/header.html --with-footer extra/footer.html \
		--toc \
		--external ConCert https://au-cobra.github.io/ConCert/ \
		--external mathcomp https://math-comp.github.io/htmldoc_2_1_0/ \
		--external Hacspec https://au-cobra.github.io/OVN/hacspec/ \
		--external Crypt https://au-cobra.github.io/OVN/ssprove/ \
		--external Mon https://au-cobra.github.io/OVN/ssprove/ \
		--external Relational https://au-cobra.github.io/OVN/ssprove/ \
		-R theories OVN \
		-d docs `find . -type f \( -wholename "*theories/*" \) -name "*.v" ! -wholename "./_opam/*"`
	cp extra/resources/coqdocjs/*.js docs
	cp extra/resources/coqdocjs/*.css docs
	cp extra/resources/toc/*.js docs
	cp extra/resources/toc/*.css docs
	mv hacspec/docs docs/hacspec
	rm -rf hacspec
	mv ssprove/docs docs/ssprove
	rm -rf ssprove
.PHONY: html