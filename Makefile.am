ACLOCAL_AMFLAGS = -I build-aux
bin_PROGRAMS = eff
eff_SOURCES =
eff_DATA = pervasives.eff
EXTRA_DIST = pervasives.eff tests examples src etc LICENSE.txt INSTALL.txt README.txt
effdir=$(datarootdir)/eff

# The main program (without the .ml extension)
EFFTARGET=src/eff

# How to compile
EFFOCAMLBUILD=$(OCAMLBUILD) -use-menhir -lib unix

.PHONY: test test-validate test-clean \
	eff.byte eff.native eff.d.byte eff.p.native

eff: eff.$(BUILDBEST)
	cd $(srcdir) && \
	cp eff.$(BUILDBEST) eff

eff.byte: src/version.ml
	cd $(srcdir) && \
	$(EFFOCAMLBUILD) $(EFFTARGET).byte

eff.native: src/version.ml
	cd $(srcdir) && \
	$(EFFOCAMLBUILD) $(EFFTARGET).native

eff.d.byte: src/version.ml
	cd $(srcdir) && $(EFFOCAMLBUILD) $(EFFTARGET).d.byte

eff.p.native: src/version.ml
	cd $(srcdir) && $(EFFOCAMLBUILD) $(EFFTARGET).p.native

src/version.ml:
	echo "let version=\"$(PACKAGE_VERSION)\";; let effdir=\"$(effdir)\";;" > src/version.ml

# Explain parser conflicts in the file parser.conflicts
conflicts:
	cd $(srcdir); \
	$(EFFOCAMLBUILD) -yaccflags "--explain" src/parser.mli; \
	if [ -f $(srcdir)/_build/src/parser.conflicts ]; \
	then \
		mv -f $(srcdir)/_build/src/parser.conflicts .; \
	fi

# "make test" to see if anything broke
test: eff.$(BUILDBEST)
	cd $(srcdir)/tests && sh ./test.sh

# "make test-validate" to see if anything broke and ask for validation of possibly
# broken things.
test-validate:
	cd $(srcdir)/tests && sh ./test.sh -v

# Clean up tests
test-clean:
	cd $(srcdir) && rm -f tests/*.out tests/*/*.out

clean: test-clean
	cd $(srcdir) && \
	rm -f eff eff-$(PACKAGE_VERSION) src/version.ml && \
	ocamlbuild -clean && rm -f parser.conflicts
