ACLOCAL_AMFLAGS = -I build-aux
bin_SCRIPTS = eff
eff_DATA = pervasives.eff eff-$(PACKAGE_VERSION)
EXTRA_DIST = build-aux/make-eff pervasives.eff tests examples src etc LICENSE.txt INSTALL.txt README.txt
effdir=$(datarootdir)/eff/$(PACKAGE_VERSION)

# The main program (without the .ml extension)
EFFTARGET=src/eff

# How to compile
EFFOCAMLBUILD=$(OCAMLBUILD) -use-menhir -lib nums

.PHONY: install-datahook test test-validate test-clean \
	eff.byte eff.native eff.d.byte eff.p.native

eff-$(PACKAGE_VERSION): eff.$(BUILDBEST)
	cd $(srcdir) && \
	cp eff.$(BUILDBEST) eff-$(PACKAGE_VERSION)

eff.byte:
	cd $(srcdir) && \
	$(EFFOCAMLBUILD) $(EFFTARGET).byte

eff.native:
	cd $(srcdir) && \
	$(EFFOCAMLBUILD) $(EFFTARGET).native

eff.d.byte:
	cd $(srcdir) && $(EFFOCAMLBUILD) $(EFFTARGET).d.byte

eff.p.native:
	cd $(srcdir) && $(EFFOCAMLBUILD) $(EFFTARGET).p.native

eff:
	sh $(srcdir)/build-aux/make-eff \
	   "$(effdir)/pervasives.eff" \
	   "$(effdir)/eff-$(PACKAGE_VERSION)" \
           "$(WRAPPER)"

install-data-hook:
	chmod a+x $(effdir)/eff-$(PACKAGE_VERSION)

# Explain parser conflicts in the file parser.conflicts
conflicts:
	cd $(srcdir) ; \
	$(EFFOCAMLBUILD) -yaccflags "--explain" src/parser.mli ; \
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
	rm -f eff eff-$(PACKAGE_VERSION) && \
	ocamlbuild -clean && rm -f parser.conflicts
