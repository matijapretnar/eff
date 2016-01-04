# OASIS_START
# DO NOT EDIT (digest: 4d265c1dbe34db850ba8f3cfa7396db0)

SETUP = ocaml setup.ml

build: setup.data
	$(SETUP) -build $(BUILDFLAGS)

doc: setup.data build
	$(SETUP) -doc $(DOCFLAGS)

all:
	$(SETUP) -all $(ALLFLAGS)

install: setup.data
	$(SETUP) -install $(INSTALLFLAGS)

uninstall: setup.data
	$(SETUP) -uninstall $(UNINSTALLFLAGS)

reinstall: setup.data
	$(SETUP) -reinstall $(REINSTALLFLAGS)

clean:
	$(SETUP) -clean $(CLEANFLAGS)

distclean:
	$(SETUP) -distclean $(DISTCLEANFLAGS)

setup.data:
	$(SETUP) -configure $(CONFIGUREFLAGS)

configure:
	$(SETUP) -configure $(CONFIGUREFLAGS)

.PHONY: build doc all install uninstall reinstall clean distclean configure

# OASIS_STOP

eff: setup.data
	$(SETUP) -build $(BUILDFLAGS)

# "make test" to see if anything broke
test: eff
	cd tests && sh ./test.sh

# "make test-validate" to see if anything broke
# and ask for validation of possibly broken things.
test-validate: eff
	cd tests && sh ./test.sh -v

.PHONY: test test-validate
