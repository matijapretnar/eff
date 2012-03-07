##### Configuration

# Where to install eff files
LIBDIR=/usr/local/share/eff

# Where to link the eff executable from
BINDIR=/usr/local/bin

##### Do not touch below, unless you know what you are doing

# The main program (without the .ml extension)
TARGET=src/eff

# How to compile
OCAMLBUILD=ocamlbuild -use-menhir -lib nums

default: native

.PHONY: byte native debug profile install clean test vtest

byte:
	$(OCAMLBUILD) $(TARGET).byte

native:
	$(OCAMLBUILD) $(TARGET).native

debug:
	$(OCAMLBUILD) $(TARGET).d.byte

profile:
	$(OCAMLBUILD) $(TARGET).p.native

install: native
	/bin/mkdir -p $(LIBDIR)
	/bin/mkdir -p $(BINDIR)
	/bin/cp -f pervasives.eff $(LIBDIR)
	/usr/bin/sed 's|BASEDIR=.|BASEDIR="$(LIBDIR)"|' < eff > $(LIBDIR)/eff
	/bin/chmod +x $(LIBDIR)/eff
	if [ -f eff.native ] ; then /bin/cp -f eff.native $(LIBDIR) ; fi
	if [ -f eff.byte ] ; then /bin/cp -f eff.byte $(LIBDIR) ; fi
	/bin/ln -Fs $(LIBDIR)/eff $(BINDIR)

# Explain parser conflicts in the file parser.conflicts
conflicts:
	$(OCAMLBUILD) -yaccflags "--explain" src/parser.mli
	touch _build/parser.conflicts
	mv _build/parser.conflicts .

# "make test" to see if anything broke
test:
	cd tests ; \
	./test.sh

# "make vtest" to see if anything broke and ask for validation of possibly
# broken things.
vtest:
	cd tests ; \
	./test.sh -v

# Clean up
clean:
	ocamlbuild -clean
	/bin/rm -f parser.conflicts
