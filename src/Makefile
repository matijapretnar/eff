# Configure the location of the following commands. The source ought to
# compile even if you do no have these commands.

UNAME=uname
GIT=git
DATE=date

# You should not touch anything below, unless you know what you are doing.

TARGET=eff
OCAMLBUILD=ocamlbuild -use-menhir -lib nums
TEST=../test.sh

.PHONY: version.ml

default: native

byte:	version.ml
	$(OCAMLBUILD) $(TARGET).byte
native: version.ml
	$(OCAMLBUILD) $(TARGET).native
debug:  version.ml
	$(OCAMLBUILD) $(TARGET).d.byte
profile: version.ml
	$(OCAMLBUILD) $(TARGET).p.native
conflicts:
	$(OCAMLBUILD) -yaccflags "--explain" parser.mli
	touch _build/parser.conflicts
	mv _build/parser.conflicts .

version.ml:
	export VERSION="`$(GIT) rev-parse HEAD`"; \
	export OS="`$(UNAME)`"; \
	export DATE="`$(DATE) +%Y-%m-%d`"; \
	echo "let changeset = \"$$VERSION\" ;; let os = \"$$OS\" ;; let date = \"$$DATE\"" > version.ml

# Run this to see if anything broke
test:
	$(TEST)

# Run this to see if anything broke and re-validate things that changes but
# are not broken.
vtest:
	$(TEST) -v

# Explain parser conflicts in the file parser.conflicts

# Clean up
clean:
	ocamlbuild -clean
	/bin/rm -f parser.conflicts

