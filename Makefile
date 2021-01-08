default: format
	dune build

format:
	dune build @fmt --auto-promote

release: format
	dune build --profile release

clean:
	dune clean

test: default
	dune runtest

test_explicit: default
	dune runtest tests/explicit-effect-subtyping

install: release
	dune install

uninstall: release
	dune uninstall

.PHONY: default format release clean test test-validate install uninstall
