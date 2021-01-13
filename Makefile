default: format
	dune build || true

format:
	dune build @fmt --auto-promote

release: format
	dune build --profile release

clean:
	dune clean

.PHONY: test
test: generate_tests
	dune runtest

.PHONY: generate_tests 
generate_tests: 
	@ dune build @generate_tests --auto-promote || true

install: release
	dune install

uninstall: release
	dune uninstall

.PHONY: default format release clean test test-validate install uninstall
