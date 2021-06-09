default: format
	dune build src/eff
.PHONY: default

format:
	dune build @fmt --auto-promote
.PHONY: format

release: format
	dune build --profile release
.PHONY: release

clean:
	dune clean
.PHONY: clean

test: default
	dune runtest
.PHONY: test

generate_benchmarks: 
	dune build @generate_benchmarks --auto-promote
.PHONY: generate_benchmark 

benchmark: 
	dune build @benchmark --auto-promote
.PHONY: benchmark 

graphs: 
	cd misc/code-generation-benchmarks/generate-graphs && dune build . --auto-promote && ./graphs.exe
.PHONY: graphs

install: release
	dune install
.PHONY: install

uninstall: release
	dune uninstall
.PHONY: uninstall
