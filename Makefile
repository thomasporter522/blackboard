
build:
	dune build

file ?= "examples/ex.bb"

run: 
	dune build
	dune exec bin/main.exe $(file)