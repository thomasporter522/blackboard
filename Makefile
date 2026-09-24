
build:
	dune build
	cp -r blackboard-vscode-extension ~/.vscode/extensions

file ?= "examples/ex.bb"

run: 
	dune build
	dune exec bin/main.exe $(file)