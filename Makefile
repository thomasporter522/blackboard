
build:
	dune build
	cp -r blackboard-vscode-extension ~/.vscode/extensions

file ?= "examples/ex.bb"

run: 
	make build
	dune exec bin/main.exe $(file)

runweb:
	make build
	cd blackboard-web && npm run dev
	
init:
	cd blackboard-web && npm install