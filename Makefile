
build:
	dune build
	cp -r blackboard-vscode-extension ~/.vscode/extensions

file ?= "examples/ex.bb"

run: 
	make build
	dune exec bin/main.exe $(file)

web:
	make build
	cp _build/default/bin/reason_to_js.bc.js blackboard-web/public/
	cd blackboard-web && npm run dev
	
init:
	cd blackboard-web && npm install