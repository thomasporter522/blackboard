open Js_of_ocaml

let identity = (s: string) => s ++ s;
let () = Js.export("identity", identity);