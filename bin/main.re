
open Blackboard.Printing
open Blackboard.Parse
open Blackboard.Program


// let my_root = J(Empty, Arrow("A", Typ, Arrow("x", Var(0), Var(1))))
// let my_demo = ArrowIntro(ArrowIntro(Hyp("x")))
// // let my_demo = ArrowIntro(ArrowIntro(InForm(Typ, Hole, Hole)))
// // let my_demo = ArrowIntro(ArrowIntro(Hole))
// // let my_demo = ArrowIntro(ArrowIntro(Obvious))
// print_endline(string_of_report(check_demo_root(my_root, my_demo)))

let filename = Array.length(Sys.argv) > 1 ? Sys.argv[1] : "examples/ex.bb"

print_endline(string_of_report(check_program(program_of_file(filename))))