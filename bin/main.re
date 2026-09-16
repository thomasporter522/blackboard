open Blackboard.Core
open Blackboard.Demo
open Blackboard.Printing


let my_root = J(Empty, Arrow("A", Typ, Arrow("x", Var(0), Var(1))))
let my_demo = ArrowIntro(ArrowIntro(Hyp("x")))
print_endline(string_of_report(check_demo_root(my_demo, my_root)))