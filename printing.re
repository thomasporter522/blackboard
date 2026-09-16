open Core

let string_of_report(r : demo_check_report) : string = {

}


let my_root = J(Empty, Arrow("A", Typ, Arrow("x", Var(0), Var(1))))
let my_demo = ArrowIntro(Hole)
print_endline(string_of_report(check_demo_root(my_demo, my_root)))