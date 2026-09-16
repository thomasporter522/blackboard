open Core
open Demo

type alpha_tm = 
    | Typ 
    | In(alpha_tm, alpha_tm)
    | Arrow(name, alpha_tm, alpha_tm)
    | Var(name)
    | Ap(alpha_tm, alpha_tm);

type alpha_program = 
    | Empty 
    | Prove(alpha_tm, demo, alpha_program)

type program = 
    | Empty 
    | Prove(tm, demo, program)

let var_of_alpha (c : list(name), x : name) : int = Option.get(List.find_index(y => y == x, c));

let rec tm_of_alpha (c : list(name), t : alpha_tm) : tm = switch(t) {
    | Typ => Typ
    | In(t1, t2) => In(tm_of_alpha(c, t1),tm_of_alpha(c, t2))
    | Arrow(x, t1, t2) => Arrow(x, tm_of_alpha(c, t1), tm_of_alpha([x, ...c], t2))
    | Var(x) => Var(var_of_alpha(c, x))
    | Ap(t1, t2) => Ap(tm_of_alpha(c, t1),tm_of_alpha(c, t2));
}

let rec program_of_alpha (p : alpha_program) : program = switch(p) {
    | Empty => Empty 
    | Prove(a, d, p) => Prove(tm_of_alpha([], a), d, program_of_alpha(p))
}

let rec check_program (p : program) = {
    switch(p) {
    | Prove(ty, d, Empty) => check_demo_root(J(Empty, ty), d)
    | _ => failwith("can't yet check compound program")
    }
}