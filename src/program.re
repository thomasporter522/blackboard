open Core
open Demo

type surface_tm = 
    | Typ 
    | In(surface_tm, surface_tm)
    | Arrow(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | Var(name)
    | Ap(surface_tm, surface_tm);

type surface_demo = 
    | Hole
    | Hyp(name)
    | InForm(tm, surface_demo, surface_demo)
    | InElim(tm, surface_demo)
    | Have(name, tm, surface_demo, surface_demo)
    | Suffices(name, tm, surface_demo, surface_demo)
    | TypForm
    | ArrowForm(surface_demo, surface_demo)
    | Ap(name, tm, tm, surface_demo, surface_demo)
    | Given(name, surface_tm, surface_demo, surface_demo)
    | Obvious

type surface_program = 
    | Empty 
    | Prove(surface_tm, surface_demo, surface_program)

type program = 
    | Empty 
    | Prove(tm, demo, program)

let var_of_surface (c : list(name), x : name) : int = Option.get(List.find_index(y => y == x, c));

let rec tm_of_surface (c : list(name), t : surface_tm) : tm = switch(t) {
    | Typ => Typ
    | In(t1, t2) => In(tm_of_surface(c, t1),tm_of_surface(c, t2))
    | Arrow([x,...xs], t1, t2) => Arrow(x, tm_of_surface(c, t1), tm_of_surface([x, ...c], Arrow(xs, t1, t2)))
    | Arrow([], _, t2) => tm_of_surface(c, t2)
    | SimpleArrow(t1, t2) => Arrow("_", tm_of_surface(c, t1), tm_of_surface(["_", ...c], t2))
    | Var(x) => Var(var_of_surface(c, x))
    | Ap(t1, t2) => Ap(tm_of_surface(c, t1),tm_of_surface(c, t2));
}

let rec demo_of_surface (d : surface_demo) : demo = switch(d) {
    | Hole => Hole
    | Hyp(x) => Hyp(x)
    | InForm(a, d1, d2) => InForm(a, demo_of_surface(d1), d2)
    | InElim(a, d) => InElim(a, d)
    | Have(x, a, d1, d2) => Have(x, a, demo_of_surface(d1), d2) 
    | Suffices(x, a, d1, d2) => Suffices(x, a, demo_of_surface(d1), d2)
    | TypForm => TypForm
    | ArrowForm(d1, d2) => ArrowForm(demo_of_surface(d1), d2)
    | Ap(x, a1, a2, d1, d2) => Ap(x, a1, a2, demo_of_surface(d1), d2)
    | Given(x, a, d1, d2) => Given(x, tm_of_surface(a), demo_of_surface(d1), d2)
    | Obvious => Obvious
}

let rec program_of_surface (p : surface_program) : program = switch(p) {
    | Empty => Empty 
    | Prove(a, d, p) => Prove(tm_of_surface([], a), d, program_of_surface(p))
}

let check_program (p : program) = {
    switch(p) {
    | Prove(ty, d, Empty) => check_demo_root(J(Empty, ty), d)
    | _ => failwith("can't yet check compound program")
    }
}