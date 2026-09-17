open Core
open Demo

type surface_program = 
    | Empty 
    | Prove(surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Prove(tm, demo, program)

let rec program_of_surface (p : surface_program) : program = switch(p) {
    | Empty => Empty 
    | Prove(a, d, p) => Prove(tm_of_surface(Empty, a), d, program_of_surface(p))
}

let check_program (p : program) = {
    switch(p) {
    | Prove(ty, d, Empty) => check_demo_root(J(Empty, ty), d)
    | _ => failwith("can't yet check compound program")
    }
}