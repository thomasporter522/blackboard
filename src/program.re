open Core
open Demo

type surface_signature = list((name, surface_tm))
type signature = list((name, tm))

type surface_program = 
    | Empty 
    | Assume(surface_signature, demo, surface_program)
    | Prove(surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Assume(signature, demo, program)
    | Prove(tm, demo, program)

let rec signature_of_surface(c : ctx, s : surface_signature) : (ctx, signature) = switch(s) {
    | [] => (c, [])
    | [(x, ty),...s'] => {
        let ty_elab = tm_of_surface(c, ty);
        let c' = Cons(c, x, ty_elab);
        let (c'', s'') = signature_of_surface(c', s');
        (c'', [(x, ty_elab), ...s''])
    }
}

let rec program_of_surface (c : ctx, p : surface_program) : program = switch(p) {
    | Empty => Empty 
    | Assume(s, d, p) => 
        let (c', s') = signature_of_surface(c, s);
        Assume(s', d, program_of_surface(c', p))
    | Prove(a, d, p) => Prove(tm_of_surface(Empty, a), d, program_of_surface(c, p))
}

let check_program (p : program) = {
    switch(p) {
    | Prove(ty, d, Empty) => check_demo_root(J(Empty, ty), d)
    | _ => failwith("can't yet check compound program")
    }
}