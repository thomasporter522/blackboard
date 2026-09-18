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
    | Assume(ctx, signature, demo, program)
    | Prove(ctx, tm, demo, program)

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
        Assume(c, s', d, program_of_surface(c', p))
    | Prove(a, d, p) => Prove(c, tm_of_surface(Empty, a), d, program_of_surface(c, p))
}

type program_check_report = list(demo_check_report);

let rec ty_arrow_of_sig (s : signature, m : int) : tm = switch(s) {
    | [] => Var(m)
    | [(x, ty), ...s] => Arrow(x, shift(ty, 0), ty_arrow_of_sig(s, m+1))
}

// let ty_arrow_of_sig (_s : signature, _m : int) : tm = Typ

let ty_of_sig (s : signature) : tm = Arrow("M", Typ, Arrow("_", ty_arrow_of_sig(s, 0), Var(1)))

// let ty_of_sig (_s : signature) : tm = Typ

let rec check_program (p : program) : program_check_report = {
    switch(p) {
    | Empty => []
    | Assume(c, s, d, p) => [check_demo_root(J(c, In(ty_of_sig(s), Typ)), d),... check_program(p)]
    | Prove(c, ty, d, p) => [check_demo_root(J(c, ty), d),... check_program(p)]
    }
}