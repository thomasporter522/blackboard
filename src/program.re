open Lang
open Demo

type surface_signature = list((name, surface_tm))
type signature = list((name, tm))

type surface_program = 
    | Empty 
    | Assume(surface_signature, demo, surface_program)
    | Construct(surface_signature, demo, surface_program)
    | Prove(surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Assume(ctx, signature, demo, program)
    | Construct(ctx, signature, demo, program)
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
    | Construct(s, d, p) => 
        let (c', s') = signature_of_surface(c, s);
        Construct(c, s', d, program_of_surface(c', p))
    | Prove(a, d, p) => Prove(c, tm_of_surface(Empty, a), d, program_of_surface(c, p))
}

type program_check_report = list(demo_check_report);

let swap01 (x : int) : int = switch(x) {
    | 0 => 1 
    | 1 => 0 
    | x => x
}
// d : type
// c : d0
// b : c0 d1,
// a : b0 c1 d2

// d, c, b, a, M |- M0
// d, c, b, M, a |- M1 (swap)
// d, c, b |- a : b0 c1 d2
// d, c, b, M |- a : b1 c2 d3 (bump)
// d, c, b, M |- (a : b1 c2 d3) -> M1

// d : type
// c : d0

// b, a, M |- M0
// b, M, a |- M1 (swap)
// b |- a : b0
// b, M |- a : b1 (bump)
// b, M |- (a : b1) -> M1
// M, b |- (a : b0) -> M2 (smartswap)


let rec ty_arrow_of_sig (s : signature, depth : int) : tm = switch(s) {
    | [] => Var(depth)
    | [(x, ty), ...s] => Arrow(x, varmap(ty, depth, x => x+1), ty_arrow_of_sig(s, depth+1))
}

// let ty_arrow_of_sig (_s : signature, _m : int) : tm = Typ

let ty_of_sig (s : signature) : tm = Arrow("M", Typ, Arrow("_", ty_arrow_of_sig(s, 0), Var(1)))

// let ty_of_sig (_s : signature) : tm = Typ

let rec check_program (p : program) : program_check_report = {
    switch(p) {
    | Empty => []
    | Assume(c, s, d, p) => [check_demo_root(J(c, In(ty_of_sig(s), Typ)), d),... check_program(p)]
    | Construct(c, s, d, p) => [check_demo_root(J(c, ty_of_sig(s)), d),... check_program(p)]
    | Prove(c, ty, d, p) => [check_demo_root(J(c, ty), d),... check_program(p)]
    }
}