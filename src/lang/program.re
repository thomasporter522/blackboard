open Term
open Demo

type arg_chunk = (list(name), surface_tm)

type surface_signature = list((name, list(arg_chunk), surface_tm))
// type signature = list((name, tm))

type surface_program = 
    | Empty 
    | Assume(surface_signature, demo, surface_program)
    | Construct(surface_signature, demo, surface_program)
    | Prove(surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Assume(ctx, tm, demo, program)
    | Construct(ctx, tm, demo, program)
    | Prove(ctx, tm, demo, program)

// let rec signature_of_surface(c : ctx, s : surface_signature) : (ctx, signature) = switch(s) {
//     | [] => (c, [])
//     | [(x, ty, a),...s'] => {
//         let ty_elab = tm_of_surface(c, ty);
//         let c' = Cons(c, x, ty_elab, a);
//         let (c'', s'') = signature_of_surface(c', s');
//         (c'', [(x, ty_elab), ...s''])
//     }
// }

let rec form_strong_arrow(a : list(arg_chunk), ty : surface_tm) : surface_tm = switch(a) {
    | [] => ty 
    | [(xs, ty1), ... a'] => SurfaceArrow(Strong, xs, ty1, form_strong_arrow(a', ty))
}

let rec extend_context_surface_signature(c : ctx, s : surface_signature) : ctx = switch(s) {
    | [] => c
    | [(x, a, ty),...s'] => {
        let ty_elab = tm_of_surface(c, form_strong_arrow(a, ty));
        let c' = Cons(c, x, ty_elab);
        extend_context_surface_signature(c', s');
    }
}

let rec ty_arrow_of_surface_signature(c : ctx, s : surface_signature, depth : int) : tm = switch(s){
    | [] => Var(depth)
    | [(x, a, ty),...s'] => {
        let ty_elab = tm_of_surface(c, form_strong_arrow(a, ty));
        let c' = Cons(c, x, ty_elab);
        Arrow(Weak, x, ty_elab, ty_arrow_of_surface_signature(c', s', depth+1))
    }
}

let ty_of_surface_signature(c : ctx, s : surface_signature) : tm = {
    Arrow(Weak, "M", Prop, Arrow(Weak, "_", ty_arrow_of_surface_signature(Cons(c, "#M", Prop), s, 0), Var(1)))
}

let rec program_of_surface (c : ctx, p : surface_program) : program = switch(p) {
    | Empty => Empty 
    | Assume(s, d, p) => 
        let c' = extend_context_surface_signature(c, s);
        let ty = ty_of_surface_signature(c, s);
        Assume(c, ty, d, program_of_surface(c', p))
    | Construct(s, d, p) => 
        let c' = extend_context_surface_signature(c, s);
        let ty = ty_of_surface_signature(c, s);
        Construct(c, ty, d, program_of_surface(c', p))
    | Prove(a, d, p) => Prove(c, tm_of_surface(Empty, a), d, program_of_surface(c, p))
}

type program_check_report = list(report);

let rec check_program (p : program) : program_check_report = {
    switch(p) {
    | Empty => []
    | Assume(c, ty, d, p) => [check_demo_root(J(c, In(ty, Prop), Blue), d),... check_program(p)]
    | Construct(c, ty, d, p) => [check_demo_root(J(c, ty, Blue), d),... check_program(p)]
    | Prove(c, ty, d, p) => [check_demo_root(J(c, ty, Blue), d),... check_program(p)]
    }
}

let check_surface_program (p : surface_program) : program_check_report = {
    check_program(program_of_surface(Empty, p))
}