open Term
open Demo

type arg_chunk = (list(name), surface_tm)

type surface_signature = list((name, list(arg_chunk), surface_tm))
// type signature = list((name, tm))

type surface_program = 
    | SurfaceEmpty 
    | SurfaceAssume(range, surface_signature, demo, surface_program)
    | SurfaceConstruct(range, surface_signature, demo, surface_program)
    | SurfaceProve(range, surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Assume(range, ctx, tm, demo, program)
    | Construct(range, ctx, tm, demo, program)
    | Prove(range, ctx, tm, demo, program)

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

let rec extend_context_surface_signature(c : ctx, s : surface_signature) : (ctx, list(ranged_error)) = switch(s) {
    | [] => (c, [])
    | [(x, a, ty),...s'] => {
        let (ty_elab, es1) = tm_of_surface(c, form_strong_arrow(a, ty));
        let c' = Cons(c, x, ty_elab);
        let (c'', es2) = extend_context_surface_signature(c', s');
        (c'', es1 @ es2)
    }
}

let rec ty_arrow_of_surface_signature(c : ctx, s : surface_signature, depth : int) : tm = switch(s){
    | [] => Var(depth)
    | [(x, a, ty),...s'] => {
        let (ty_elab, _) = tm_of_surface(c, form_strong_arrow(a, ty));
        let c' = Cons(c, x, ty_elab);
        Arrow(Weak, x, ty_elab, ty_arrow_of_surface_signature(c', s', depth+1))
    }
}

let ty_of_surface_signature(c : ctx, s : surface_signature) : tm = {
    Arrow(Weak, "M", Prop, Arrow(Weak, "_", ty_arrow_of_surface_signature(Cons(c, "#M", Prop), s, 0), Var(1)))
}

let rec program_of_surface (c : ctx, p : surface_program) : (program, list(ranged_error)) = switch(p) {
    | SurfaceEmpty => (Empty, [])
    | SurfaceAssume(r, s, d, p) => 
        let (c', es1) = extend_context_surface_signature(c, s);
        let ty = ty_of_surface_signature(c, s);
        let (p', es2) = program_of_surface(c', p);
        (Assume(r, c, ty, d, p'), es1 @ es2)
    | SurfaceConstruct(r, s, d, p) => 
        let (c', es1) = extend_context_surface_signature(c, s);
        let ty = ty_of_surface_signature(c, s);
        let (p', es2) = program_of_surface(c', p);
        (Construct(r, c, ty, d, p'), es1 @ es2)
    | SurfaceProve(r, a, d, p) => 
        let (p', es1) = program_of_surface(c, p);
        let (t', es2) = tm_of_surface(Empty, a);
        (Prove(r, c, t', d, p'), es1 @ es2)
}

type program_check_report = list(report);

let rec check_program (p : program) : program_check_report = {
    switch(p) {
    | Empty => []
    | Assume(r, c, ty, d, p) => [check_demo_root(J(c, In(ty, Prop), Blue), d, r),... check_program(p)]
    | Construct(r, c, ty, d, p) => [check_demo_root(J(c, ty, Blue), d, r),... check_program(p)]
    | Prove(r, c, ty, d, p) => [check_demo_root(J(c, ty, Blue), d, r),... check_program(p)]
    }
}

let check_surface_program (p : surface_program) : program_check_report = {
    let (p', es) = program_of_surface(Empty, p);
    [{open_goals: [], errors: es, completes: []}] @ check_program(p')
}