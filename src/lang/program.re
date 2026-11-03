open Term
open Demo

type surface_program = 
    | SurfaceEmpty 
    | SurfaceAssume(range, bool, list(surface_tele_entry), demo, surface_program)
    | SurfaceConstruct(range, bool, list(surface_tele_entry), demo, surface_program)
    | SurfaceProve(range, bool, name, surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Assume(range, bool, ctx, tm, demo, program)
    | Construct(range, bool, ctx, tm, demo, program)
    | Prove(range, bool, ctx, tm, demo, program)

// let rec signature_of_surface(c : ctx, s : surface_signature) : (ctx, signature) = switch(s) {
//     | [] => (c, [])
//     | [(x, ty, a),...s'] => {
//         let ty_elab = tm_of_surface(c, ty);
//         let c' = Cons(c, x, ty_elab, a);
//         let (c'', s'') = signature_of_surface(c', s');
//         (c'', [(x, ty_elab), ...s''])
//     }
// }

type program_check_report = list(report);

let rec check_program (p : program) : program_check_report = {
    switch(p) {
    | Empty => []
    | Assume(r, tidy, c, ty, d, p) => [check_demo_root(J(c, In(ty, Prop)), d, r, tidy),... check_program(p)]
    | Construct(r, tidy, c, ty, d, p) => [check_demo_root(J(c, ty), d, r, tidy),... check_program(p)]
    | Prove(r, tidy, c, ty, d, p) => [check_demo_root(J(c, ty), d, r, tidy),... check_program(p)]
    }
}
