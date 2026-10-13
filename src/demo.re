open Lang
// open Lang_printing
open Deriv.PartialDerivation
open Deriv

type surface_tm = 
    | SurfaceProp 
    | SurfaceTyp 
    | SurfaceIn(surface_tm, surface_tm)
    | SurfaceArrow(list(name), surface_tm, surface_tm)
    | SurfaceLambda(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | SurfaceVar(name)
    | SurfaceStrictAp(surface_tm, surface_tm)
    | SurfaceLaxAp(surface_tm, surface_tm);

type schema = 
    | Definition

type tactic = 
    | Check
    | Direct
    | GivenAll
    | Schema(schema)

type demo = 
    | Hole
    | HypProp(name)
    | ElabHypProp(int)
    | HypTyp(name)
    | InForm(tm, demo, demo)
    | Claim(name, surface_tm, demo, demo)
    | Suffices(name, surface_tm, demo, demo)
    | PropForm
    | TypForm
    | PropArrowForm(name, demo, demo)
    | TypArrowForm(name, demo, demo)
    // | ArrowElim(demo)
    | ApTyp(name, surface_tm, surface_tm, demo, demo)
    | ElabApTyp(name, tm, tm, demo, demo)
    | At(demo, surface_tm, demo)
    | ElabAt(demo, tm, demo)
    | Given(name, surface_tm, demo, demo)
    | ElabGiven(name, tm, demo, demo)
    | Use(demo, demo)
    | Obvious
    | Tactic(tactic, list(demo))

and tm_or_demo = 
    | Tm(surface_tm)
    | Demo(demo)

type report = {
    open_goals : list(judgment),
    errors : list(error)
}

let mk_report (open_goals : list(judgment), errors : list(string)) : report = {
    open_goals, errors
}

let pure_report : report = mk_report([], [])

let merge_reports(r1 : report, r2 : report) : report = {
    open_goals : r1.open_goals @ r2.open_goals,
    errors : r1.errors @ r2.errors
}

let rec merge_report_list(rs : list(report)) : report = switch(rs){
    | [] => pure_report
    | [h, ...t] => merge_reports(h, merge_report_list(t))
}

type demo_result = (t, report)

let dry(s : t, x : result(t, error)) : demo_result = switch(x) {
    | Ok(s') => (s', pure_report)
    | Error(e) => (Result.get_ok(skip(s)), mk_report([], [e]))
}

let undry(x : demo_result) : result(t, error) =
    if (snd(x).errors == []) { Ok(fst(x)) } else { Error("Errors:\n" ++ String.concat("\n", snd(x).errors ) )}

let (let-?) = (x: demo_result, f: list(error) => demo_result): demo_result =>
  if(snd(x).errors == []) { x } else { f(snd(x).errors) }

let (let-+) = (x: demo_result, f: t => demo_result): demo_result =>
  if(snd(x).errors == []) { f(fst(x)) } else { x }

let (let-*) = (x: demo_result, f: t => demo_result): demo_result => {
  let (s, r) = f(fst(x));
  (s, merge_reports(snd(x), r))
}

let skip_and_error(s : t, e : error) : (t, report) {
    let s' = Result.get_ok(skip(s));
    (s', mk_report([], [e]))
}

let attempt_option(v : result('a, error), f : 'a => (t, report), backup : (t, report)) : (t, report) = {
    switch(v) {
    | Ok(v) => f(v)
    | Error(_) => backup
    }
}

let attempt(s : t, v : result('a, error), f : 'a => (t, report)) : (t, report) = {
    switch(v) {
    | Ok(v) => f(v)
    | Error(e) => skip_and_error(s, e)
    }
}


let rec var_of_surface (c : ctx, x : name) : int = switch(c) {
    | Cons(_, y, _, _) when x == y => 0 
    | Cons(c, _, _, _) => 1+var_of_surface(c, x)
    | Empty => failwith("unbound variable: " ++ x)
}

let rec tm_of_surface (c : ctx, t : surface_tm) : tm = switch(t) {
    | SurfaceProp => Prop
    | SurfaceTyp => Typ
    | SurfaceIn(t1, t2) => In(tm_of_surface(c, t1),tm_of_surface(c, t2))
    | SurfaceArrow([x,...xs], t1, t2) => Arrow(x, tm_of_surface(c, t1), tm_of_surface(Cons(c, x, tm_of_surface(c, t1), Typ), SurfaceArrow(xs, t1, t2)))
    | SurfaceArrow([], _, t2) => tm_of_surface(c, t2)
    | SurfaceLambda([x,...xs], t1, t2) => Lam(x, tm_of_surface(c, t1), tm_of_surface(Cons(c, x, tm_of_surface(c, t1), Typ), SurfaceLambda(xs, t1, t2)))
    | SurfaceLambda([], _, t2) => tm_of_surface(c, t2)
    | SimpleArrow(t1, t2) => Arrow("_", tm_of_surface(c, t1), tm_of_surface(Cons(c, "_", tm_of_surface(c, t1), Typ), t2))
    | SurfaceStrictAp(t1, t2) => Ap(Strict, tm_of_surface(c, t1),tm_of_surface(c, t2));
    | SurfaceVar(x) => Var(var_of_surface(c, x))
    | SurfaceLaxAp(t1, t2) => Ap(Lax, tm_of_surface(c, t1),tm_of_surface(c, t2));
}

let rec find_assumption(c : ctx, ty : tm, n : int) : result (int, error) = {
    try {
        if (equiv(ty, get_lookup_index(c, n, Prop))) { Ok(n) } else { find_assumption(c, ty, n+1) }
    } {
       | _ => Error("can't find assumption")
    }
}


// inverse of wknvar(n, _)
let invert_wknvar(n : int, m : int) : result(int, error) = {
    if (n == m) { Error("unstrengthenable var") } else 
    if (n > m) { Ok(m) } else { Ok(m-1) }
}

// inverse of wkn(n, _)
let rec invert_wkn(n : int, a : tm) : result(tm, error) = switch(a) {
    | Prop => Ok(Prop)
    | Typ => Ok(Typ)
    | In(a, ty) => {
        let* a' = invert_wkn(n, a);
        let* ty' = invert_wkn(n, ty);
        Ok(In(a', ty'))
    }
    | Arrow(y, ty1, ty2) => {
        let* ty1' = invert_wkn(n, ty1);
        let* ty2' = invert_wkn(n+1, ty2);
        Ok(Arrow(y, ty1', ty2'))
    }
    | Lam(y, ty, a) => {
        let* ty' = invert_wkn(n, ty);
        let* a' = invert_wkn(n+1, a);
        Ok(Lam(y, ty', a'))
    }
    | Var(y) => {
        let* y' = invert_wknvar(n, y);
        Ok(Var(y'))
    }
    | Ap(st, a1, a2) => {
        let* a1' = invert_wkn(n, a1);
        let* a2' = invert_wkn(n, a2);
        Ok(Ap(st, a1', a2'))
    } 
}

// inverse of wk(_)
let invert_wk(a : tm) : result(tm, error) = invert_wkn(0, a)


let rec infer_arrow_typ_of_ap(c, hd_ty: tm, tds: list((surface_tm, demo))) : result((name, tm, tm), error) = {
    switch(tds) {
    | [] => switch(hd_ty) {
        | Arrow(x, a, b) => Ok((x, a, b))
        | _ => Error("head is not of arrow type")
        }
    | [(a, _), ...other_tds] => {
        Result.bind(infer_arrow_typ_of_ap(c, hd_ty, other_tds), f => {
            let (_, _, ty_b) = f;
            let elab_a = tm_of_surface(c, a);
            switch(subst(elab_a, ty_b)) {
            | Arrow(x, a, b) => Ok((x, a, b))
            | _ => Error("constituent is not of arrow type")
            }
        })
    }
    }
}

// infers the type proven by a demo in a context
let rec infer_proven_ty(c : ctx, d : demo) : result(tm, error) = switch(d) {
    | HypProp(x) => Result.bind(index_of_name(c, x), n => infer_proven_ty(c, ElabHypProp(n)))
    | ElabHypProp(n) => lookup_index_prop(c, n)
    | At(d1, a, d2) => {
        let elab_a = tm_of_surface(c, a);
        infer_proven_ty(c, ElabAt(d1, elab_a, d2))
    }
    | ElabAt(d, a, _) => {
        Result.bind(infer_proven_ty(c, d), inferred_ty => switch(inferred_ty) {
        | Arrow(_, _, ty_b) => Ok(subst(a, ty_b))
        | _ => Error("ap of non-arrow")
        })
    }
    | Use(d1, _) => {
        let* d1_proves = infer_proven_ty(c, d1);
        switch(d1_proves) {
        | Arrow(_, _, ty_b) => invert_wk(ty_b)
        | _ => Error("use of non-arrow or non-simple arrow")
        }
    }
    | _ => Error("cannot infer what it proves") // todo: make this message better
}

// infers the type of a term in a context
let rec infer_typ(c : ctx, a : tm) : result(tm, error) = switch(a) {
    | Prop => Ok(Typ)
    | Typ => Ok(Typ)
    | In(_) => Ok(Typ)
    | Arrow(x, ty1, ty2) => 
        let* ty1_assumption : assumption = switch(infer_typ(c, ty1)) {
            | Ok(Prop) => Ok(Prop)
            | Ok(Typ) => Ok(Typ)
            | _ => Error("domain is not a prop or type")
        };
        let* ty2_typ = infer_typ(Cons(c, x, ty1, ty1_assumption), ty2);
        Ok(ty2_typ)
    | Lam(x, ty, b) => 
        let* ty_body = infer_typ(Cons(c, x, ty, Typ), b);
        Ok(Arrow(x, ty, ty_body))
    // | Unlam(_, f) => switch(c) {
    //     | Empty => Error("Unlambda has no type in the empty context")
    //     | Cons(c', _, _) => switch(infer_typ(c', f)) {
    //         | Ok(Arrow(_, _, ty_b)) => Ok(ty_b)
    //         | Ok(_) => Error("Unlambda body does not have arrow type")
    //         | Error(e) => Error(e)
    //         }   
    //     }
    | Var(x) => lookup_index_typ(c, x)
    | Ap(_, a1, a2) => switch(infer_typ(c, a1)) {
        | Ok(Arrow(_, _, ty2)) => Ok(subst(a2, ty2))
        | Ok(_) => Error("Applied term does not have arrow type")
        | Error(e) => Error(e)
    }
}

let assumed(s : t) : result (t, error) = {
    let (c, ty_goal, _) = tuple_of_judgment(Result.get_ok(focused(s)));
    let* x = find_assumption(c, ty_goal, 0);
    hyp_prop(s, x)
}

// if the focus of [s] is c, x : A |- T, refines to goal c |- T' where wk(T') = T
let weaken_goal(s : t) : result(t, error) = {
    let (_, ty, _) = goal_tuple(s);
    let* ty_inv_wk = invert_wk(ty);
    weaken(s, ty_inv_wk)
}

// // if the focus of [s] is c |- B[a/x], refines to goals a : A and (x : A) -> B
// // assumes (x : A) -> B is well-typed in c
// let forall_elim(s : t, x : name, ty_a : tm, ty_b : tm, a : tm) : result (t, error) = {
//     let* s = cut(s, "#f", Arrow(x, ty_a, ty_b));
//     let* s = swap(s);
//     let* a_wk = wk(a);
//     let* s = in_elimination(s, Ap(Var(0), a_wk));
//     let* ty_a' = wk(ty_a);
//     let* s = ap(s, x, ty_a', wkn(1, ty_b));
//     let* s = hyp(s);
//     let* s = weaken_goal(s);
//     Ok(s)
// }

// // if the focus of [s] is c |- B, refines to goals A -> B and A
// // assumes [ty_A] (A) is well-typed in c
// let modus_ponens(s : t, ty_a : tm) : result (t, error) = {
//     let* s = cut(s, "#a", ty_a);
//     let* s = swap(s);
//     let* ty_a' = wk(ty_a);
//     let (_, ty_b) = goal_tuple(s);
//     let* ty_b' = wk(ty_b);
//     let* s = forall_elim(s, "_", ty_a', ty_b', Var(0));
//     let* s = hyp(s);
//     let* s = weaken_goal(s);
//     Ok(s)
// }


// tries to discharge goals of the form `t : T`
let rec check(s : t) : result(t, error) = {
    let (c, ty_goal, _) = goal_tuple(s);
    switch(ty_goal) {
        | In(Prop, _) => prop_formation(s)
        | In(Typ, _) => typ_formation(s)
        | In(Arrow(x, t1, _), _) => {
            let* s = 
                switch(infer_typ(c, t1)) {
                | Ok(Prop) => prop_arrow_formation(s, x)
                | Ok(Typ) => typ_arrow_formation(s, x)
                | Ok(_) => Error("arrow domain is not a prop or type")
                | Error(e) => Error(e)
                };
            let* s = check(s);
            let* s = check(s);
            Ok(s)
        }
        | In(Var(_), _) => hyp_typ(s)
        | In(Ap(_, a1, _), _) => {
            switch(infer_typ(c, a1)) {
            | Ok(Arrow(x, ty1, ty2)) => {
                let* s = ap(s, x, ty1, ty2);
                let* s = check(s);
                let* s = check(s);
                Ok(s)
            }
            | _ => Error("applying a non-arrow")
            }
        }
        | In(Lam(_), _) => {
            let* s = pi_introduction(s);
            let* s = check(s);
            let* s = check(s);
            Ok(s)
        }
        | In(In(_, _), _) => failwith("unimplemented: In")
        // | In(_, _) => failwith("impossible")
        | _ => Error("not a type obligation")
    }
}

let obvious(s : t) : result(t, error) = {
    let! _ = assumed(s);
    let! e = check(s);
    Error(e)
}

let given(s : t, x) : result(t, error) = {
    let (c, ty_goal, _) = goal_tuple(s);
    switch(ty_goal) {
    | Arrow(_, ty1, _) => 
        switch(infer_typ(c, ty1)) {
        | Ok(Prop) => implies_introduction(s, x)
        | _ => forall_introduction(s, x)
        }
    | _ => Error("not an arrow")
    }
}

let given_type(s : t, x, ty_elab) : result(t, error) = {
    let (_, ty_goal, _) = goal_tuple(s);
    switch(ty_goal) {
    | Arrow(_, ty1, _) when !equiv(ty_elab, ty1) =>  Error("wrong given type")
    | _ => given(s, x)
    }
}

// // if the goal is c |- (y : A) -> B, refines to c |- A : type and c, x : A |- B
// let forall_introduction(s : t, x : name) = {
//     let* s = 
// }

// if the goal is (M : prop) -> (A -> M) -> M, refines to goal A.
let direct(s : t) : result(t, error) = {
    let* s = forall_introduction(s, "M");
    let* s = obvious(s);
    let* s = implies_introduction(s, "h");
    let* s = obvious(s);
    let (c, _, _) = goal_tuple(s);
    let* target = switch(lookup_index_prop(c, 0)) {
        | Ok(Arrow(_, ty_a, _)) => Ok(ty_a) 
        | _ => Error("cannot prove directly")
    };
    let* s = implies_elimination(s, target);
    let* s = assumed(s);
    let* s = weaken_goal(s);
    let* s = weaken_goal(s);
    Ok(s)
}

let at_ty(s : t, ty1 : tm, a : tm) : result(t, error) = 
    switch(ty1) {
    | Arrow(x, ty_1, ty_2) => forall_elimination(s, x, ty_1, ty_2, a)
    | _ => Error("Cannot 'at' non-arrow type")
    }

// attempt(s, arrow_introduction("M", s), s1 => {
    //             let (s2, r1) = check_demo(s1, Obvious);
    //             attempt(s2, arrow_introduction("h", s2), s3 => {
    //                 let (s4, r2) = check_demo(s3, Obvious);
    //                 let (c, _) = pair_of_judgment(Result.get_ok(focused(s4)));
    //                 let target = switch(lookup_index(c, 0)) {
    //                     | Arrow(_, ty_a, _) => ty_a 
    //                     | _ => failwith("impossible")
    //                 };
    //                 attempt(s4, modus_ponens(s4, target), s5 => {
    //                     attempt(s5, assumed(s5), s6 => {
    //                         attempt(s6, weaken(s6), s7 => {
    //                             attempt(s7, weaken(s7), s8 => {
    //                                 let (s9, r3) = check_demo(s8, d);
    //                                 (s9, merge_report_list([r1, r2, r3]))
    //                             })
    //                         })
    //                     })
    //                 })
    //             })
    //         })

// let rec nth_premise(ty : tm, n : int, downshift : int) : result (tm, error) = {
//     switch(ty) {
//     | Arrow(_, ty1, ty2) when n == 1 && no_x(ty2, 0) => Ok(varmap(ty1, 0, x => x-downshift))
//     | Arrow(_, _, ty2) when n > 1 => nth_premise(ty2, n-1, downshift+1)
//     | _ => Error("head cannot be applied")
//     }
// }

let rec find_refl(c : ctx, eq : int, current : int) : result(int, error) = {
    try { 
        switch(lookup_index_prop(c, current)) {
        | Ok(Arrow(_, Typ, Arrow(_, Var(0), 
            Ap(Lax, Ap(Lax, Ap(Lax, Var(eq'), Var(1)), Var(0)), Var(0)))))
            when eq == eq'-2  => Ok(current)
        | _ => find_refl(c, eq, current-1)
        } 
    } { | _ => Error("couldn't find refl") }
}

// precondition: the [s.focused] is nonempty
// invariant: the root of returned PD.t is the same as that of [s]
// invariant: the focused of returned PD.t is the tail of that of [s]
let rec check_demo(s : t, d : demo) : (t, report) = 
    switch(d) {
    | Hole =>
        let s' = Result.get_ok(skip(s));
        let j = Result.get_ok(focused(s));
        (s', mk_report([j], []))
    | HypProp(x) =>
        let f = Result.get_ok(focused(s));
        attempt(s, index_of_name(ctx_of_judgment(f), x), n => 
            check_demo(s, ElabHypProp(n)))
    | ElabHypProp(n) =>
        attempt(s, hyp_prop(s, n), s' => (s', pure_report))
    | HypTyp(x) =>
        let (c, ty_goal, _) = goal_tuple(s);
        attempt(s, index_of_name(c, x), n => {
            switch(ty_goal) {
            | In(Var(n'), _) when n' == n => {
                attempt(s, hyp_typ(s), s' => 
                    (s', pure_report))
            }
            | _ => skip_and_error(s, "typ-of failure")
            }
        })
    | InForm(ty, d1, d2) =>
        let-+ s = dry(s, in_formation(s, ty));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    | Claim(x, ty, d1, d2) => {
        let (c, _, _) = goal_tuple(s);
        let ty_elab = tm_of_surface(c, ty);
        attempt(s, cut(s, x, ty_elab), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    }
    | Suffices(x, ty, d1, d2) => {
        let (c, _, _) = goal_tuple(s);
        let ty_elab = tm_of_surface(c, ty);
        attempt(s, cut(s, x, ty_elab), s' => {
            attempt(s', swap(s'), s'' => {
                let (s''', r1) = check_demo(s'', d1);
                let (s'''', r2) = check_demo(s''', d2);
                (s'''', merge_reports(r1, r2))
            });
        });
    }
    | PropForm =>
        attempt(s, prop_formation(s), s' => (s', pure_report))
    | TypForm =>
        attempt(s, typ_formation(s), s' => (s', pure_report))
    | PropArrowForm(x, d1, d2) => 
        attempt(s, prop_arrow_formation(s, x), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    | TypArrowForm(x, d1, d2) => 
        attempt(s, typ_arrow_formation(s, x), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    // | ArrowElim(d) => attempt(s, arrow_elimination(s), s' => check_demo(s', d));
    | ApTyp(x, ty1, ty2, d1, d2) => {
        let (c, _, _) = goal_tuple(s);
        let ty1_elab = tm_of_surface(c, ty1);
        let ty2_elab = tm_of_surface(Cons(c, x, ty1_elab, Typ), ty2);
        check_demo(s, ElabApTyp(x, ty1_elab, ty2_elab, d1, d2))
    }
    | ElabApTyp(x, ty1, ty2, d1, d2) => {
        attempt(s, ap(s, x, ty1, ty2), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    }
    | At(d1, a, d2) => {
        let (c, _, _) = goal_tuple(s);
        let a_elab = tm_of_surface(c, a);
        check_demo(s, ElabAt(d1, a_elab, d2))
    }
    | ElabAt(d1, a, d2) => {
        let (c, _, _) = goal_tuple(s);
        attempt(s, {
            let* d1_ty = infer_proven_ty(c, d1);
            at_ty(s, d1_ty, a)}
            , s1 => {
            let (s2, r1) = check_demo(s1, d1);
            let (s3, r2) = check_demo(s2, d2);
            (s3, merge_report_list([r1, r2]))
        })
    }
    | Given(x, ty, d1, d2) => {
        let (c, _, _) = goal_tuple(s);
        let ty_elab = tm_of_surface(c, ty);
        check_demo(s, ElabGiven(x, ty_elab, d1, d2));
    }
    | ElabGiven(x, ty_elab, d1, d2) => {
        attempt(s, given_type(s, x, ty_elab), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        })
    }
    | Use(d1, d2) => {
        let (c, _, _) = goal_tuple(s);
        attempt(s, infer_proven_ty(c, d1), d1_ty => 
            switch(d1_ty) {
            | Arrow(_, ty_1, _)  => {
                attempt(s, implies_elimination(s, ty_1), s' => {
                    let (s2, r1) = check_demo(s', d1);
                    let (s3, r2) = check_demo(s2, d2);
                    (s3, merge_report_list([r1, r2]))
                })
            }
            | _ => skip_and_error(s, "not an arrow") 
            }
        )
    }
    | Obvious =>  attempt(s, obvious(s), s' => (s', pure_report))
    | Tactic(Check, ds) => {
        if(ds != []) {
            skip_and_error(s, "side conditions not supported yet")
        } else {
            attempt(s, check(s), s' => (s', pure_report))
        }
    }
    | Tactic(Schema(Definition), ds) => {
        if (ds != []) {
            skip_and_error(s, "side conditions not supported yet")
        } else {
            dry(s, definition(s));
        }
    }
    | Tactic(Direct, ds) => switch(ds) {
        | [d] => attempt(s, direct(s), s => check_demo(s, d))
        | _ => skip_and_error(s, "wrong number of args to direct")
    }
    | Tactic(GivenAll, ds) => switch(ds) {
        | [d] => 
            let (_, ty_goal, _) = goal_tuple(s);
            switch(ty_goal) {
            | Arrow(x, _, _) when x != "_" => {
                attempt(s, given(s, x), s1 => {
                    let (s2, r1) = check_demo(s1, Obvious);
                    let (s3, r2) = check_demo(s2, Tactic(GivenAll, [d]));
                    (s3, merge_reports(r1, r2))
                })
            }
            | _ => check_demo(s, d)
            }
        | _ => skip_and_error(s, "wrong number of args to givenall")
    }
}

and definition(s : t) : result(t, error) = {
    let (c, ty_goal, _) = goal_tuple(s);
    switch(ty_goal) {
    | Arrow(_, Prop, Arrow(_, Arrow(xname, ty, Arrow(xeq, Ap(Lax, Ap(Lax, Ap(Lax, Var(eq), ty'), Var(0)), xthing), Var(2))), Var(1))) => {
            let* str_ty = invert_wk(ty);
            let* str_ty' = invert_wk(ty');
            let* str_str_ty' = invert_wk(str_ty');
            if (!equiv(str_ty, str_str_ty')) { 
                Error("not a definition obligation: the term type does not match the equation type: " ++ Lang_printing.string_of_term(c, str_ty) ++ " ≠ " ++ Lang_printing.string_of_term(c, str_str_ty')) 
            } else {
                let* refl = find_refl(c, eq-2, eq-2);
                undry(check_demo(s, ElabGiven("M", Prop, PropForm, 
                    ElabGiven("h", Arrow(xname, ty, Arrow(xeq, Ap(Lax, Ap(Lax, Ap(Lax, Var(eq), ty'), Var(0)), xthing), Var(2))), Tactic(Check, []), 
                    Use(ElabAt(ElabHypProp(0), xthing, Obvious), ElabAt(ElabAt(ElabHypProp(refl+2), wk(ty), Obvious), xthing, Obvious))
                    ))))
            }
        }
    | Arrow(m, Prop, Arrow(_, Arrow(_, _, Arrow(_, Ap(Lax, Ap(Lax, Ap(Lax, Var(_), _), Var(0)), _), Var(2))), _)) 
        => Error("not a definition obligation: motive is not " ++ m)
    | Arrow(m, Prop, Arrow(_, Arrow(_, _, Arrow(_, Ap(Lax, Ap(Lax, Ap(Lax, Var(_), _), Var(0)), _), _)), _)) 
        => Error("not a definition obligation: inner motive is not " ++ m)
    | Arrow(_, Prop, Arrow(_, Arrow(_, _, Arrow(_, Ap(Lax, Ap(Lax, Ap(Lax, Var(_), _), _), _), _)), _)) 
        => Error("not a definition obligation: LHS of equation is not the declared object")
    | Arrow(_, Prop, Arrow(_, Arrow(_, _, Arrow(_, _, _)), _)) 
        => Error("not a definition obligation: second component is not an equation")
    | _ => Error("not a definition obligation: not a construction with two components")
    }
}


let check_demo_root(root : judgment, d : demo) : report = {
    let (s, r) = check_demo(init(root), d);
    assert(verify(s,root));
    r
}
