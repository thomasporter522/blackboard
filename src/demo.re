open Lang
// open Lang_printing
open Deriv.PartialDerivation
open Deriv

type surface_tm = 
    | Typ 
    | SurfaceIn(surface_tm, surface_tm)
    | SurfaceArrow(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | SurfaceUnlam(surface_tm, name)
    | SurfaceVar(name)
    | SurfaceAp(surface_tm, surface_tm);

type schema = 
    | Definition

type tactic = 
    | Check
    | Direct
    | GivenAll
    // | Schema(schema)

type demo = 
    | Hole
    | Hyp(name)
    | ElabHyp(int)
    | HypTyp(name)
    | InForm(tm, demo, demo)
    | InElim(tm, demo)
    | Claim(name, surface_tm, demo, demo)
    | Suffices(name, surface_tm, demo, demo)
    | TypForm
    | ArrowForm(name, demo, demo)
    | ArrowElim(demo)
    | ApTyp(name, surface_tm, surface_tm, demo, demo)
    | ElabApTyp(name, tm, tm, demo, demo)
    | At(demo, surface_tm, demo)
    | ElabAt(demo, tm, demo)
    | Given(name, surface_tm, demo, demo)
    | ElabGiven(name, tm, demo, demo)
    // | Use(demo, demo)
    | Obvious
    | Tactic(tactic, list(demo))

and tm_or_demo = 
    | Tm(surface_tm)
    | Demo(demo)

type demo_check_report = {
    open_goals : list(judgment),
    errors : list(string)
}

let report (open_goals : list(judgment), errors : list(string)) : demo_check_report = {
    open_goals, errors
}

let merge_reports(r1 : demo_check_report, r2 : demo_check_report) : demo_check_report = {
    open_goals : r1.open_goals @ r2.open_goals,
    errors : r1.errors @ r2.errors
}


let rec merge_report_list(rs : list(demo_check_report)) : demo_check_report = switch(rs){
    | [] => report([], [])
    | [h, ...t] => merge_reports(h, merge_report_list(t))
}

let skip_and_error(s : t, e : error) : (t, demo_check_report) {
    let s' = Result.get_ok(skip(s));
    (s', report([], [e]))
}


let attempt_option(v : result('a, error), f : 'a => (t, demo_check_report), backup : (t, demo_check_report)) : (t, demo_check_report) = {
    switch(v) {
    | Ok(v) => f(v)
    | Error(_) => backup
    }
}

let attempt(s : t, v : result('a, error), f : 'a => (t, demo_check_report)) : (t, demo_check_report) = {
    switch(v) {
    | Ok(v) => f(v)
    | Error(e) => skip_and_error(s, e)
    }
}


let rec var_of_surface (c : ctx, x : name) : int = switch(c) {
    | Cons(_, y, _) when x == y => 0 
    | Cons(c, _, _) => 1+var_of_surface(c, x)
    | Empty => failwith("unbound variable: " ++ x)
}

let rec tm_of_surface (c : ctx, t : surface_tm) : tm = switch(t) {
    | Typ => Typ
    | SurfaceIn(t1, t2) => In(tm_of_surface(c, t1),tm_of_surface(c, t2))
    | SurfaceArrow([x,...xs], t1, t2) => Arrow(x, tm_of_surface(c, t1), tm_of_surface(Cons(c, x, tm_of_surface(c, t1)), SurfaceArrow(xs, t1, t2)))
    | SurfaceArrow([], _, t2) => tm_of_surface(c, t2)
    | SimpleArrow(t1, t2) => Arrow("_", tm_of_surface(c, t1), tm_of_surface(Cons(c, "_", tm_of_surface(c, t1)), t2))
    | SurfaceUnlam(t, x) => switch(c) {
        | Cons(c', y, _) when x == y => Unlam(x, tm_of_surface(c', t))
        | Cons(_) => failwith("Can only unlambda with the most proximate variable")
        | Empty => failwith("Unable to elaborate unlamda in empty context")
    }
    | SurfaceVar(x) => Var(var_of_surface(c, x))
    | SurfaceAp(t1, t2) => Ap(tm_of_surface(c, t1),tm_of_surface(c, t2));
}

let rec find_assumption(c : ctx, ty : tm, n : int) : result (int, error) = {
    try {
        if (equiv(ty, get_lookup_index(c, n))) { Ok(n) } else { find_assumption(c, ty, n+1) }
    } {
       | _ => Error("can't find assumption")
    }
}


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
            switch(getsubst(elab_a, ty_b)) {
            | Arrow(x, a, b) => Ok((x, a, b))
            | _ => Error("constituent is not of arrow type")
            }
        })
    }
    }
}

// infers the type proven by a demo in a context
let rec infer_proven_ty(c : ctx, d : demo) : result(tm, error) = switch(d) {
    | Hyp(x) => Result.bind(index_of_name(c, x), n => infer_proven_ty(c, ElabHyp(n)))
    | ElabHyp(n) => lookup_index(c, n)
    | At(d1, a, d2) => {
        let elab_a = tm_of_surface(c, a);
        infer_proven_ty(c, ElabAt(d1, elab_a, d2))
    }
    | ElabAt(d, a, _) => {
        Result.bind(infer_proven_ty(c, d), inferred_ty => switch(inferred_ty) {
        | Arrow(_, _, ty_b) =>
            Ok(getsubst(a, ty_b))
        | _ => Error("ap of non-arrow")
        })
    }
    // | Use(d1, _) => {
    //     Result.bind(infer_proven_ty(c, d1), inferred_ty => switch(inferred_ty) {
    //     | Arrow(_, _, ty_b) when no_x(ty_b, 0) => Ok(downshift(ty_b, 0))
    //     | _ => Error("use of non-arrow or non-simple arrow")
    //     })
    // }
    | _ => Error("cannot infer what it proves") // todo: make this message better
}

// infers the type of a term in a context
let rec infer_typ(c : ctx, a : tm) : result(tm, error) = switch(a) {
    | Typ => Ok(Typ)
    | In(_) => Ok(Typ)
    | Arrow(_) => Ok(Typ)
    | Lam(x, ty, b) => Result.bind(infer_typ(Cons(c, x, ty), b), ty_body => Ok(Arrow(x, ty, ty_body)))
    | Unlam(_, f) => switch(c) {
        | Empty => Error("Unlambda has no type in the empty context")
        | Cons(c', _, _) => switch(infer_typ(c', f)) {
            | Ok(Arrow(_, _, ty_b)) => Ok(ty_b)
            | Ok(_) => Error("Unlambda body does not have arrow type")
            | Error(e) => Error(e)
            }   
        }
    | Var(x) => lookup_index(c, x)
    | Ap(a1, a2) => switch(infer_typ(c, a1)) {
        | Ok(Arrow(_, _, ty2)) => subst(a2, ty2)
        | Ok(_) => Error("Applied term does not have arrow type")
        | Error(e) => Error(e)
    }
}

let assumed(s : t) : result (t, error) = {
    let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
    Result.bind(find_assumption(c, ty_goal, 0), n => 
        Result.bind(in_elimination(s, Var(n)), s' => 
                hyp(s')))
}

// inverse of wknvar(n, _)
let invert_wknvar(n : int, m : int) : result(int, error) = {
    if (n == m) { Error("unstrengthenable var") } else 
    if (n > m) { Ok(m) } else { Ok(m-1) }
}

// inverse of wkn(n, _)
let rec invert_wkn(n : int, a : tm) : result(tm, error) = switch(a) {
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
    | Unlam(y, a) =>
        if (n <= 0) { Error("unstrengthenable") } 
        else { 
            let* a' = invert_wkn(n-1, a);
            Ok(Unlam(y, a')) 
        } 
    | Var(y) => {
        let* y' = invert_wknvar(n, y);
        Ok(Var(y'))
    }
    | Ap(a1, a2) => {
        let* a1' = invert_wkn(n, a1);
        let* a2' = invert_wkn(n, a2);
        Ok(Ap(a1', a2'))
    } 
}

// inverse of wk(_)
let invert_wk(a : tm) : result(tm, error) = invert_wkn(0, a)

// if the focus of [s] is c, x : A |- T, refines to goal c |- T' where wk(T') = T
let weaken_goal(s : t) : result(t, error) = {
    let (_, ty) = pair_of_judgment(Result.get_ok(focused(s)));
    let* ty_inv_wk = invert_wk(ty);
    weaken(s, ty_inv_wk)
}

// if the focus of [s] is c |- B[a/x], refines to goals a : A and (x : A) -> B
// assumes (x : A) -> B is well-typed in c
let forall_elim(s : t, x : name, ty_a : tm, ty_b : tm, a : tm) : result (t, error) = {
    let* s = cut(s, "#f", Arrow(x, ty_a, ty_b));
    let* s = swap(s);
    let* a_wk = wk(a);
    let* s = in_elimination(s, Ap(Var(0), a_wk));
    let* ty_a_wk = wk(ty_a);
    let* s = ap(s, x, ty_a_wk, wkn(1, ty_b));
    let* s = hyp(s);
    let* s = weaken_goal(s);
    Ok(s)
}

// if the focus of [s] is c |- B, refines to goals A -> B and A
// assumes [ty_A] (A) is well-typed in c
let modus_ponens(s : t, ty_a : tm) : result (t, error) = {
    let* s = cut(s, "#a", ty_a);
    let* ty_a' = wk(ty_a);
    // let ty_a' = ty_a;
    let (_, ty_b) = goal(s);
    let* s = forall_elim(s, "_", ty_a', ty_b, Var(0));
    // let* s = in_elimination(s, Var(0));
    // let* ty_a'' = wk(ty_a');
    // let* ty_b' = wk(ty_b);
    // let* s = ap(s, "_", ty_a'', ty_b');
    // let* s = hyp(s);
    let* s = hyp(s);
    let* s = weaken_goal(s);
    Ok(s)
    // Result.bind(cut(s, "#a", ty_a), s' => {
    // Result.bind(swap(s'), s2 => {
    // let (_, ty_b) = pair_of_judgment(Result.get_ok(focused(s2)));
    // Result.bind(cut(s2, "#f", Arrow("_", getwk(ty_a), getwk(ty_b))), s3 => {
    // Result.bind(swap(s3), s4 => {
    // Result.bind(in_elimination(s4, Ap(Var(0), Var(1))), s5 => {
    // Result.bind(ap(s5, "_", getwk(getwk(ty_a)), getwk(getwk(ty_b))), s6 => { 
    // Result.bind(hyp(s6), s7 => { 
    // Result.bind(hyp(s7), s8 => { 
    // weaken(s8, failwith("todo"))
    // })
    // })
    // })
    // })
    // })
    // })
    // })
    // })
}

// if(ds != []) {
//     skip_and_error(s, "side conditions not supported yet")
// } else {
//     let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
//     switch(ty_goal) {
//         | In(Typ, _) => check_demo(s, TypForm)
//         | In(Arrow(x, _, _), _) => check_demo(s, ArrowForm(x, Tactic(Check, []), Tactic(Check, [])))
//         | In(Var(_), _) => attempt(s, hyp(s), s' => (s', report([], [])))
//         | In(Ap(a1, _), _) => {
//             switch(infer_typ(c, a1)) {
//             | Ok(Arrow(x, ty1, ty2)) => check_demo(s, ElabApTyp("_" ++ x, ty1, ty2, Tactic(Check, []), Tactic(Check, [])))
//             | _ => skip_and_error(s, "applying a non-arrow")
//             }
//         }
//         | In(Lam(_), _) => failwith("unimplemented: Lam")
//         | In(Unlam(_), _) => check_demo(s, ArrowElim(Tactic(Check, [])))
//         | In(In(_, _), _) => failwith("unimplemented: In")
//         | _ => skip_and_error(s, "not a type obligation")
//     }


let rec check(s : t) : result(t, error) = {
    let (c, ty_goal) = goal(s);
    switch(ty_goal) {
        | In(Typ, _) => typ_formation(s)
        | In(Arrow(x, _, _), _) => {
            let* s = arrow_formation(s, x);
            let* s = check(s);
            let* s = check(s);
            Ok(s)
        }
        | In(Var(_), _) => hyp(s)
        | In(Ap(a1, _), _) => {
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
        | In(Lam(_), _) => failwith("unimplemented: Lam")
        | In(Unlam(_), _) => {
            let* s = arrow_elimination(s);
            let* s = check(s);
            Ok(s)
        }
        | In(In(_, _), _) => failwith("unimplemented: In")
        | _ => Error("not a type obligation")
    }
}

let obvious(s : t) : result(t, error) = {
    let! _ = assumed(s);
    let! e = check(s);
    Error(e)
}

// if the goal is (M : type) -> (A -> M) -> M, refines to goal A.
let direct(s : t) : result(t, error) = {
    let* s = arrow_introduction(s, "M");
    let* s = obvious(s);
    let* s = arrow_introduction(s, "h");
    let* s = obvious(s);
    let (c, _) = goal(s);
    let* target = switch(lookup_index(c, 0)) {
        | Ok(Arrow(_, ty_a, _)) => Ok(ty_a) 
        | _ => Error("cannot prove directly")
    };
    print_endline(Lang_printing.string_of_term(c, target));
    let* s = modus_ponens(s, target);
    let* s = assumed(s);
    let* s = weaken_goal(s);
    let* s = weaken_goal(s);
    Ok(s)
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
        switch(get_lookup_index(c, current)) {
        | Arrow(_, Typ, Arrow(_, Var(0), 
            Ap(Ap(Ap(Var(eq'), Var(1)), Var(0)), Var(0))
            )) when eq == eq'-2  => Ok(current)
        | _ => find_refl(c, eq, current-1)
        } 
    } { | _ => Error("couldn't find refl") }
}

// precondition: the [s.focused] is nonempty
// invariant: the root of returned PD.t is the same as that of [s]
// invariant: the focused of returned PD.t is the tail of that of [s]
let rec check_demo(s : t, d : demo) : (t, demo_check_report) = 
    switch(d) {
    | Hole =>
        let s' = Result.get_ok(skip(s));
        let j = Result.get_ok(focused(s));
        (s', report([j], []))
    | Hyp(x) =>
        let f = Result.get_ok(focused(s));
        attempt(s, index_of_name(ctx_of_judgment(f), x), n => 
            check_demo(s, ElabHyp(n)))
    | ElabHyp(n) =>
        attempt(s, in_elimination(s, Var(n)), s' => 
            attempt(s', hyp(s'), s'' => 
                (s'', report([], []))))
    | HypTyp(x) =>
        let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
        attempt(s, index_of_name(c, x), n => {
            switch(ty_goal) {
            | In(Var(n'), _) when n' == n => {
                attempt(s, hyp(s), s' => 
                    (s', report([], [])))
            }
            | _ => skip_and_error(s, "typ-of failure")
            }
        })
    | InForm(ty, d1, d2) => 
        attempt(s, in_formation(s, ty), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    | InElim(a, d) => {
        attempt(s, in_elimination(s, a), s' => {
            let (s'', r1) = check_demo(s', d);
            (s'', r1)
        });
    }
    | Claim(x, ty, d1, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let ty_elab = tm_of_surface(c, ty);
        attempt(s, cut(s, x, ty_elab), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    }
    | Suffices(x, ty, d1, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let ty_elab = tm_of_surface(c, ty);
        attempt(s, cut(s, x, ty_elab), s' => {
            attempt(s', swap(s'), s'' => {
                let (s''', r1) = check_demo(s'', d1);
                let (s'''', r2) = check_demo(s''', d2);
                (s'''', merge_reports(r1, r2))
            });
        });
    }
    | TypForm =>
        attempt(s, typ_formation(s), s' => (s', report([], [])))
    | ArrowForm(x, d1, d2) => 
        attempt(s, arrow_formation(s, x), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    | ArrowElim(d) => attempt(s, arrow_elimination(s), s' => check_demo(s', d));
    | ApTyp(x, ty1, ty2, d1, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let ty1_elab = tm_of_surface(c, ty1);
        let ty2_elab = tm_of_surface(Cons(c, x, ty1_elab), ty2);
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
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let a_elab = tm_of_surface(c, a);
        check_demo(s, ElabAt(d1, a_elab, d2))
    }
    | ElabAt(d1, a, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        attempt(s, infer_proven_ty(c, d1), d1_ty => 
            switch(d1_ty) {
            | Arrow(x, ty_1, ty_2) => {
                attempt(s, forall_elim(s, x, ty_1, ty_2, a), s' => {
                let (s2, r1) = check_demo(s', d2);
                let (s3, r2) = check_demo(s2, d1);
                (s3, merge_report_list([r1, r2]))
            })
            }
            | _ => skip_and_error(s, "applying non arrow")
            }
        )
    }
    | Given(x, ty, d1, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let ty_elab = tm_of_surface(c, ty);
        check_demo(s, ElabGiven(x, ty_elab, d1, d2));
    }
    | ElabGiven(x, ty_elab, d1, d2) => {
        let (_c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
        switch(ty_goal) {
            | Arrow(_, ty1, _) => 
                if (!equiv(ty_elab, ty1)) {
                    skip_and_error(s, "wrong given type")
                } else {
                    attempt(s, arrow_introduction(s, x), s' => {
                    let (s'', r1) = check_demo(s', d1);
                    let (s''', r2) = check_demo(s'', d2);
                    (s''', merge_reports(r1, r2))
                })
                }
            | _ => skip_and_error(s, "not an arrow")
        }}
    // | Use(d1, d2) => {
    //     let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
    //     attempt(s, infer_proven_ty(c, d1), d1_ty => 
    //         switch(d1_ty) {
    //         | Arrow(_, ty_1, ty_2) when no_x(ty_2, 0) => {
    //             attempt(s, modus_ponens(s, ty_1), s' => {
    //                 let (s2, r1) = check_demo(s', d1);
    //                 let (s3, r2) = check_demo(s2, d2);
    //                 (s3, merge_report_list([r1, r2]))
    //             })
    //         }
    //         | _ => skip_and_error(s, "not a simple arrow") 
    //         }
    //     )
    // }
    | Obvious => {
        attempt_option(typ_formation(s), s' => (s', report([], [])), 
        attempt_option(assumed(s), s' => (s', report([], [])), 
        attempt_option(hyp(s), s' => (s', report([], [])), 
        // skip_and_error(s, "not obvious"))))
        check_demo(s, Tactic(Check, [])))))
    }
    | Tactic(Check, ds) => {
        if(ds != []) {
            skip_and_error(s, "side conditions not supported yet")
        } else {
            attempt(s, check(s), s' => (s', report([], [])))
        }
    }
    // | Tactic(Schema(Definition), ds) => {
    //     if (ds != []) {
    //         skip_and_error(s, "side conditions not supported yet")
    //     } else {
    //         let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
    //         switch(ty_goal) {
    //         | Arrow(_, Typ, Arrow(_, Arrow(xname, ty, Arrow(xeq, Ap(Ap(Ap(Var(eq), ty'), Var(0)), xthing), Var(2))), Var(1))) 
    //             when equiv(ty, ty') => 
    //             attempt(s, find_refl(c, eq-2, eq-2), refl => {
    //             check_demo(s, ElabGiven("M", Typ, TypForm, 
    //                 ElabGiven("portal", Arrow(xname, ty, Arrow(xeq, Ap(Ap(Ap(Var(eq), ty'), Var(0)), xthing), Var(2))), Tactic(Check, []), 
    //                 ElabAt(ElabAt(ElabHyp(0), xthing, Obvious), Ap(Ap(Var(refl+2), ty), xthing), Obvious)
    //                 )))
    //             })
    //         | _ => skip_and_error(s, "not a definition obligation")
    //         }
    //     }
    // }
    | Tactic(Direct, ds) => switch(ds) {
        | [d] => attempt(s, direct(s), s => check_demo(s, d))
        | _ => skip_and_error(s, "wrong number of args to direct")
    }
    | Tactic(GivenAll, ds) => switch(ds) {
        | [d] => 
            let (_c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
            switch(ty_goal) {
            | Arrow(x, _, _) when x != "_" => {
                attempt(s, arrow_introduction(s, x), s1 => {
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


let check_demo_root(root : judgment, d : demo) : demo_check_report = {
    let (s, r) = check_demo(init(root), d);
    assert(verify(s,root));
    r
}
