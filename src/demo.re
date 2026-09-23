open Lang
open Deriv.PartialDerivation

type surface_tm = 
    | Typ 
    | In(surface_tm, surface_tm)
    | Arrow(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | Var(name)
    | Ap(surface_tm, surface_tm);

type schema = 
    | Definition

type tactic = 
    | Check
    | Schema(schema)

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
    | Ap(name, surface_tm, surface_tm, demo, demo)
    | FE(name, surface_tm, demo)
    | At(demo, list((surface_tm, demo)))
    | BinaryAt(demo, surface_tm, demo)
    | ElabAp(name, tm, tm, demo, demo)
    | Given(name, surface_tm, demo, demo)
    | ElabGiven(name, tm, demo, demo)
    | Use(demo, list(demo))
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
    | In(t1, t2) => In(tm_of_surface(c, t1),tm_of_surface(c, t2))
    | Arrow([x,...xs], t1, t2) => Arrow(x, tm_of_surface(c, t1), tm_of_surface(Cons(c, x, tm_of_surface(c, t1)), Arrow(xs, t1, t2)))
    | Arrow([], _, t2) => tm_of_surface(c, t2)
    | SimpleArrow(t1, t2) => Arrow("_", tm_of_surface(c, t1), tm_of_surface(Cons(c, "_", tm_of_surface(c, t1)), t2))
    | Var(x) => Var(var_of_surface(c, x))
    | Ap(t1, t2) => Ap(tm_of_surface(c, t1),tm_of_surface(c, t2));
}

let rec find_assumption(c : ctx, ty : tm, n : int) : result (int, error) = {
    try {
        if (equiv(ty, lookup_index(c, n))) { Ok(n) } else { find_assumption(c, ty, n+1) }
    } {
       | _ => Error("can't find assumption")
    }
}

let assumed(s : t) : result (t, error) = {
    let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
    Result.bind(find_assumption(c, ty_goal, 0), n => 
        Result.bind(in_elimination(s, Var(n)), s' => 
                hyp(s')))
}

// if the focus of [s] is c |- B, refines to goals A -> B and A
// assumes [ty_A] (A) is well-typed in c
let modus_ponens(s : t, ty_a : tm) : result (t, error) = {
    Result.bind(cut(s, "#a", ty_a), s' => {
    Result.bind(swap(s'), s2 => {
    let (_, ty_b) = pair_of_judgment(Result.get_ok(focused(s2)));
    Result.bind(cut(s2, "#f", Arrow("_", shift(ty_a, 0), shift(ty_b, 0))), s3 => {
    Result.bind(swap(s3), s4 => {
    Result.bind(in_elimination(s4, Ap(Var(0), Var(1))), s5 => {
    Result.bind(ap(s5, "_", shift(shift(ty_a, 0), 0), shift(shift(ty_b, 1), 1)), s6 => { 
    Result.bind(hyp(s6), s7 => { 
    Result.bind(hyp(s7), s8 => { 
    weaken(s8)
    })
    })
    })
    })
    })
    })
    })
    })
}

// if the focus of [s] is c |- B[a], refines to goals a : A and (x : A) -> B[x]
// assumes (x : A) -> B[x] is well-typed in c
let forall_elim(s : t, x : name, ty_a : tm, ty_b : tm, a : tm) : result (t, error) = {
    // let (_, ty_b) = pair_of_judgment(Result.get_ok(focused(s2)));
    Result.bind(cut(s, "#f", Arrow(x, ty_a, ty_b)), s3 => {
    Result.bind(swap(s3), s4 => {
    Result.bind(in_elimination(s4, Ap(Var(0), shift(a, 0))), s5 => {
    Result.bind(ap(s5, x, shift(ty_a, 0), shift(ty_b, 1)), s6 => { 
    Result.bind(hyp(s6), s7 => { 
    weaken(s7)
    })
    })
    })
    })
    })
}

let rec nth_premise(ty : tm, n : int, downshift : int) : result (tm, error) = {
    switch(ty) {
    | Arrow(_, ty1, ty2) when n == 1 && no_x(ty2, 0) => Ok(varmap(ty1, 0, x => x-downshift))
    | Arrow(_, _, ty2) when n > 1 => nth_premise(ty2, n-1, downshift+1)
    | _ => Error("head cannot be applied")
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
            switch(subst(ty_b, elab_a, 0)) {
            | Arrow(x, a, b) => Ok((x, a, b))
            | _ => Error("constituent is not of arrow type")
            }
        })
    }
    }
}

let rec infer_proven_ty(c : ctx, d : demo) : result(tm, error) = switch(d) {
    | Hyp(x) => Result.bind(index_of_name(c, x), n => infer_proven_ty(c, ElabHyp(n)))
    | ElabHyp(n) => try { Ok(lookup_index(c, n)) } { | _ => Error("Cannot find index")}
    | At(d, []) => infer_proven_ty(c, d)
    | At(d, [(a, _), ...args]) => {
        Result.bind(infer_proven_ty(c, At(d, args)), inferred_ty => switch(inferred_ty) {
        | Arrow(_, _, ty_b) =>
            let elab_a = tm_of_surface(c, a);
            Ok(subst(ty_b, elab_a, 0))
        | _ => Error("ap of non-arrow")
        })
    }
    | BinaryAt(d, a, _) => {
        Result.bind(infer_proven_ty(c, d), inferred_ty => switch(inferred_ty) {
        | Arrow(_, _, ty_b) =>
            let elab_a = tm_of_surface(c, a);
            Ok(subst(ty_b, elab_a, 0))
        | _ => Error("ap of non-arrow")
        })
    }
    | Use(d, []) => infer_proven_ty(c, d)
    | Use(d, [_, ... args]) => {
        Result.bind(infer_proven_ty(c, Use(d, args)), inferred_ty => switch(inferred_ty) {
        | Arrow(_, _, ty_b) when no_x(ty_b, 0) => Ok(downshift(ty_b, 0))
        | _ => Error("use of non-arrow or non-simple arrow")
        })
    }
    | _ => Error("cannot infer what it proves") // todo: make this message better
}

let rec infer_typ(c : ctx, a : tm) : tm = switch(a) {
    | Typ => Typ
    | In(_) => Typ
    | Arrow(_) => Typ
    | Var(x) => lookup_index(c, x)
    | Ap(a1, a2) => {
        switch(infer_typ(c, a1)) {
        | Arrow(_, _, ty2) => subst(ty2, a2, 0)
        | _ => Typ
        }
    }
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
    | Ap(x, ty1, ty2, d1, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let ty1_elab = tm_of_surface(c, ty1);
        let ty2_elab = tm_of_surface(Cons(c, x, ty1_elab), ty2);
        check_demo(s, ElabAp(x, ty1_elab, ty2_elab, d1, d2))
    }
    | ElabAp(x, ty1, ty2, d1, d2) => {
        attempt(s, ap(s, x, ty1, ty2), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    }
    | FE(hd, a, d) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let a_elab = tm_of_surface(c, a);
        attempt(s, index_of_name(c, hd), n => {
            switch(lookup_index(c, n)) {
            | Arrow(x, ty_a, ty_b) => 
                attempt(s, forall_elim(s, x, ty_a, ty_b, a_elab), s' => {
                    let (s'', r1) = check_demo(s', d);
                    let (s3, r2) = check_demo(s'', ElabHyp(n));
                    (s3, merge_reports(r1, r2))
                })
            | _ => skip_and_error(s, "cannot apply non-head")
            }
        })
    }
    | At(hd, tds) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        attempt(s, infer_proven_ty(c, hd), hd_ty => 
            at_with_reversed_args(s, c, hd, hd_ty, tds)
        )
    }
    | BinaryAt(d1, a, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        attempt(s, infer_proven_ty(c, d1), d1_ty => 
            switch(d1_ty) {
            | Arrow(x, ty_1, ty_2) => {
                let a_elab = tm_of_surface(c, a);
                attempt(s, forall_elim(s, x, ty_1, ty_2, a_elab), s' => {
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
                    attempt(s, arrow_introduction(x, s), s' => {
                    let (s'', r1) = check_demo(s', d1);
                    let (s''', r2) = check_demo(s'', d2);
                    (s''', merge_reports(r1, r2))
                })
                }
            | _ => skip_and_error(s, "not an arrow")
        }}
    | Use(hd, ds) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        attempt(s, infer_proven_ty(c, hd), hd_ty => 
            use_with_reversed_args(s, hd, hd_ty, ds)
        )
    }
    | Obvious => {
        attempt_option(typ_formation(s), s' => (s', report([], [])), 
        attempt_option(assumed(s), s' => (s', report([], [])), 
        attempt_option(hyp(s), s' => (s', report([], [])), 
        check_demo(s, Tactic(Check, [])))))
    }
    | Tactic(Check, ds) => {
        if(ds != []) {
            skip_and_error(s, "side conditions not supported yet")
        } else {
            let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
            switch(ty_goal) {
                | In(Typ, _) => check_demo(s, TypForm)
                | In(Arrow(x, _, _), _) => check_demo(s, ArrowForm(x, Tactic(Check, []), Tactic(Check, [])))
                | In(Var(_), _) => attempt(s, hyp(s), s' => (s', report([], [])))
                | In(Ap(a1, _), _) => {
                    switch(infer_typ(c, a1)) {
                    | Arrow(x, ty1, ty2) => check_demo(s, ElabAp("_" ++ x, ty1, ty2, Tactic(Check, []), Tactic(Check, [])))
                    | _ => skip_and_error(s, "applying a non-arrow")
                    }
                }
                | In(In(_, _), _) => failwith("unimplemented: In")
                | _ => skip_and_error(s, "not a type obligation")
            }
        }
    }
    | Tactic(Schema(Definition), ds) => {
        if (ds != []) {
            skip_and_error(s, "side conditions not supported yet")
        } else {
            let (_, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
            switch(ty_goal) {
            | Arrow(_, Typ, Arrow(_, Arrow(xname, ty, Arrow(xeq, Ap(Ap(Ap(Ap(Var(eq), ty'), ty''), Var(0)), xthing), Var(2))), Var(1))) 
                when equiv(ty, ty') && equiv(ty, ty'') => 
                check_demo(s, ElabGiven("M", Typ, TypForm, 
                    ElabGiven("portal", Arrow(xname, ty, Arrow(xeq, Ap(Ap(Ap(Ap(Var(eq), ty'), ty''), Var(0)), xthing), Var(2))), Tactic(Check, []), 
                    Hole //ElabAp("thing", )
                    )))
            | _ => skip_and_error(s, "not a definition obligation")
            }
        }
    }
}

and use_with_reversed_args(s : t, hd : demo, hd_ty : tm, ds : list(demo)) : (t, demo_check_report) = {
    switch(ds){
    | [] => check_demo(s, hd);
    | [d,... other_ds] =>
        switch(nth_premise(hd_ty, List.length(ds), 0)) {
        | Ok(premise) => {
            attempt(s, modus_ponens(s, premise), s' => {
                let (s2, r1) = use_with_reversed_args(s', hd, hd_ty, other_ds);
                let (s3, r2) = check_demo(s2, d);
                (s3, merge_report_list([r1, r2]))
            })
        }
        | Error(e) => skip_and_error(s, e)
        };
    }
}

and at_with_reversed_args(s : t, c : ctx, hd : demo, hd_ty : tm, tds : list((surface_tm, demo))) : (t, demo_check_report) = {
    switch(tds){
    | [] => check_demo(s, hd);
    | [(a, d),... other_tds] =>
        switch(infer_arrow_typ_of_ap(c, hd_ty, other_tds)) {
        | Ok((x, ty_a, ty_b)) => {
            let a_elab = tm_of_surface(c, a);
            attempt(s, forall_elim(s, x, ty_a, ty_b, a_elab), s' => {
                let (s2, r1) = check_demo(s', d);
                let (s3, r2) = at_with_reversed_args(s2, c, hd, hd_ty, other_tds);
                (s3, merge_report_list([r1, r2]))
            })
        }
        | Error(e) => skip_and_error(s, e)
        };
    }
}


let check_demo_root(root : judgment, d : demo) : demo_check_report = {
    let (s, r) = check_demo(init(root), d);
    assert(verify(s,root));
    r
}
