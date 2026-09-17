open Core
open Core.PartialDerivation

type surface_tm = 
    | Typ 
    | In(surface_tm, surface_tm)
    | Arrow(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | Var(name)
    | Ap(surface_tm, surface_tm);

type demo = 
    | Hole
    | Hyp(name)
    | HypTyp(name)
    | InForm(tm, demo, demo)
    | InElim(tm, demo)
    | Have(name, tm, demo, demo)
    | Suffices(name, tm, demo, demo)
    | TypForm
    | ArrowForm(demo, demo)
    | Ap(name, tm, tm, demo, demo)
    | Given(name, surface_tm, demo, demo)
    | Mp(surface_tm, demo, demo)
    | Use(name, list(demo))
    | Obvious

// and tm_or_demo = 
//     | Tm(surface_tm)
//     | Demo(demo)

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
    | Empty => failwith("unbound variable")
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
    Result.bind(ap(s5, "_", shift(shift(ty_a, 0), 0), shift(shift(ty_b, 0), 0)), s6 => { // todo: shift these?
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

// precondition: the [s.focused] is nonempty
// invariant: the root of returned PD.t is the same as that of [s]
// invariant: the focused of returned PD.t is the tail of that of [s]
let rec check_demo(s : t, d : demo) : (t, demo_check_report) = {
    switch(d) {
    | Hole =>
        let s' = Result.get_ok(skip(s));
        let j = Result.get_ok(focused(s));
        (s', report([j], []))
    | Hyp(x) =>
        let f = Result.get_ok(focused(s));
        attempt(s, index_of_name(ctx_of_judgment(f), x), n => 
            attempt(s, in_elimination(s, Var(n)), s' => 
                attempt(s', hyp(s'), s'' => 
                    (s'', report([], [])))))
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
    | Have(x, ty, d1, d2) => {
        attempt(s, cut(s, x, ty), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    }
    | Suffices(x, ty, d1, d2) => {
        attempt(s, cut(s, x, ty), s' => {
            attempt(s', swap(s'), s'' => {
                let (s''', r1) = check_demo(s'', d1);
                let (s'''', r2) = check_demo(s''', d2);
                (s'''', merge_reports(r1, r2))
            });
        });
    }
    | TypForm =>
        attempt(s, typ_formation(s), s' => (s', report([], [])))
    | ArrowForm(d1, d2) => 
        attempt(s, arrow_formation(s), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    | Ap(x, ty1, ty2, d1, d2) => {
        attempt(s, ap(s, x, ty1, ty2), s' => {
            let (s'', r1) = check_demo(s', d1);
            let (s''', r2) = check_demo(s'', d2);
            (s''', merge_reports(r1, r2))
        });
    }
    | Given(x, ty, d1, d2) => {
        // first check that the types line up
        let (c, ty_goal) = pair_of_judgment(Result.get_ok(focused(s)));
        switch(ty_goal) {
            | Arrow(_, ty1, _) => 
                let ty_elab = tm_of_surface(c, ty);
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
        }
    }
    | Mp(ty, d1, d2) => {
        let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
        let ty_elab = tm_of_surface(c, ty);
        attempt(s, modus_ponens(s, ty_elab), s' => {
            let (s2, r1) = check_demo(s', d1);
            let (s3, r2) = check_demo(s2, d2);
            // let (s4, r3) = check_demo(s3, d3);
            // let (s5, r4) = check_demo(s4, d4);
            (s3, merge_report_list([r1, r2]))
        });
    }
    | Use(x, ds) => 
        // failwith("todo")
        switch(ds){
        | [] => failwith("impossible")
        | [d] => {
            let (c, _) = pair_of_judgment(Result.get_ok(focused(s)));
            attempt(s, index_of_name(c, x), n => {
                switch(lookup_index(c, n)) {
                | Arrow(_, ty_a, ty_b) when no_x(ty_b, 0) => {
                    attempt(s, modus_ponens(s, ty_a), s' => {
                        let (s2, r1) = check_demo(s', Hyp(x));
                        let (s3, r2) = check_demo(s2, d);
                        (s3, merge_report_list([r1, r2]))
                    })
                }
                | _ => skip_and_error(s, "head isn't an implication")
                }
            })
        }
        | [_d, ... _ds] => failwith("todo")
    }
    | Obvious => {
        attempt_option(typ_formation(s), s' => (s', report([], [])), 
        attempt_option(assumed(s), s' => (s', report([], [])), 
        attempt_option(hyp(s), s' => (s', report([], [])), 
        skip_and_error(s,"not obvious"))))
    }
    }
}

let check_demo_root(root : judgment, d : demo) : demo_check_report = {
    let (s, r) = check_demo(init(root), d);
    assert(verify(s,root));
    r
}
