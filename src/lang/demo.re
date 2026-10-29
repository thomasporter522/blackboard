open Term
open Lang_printing
open Deriv.PartialDerivation
open Deriv

let probe(s: t) = print_endline("CTX:\n" ++ string_of_goal_ctx(s) ++ "\nGOAL:\n" ++ string_of_goal_type(s));
let probes(s: t) = print_endline("CTX:\n" ++ string_of_goal_ctx(s) ++ "\nGOAL:\n" ++ string_of_goal_types(s));


type schema = 
    | Definition

type tactic = 
    | Check
    | Direct
    | Witness(surface_tm)
    | GivenAll
    | Schema(schema)

type demo = 
    | Hole(range)
    | HypProp(range, name, demo)
    | ElabHypProp(range, int, demo)
    | HypTyp(range, name, demo)
    | ElabHypTyp(range, int, demo)
    | InForm(range, tm, demo, demo)
    | Claim(range, name, surface_tm, demo, demo)
    | Suffices(range, name, surface_tm, demo, demo)
    | PropForm(range)
    | TypForm(range)
    | PropArrowForm(range, name, demo, demo)
    | TypArrowForm(range, name, demo, demo)
    // | ArrowElim(demo)
    | ApTyp(range, name, surface_tm, surface_tm, demo, demo)
    | ElabApTyp(range, name, tm, tm, demo, demo)
    | At(range, demo, surface_tm, demo)
    | ElabAt(range, demo, tm, demo)
    | Given(range, name, surface_tm, demo, demo)
    | ElabGiven(range, name, tm, demo, demo)
    | Use(range, demo, demo)
    | Obvious(range)
    | Tactic(range, tactic, list(demo))
    | Nonsense(range)

and tm_or_demo = 
    | Tm(surface_tm)
    | Demo(demo)

type report = {
    open_goals : list((judgment, (int, int))),
    errors : list(ranged_error)
}

let mk_report (open_goals : list((judgment, (int, int))), errors : list(ranged_error)) : report = {
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


let skip_and_error(s : t, e : ranged_error) : (t, report) {
    let s' = Result.get_ok(skip(s));
    (s', mk_report([], [e]))
}

let skip_and_no_error(s : t) : (t, report) {
    let s' = Result.get_ok(skip(s));
    (s', mk_report([], []))
}

let pure(s : t, x : result(t, error), range : (int, int)) : demo_result = switch(x) {
    | Ok(s') => (s', pure_report)
    | Error(e) => skip_and_error(s, err(e, range))
}

// let simplify(x : demo_result) : result(t, error) =
//     if (snd(x).errors == []) { Ok(fst(x)) } else { Error("Errors:\n" ++ String.concat("\n", snd(x).errors ) )}

let (let-?) = (x: demo_result, f: list(ranged_error) => demo_result): demo_result =>
  if(snd(x).errors == []) { x } else { f(snd(x).errors) }

let (let-+) = (x: demo_result, f: t => demo_result): demo_result =>
  if(snd(x).errors == []) { f(fst(x)) } else { x }

let (let-*) = (x: demo_result, f: t => demo_result): demo_result => {
  let (s, r) = f(fst(x));
  (s, merge_reports(snd(x), r))
}

let (let-&) = (x : (t, result('a, ranged_error)), f : 'a => demo_result) : demo_result => {
    switch(snd(x)) {
    | Ok(a) => f(a)
    | Error(e) => skip_and_error(fst(x), e)
    }
}

let (let-**) = ((x, es) : ('a, list(ranged_error)), f: 'a => demo_result): demo_result => {
  let (t, r) = f(x);
  (t, {open_goals: r.open_goals, errors : r.errors @ es})
}

let rec var_of_surface (c : ctx, x : name) : Result.t(int, error) = switch(c) {
    | Cons(_, y, _) when x == y => Ok(0)
    | Cons(c, _, _) => 
        let* n = var_of_surface(c, x);
        Ok(1+n)
    | Empty => Error("unbound variable: " ++ x)
}

let (let**) (f : ('a, list('b)), b : 'a => ('c, list('b))) : ('c, list('b)) = {
    let (a, l1) = f;
    let (c, l2) = b(a);
    (c, l1 @ l2)
}

let rec tm_of_surface (c : ctx, t : surface_tm) : (tm, list(ranged_error)) = switch(t) {
    | SurfaceProp(_) => (Prop, [])
    | SurfaceTyp(_) => (Typ, [])
    | SurfaceIn(t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(c, t2);
        (In(t1', t2'), [])
    | SurfaceArrow(st, [x,...xs], t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(Cons(c, x, t1'), SurfaceArrow(st, xs, t1, t2));
        (Arrow(st, x, t1', t2'), [])
    | SurfaceArrow(_, [], _, t2) => tm_of_surface(c, t2)
    | SurfaceLambda([x,...xs], t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(Cons(c, x, t1'), SurfaceLambda(xs, t1, t2));
        (Lam(x, t1', t2'), [])
    | SurfaceLambda([], _, t2) => tm_of_surface(c, t2)
    | SimpleArrow(t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(Cons(c, "_", t1'), t2);
        (Arrow(Weak, "_", t1', t2'), [])
    | SurfaceAp(t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(c, t2);
        (Ap(t1', t2'), [])
    | SurfaceVar(r, x) => 
        switch(var_of_surface(c, x)) {
        | Ok(n) =>  (Var(n), [])
        | Error(_) => (FreeVar(x), [err("Unrecognized name", r)])
        }
    | SurfaceUnguard(t) => 
        let** t' = tm_of_surface(c, t);
        (Unguard(t'), [])
    | SurfaceNonsense => (Nonsense, []);
}

let rec find_assumption(c : ctx, ty : tm, n : int) : result (int, error) = {
    switch(lookup_index(c, n)) {
    | Ok(ty') when equiv(ty, ty') => Ok(n)
    | Ok(_) => find_assumption(c, ty, n+1)
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
    | Arrow(st, y, ty1, ty2) => {
        let* ty1' = invert_wkn(n, ty1);
        let* ty2' = invert_wkn(n+1, ty2);
        Ok(Arrow(st, y, ty1', ty2'))
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
    | Ap(a1, a2) => {
        let* a1' = invert_wkn(n, a1);
        let* a2' = invert_wkn(n, a2);
        Ok(Ap(a1', a2'))
    } 
    | Unguard(a) => {
        let* a' = invert_wkn(n, a);
        Ok(Unguard(a'))
    } 
    | FreeVar(x) => Ok(FreeVar(x))
    | Nonsense => Ok(Nonsense)
}

// inverse of wk(_)
let invert_wk(a : tm) : result(tm, error) = invert_wkn(0, a)


let codomain(t : tm) : result(tm, error) = switch(t) {
    | Arrow(_, _, _, t') => invert_wk(t');
    | _ => Error("not an arrow")
}

let rec infer_arrow_typ_of_ap(c, hd_ty: tm, tds: list((surface_tm, demo))) : result((strength, name, tm, tm), error) = {
    switch(tds) {
    | [] => switch(hd_ty) {
        | Arrow(st, x, a, b) => Ok((st, x, a, b))
        | _ => Error("head is not of arrow type")
        }
    | [(a, _), ...other_tds] => {
        Result.bind(infer_arrow_typ_of_ap(c, hd_ty, other_tds), f => {
            let (_, _, _, ty_b) = f;
            let (elab_a, _) = tm_of_surface(c, a);
            switch(subst(elab_a, ty_b)) {
            | Arrow(st, x, a, b) => Ok((st, x, a, b))
            | _ => Error("constituent is not of arrow type")
            }
        })
    }
    }
}

let range_of_demo(d : _) : range = switch(d) {
    | Hole(r) 
    | HypProp(r, _, _) 
    | ElabHypProp(r, _, _) 
    | HypTyp(r, _, _) 
    | ElabHypTyp(r, _, _) 
    | InForm(r, _, _, _) 
    | Claim(r, _, _, _, _) 
    | Suffices(r, _, _, _, _) 
    | PropForm(r) 
    | TypForm(r) 
    | PropArrowForm(r, _, _, _) 
    | TypArrowForm(r, _, _, _) 
    | ApTyp(r, _, _, _, _, _) 
    | ElabApTyp(r, _, _, _, _, _) 
    | At(r, _, _, _) 
    | ElabAt(r, _, _, _) 
    | Given(r, _, _, _, _) 
    | ElabGiven(r, _, _, _, _) 
    | Use(r, _, _) 
    | Obvious(r) 
    | Tactic(r, _, _) 
    | Nonsense(r) => r
}

// infers the type proven by a demo in a context
let rec infer_proven_ty(c : ctx, d : demo) : result(tm, ranged_error) = switch(d) {
    | HypProp(r, x, d) => Result.bind(arrange(index_of_name(c, x), r), n => infer_proven_ty(c, ElabHypProp(r, n, d)))
    | ElabHypProp(r, n, _) => arrange(lookup_index(c, n), r)
    | At(r, d1, a, d2) => {
        let (elab_a, _) = tm_of_surface(c, a);
        infer_proven_ty(c, ElabAt(r, d1, elab_a, d2))
    }
    | ElabAt(r, d, a, _) => {
        Result.bind(infer_proven_ty(c, d), inferred_ty => switch(inferred_ty) {
        | Arrow(_, _, _, ty_b) => Ok(subst(a, ty_b))
        | _ => Error(err("ap of non-arrow", r))
        })
    }
    | Use(r, d1, _) => {
        let* d1_proves = infer_proven_ty(c, d1);
        switch(d1_proves) {
        | Arrow(_, _, _, ty_b) => arrange(invert_wk(ty_b), r)
        | _ => Error(err("use of non-arrow or non-simple arrow", r))
        }
    }
    | _ => Error(err("cannot infer what it proves", range_of_demo(d))) // todo: make this message better
}

// infers the type of a term in a context
let rec infer_typ(c : ctx, a : tm) : result(tm, error) = switch(a) {
    | Prop => Ok(Typ)
    | Typ => Ok(Typ)
    | In(_) => Ok(Prop)
    | Arrow(_, x, ty1, ty2) => 
        let* ty2_typ = infer_typ(Cons(c, x, ty1), ty2);
        Ok(ty2_typ)
    | Lam(x, ty, b) => 
        let* ty_body = infer_typ(Cons(c, x, ty), b);
        Ok(Arrow(Weak, x, ty, ty_body))
    // | Unlam(_, f) => switch(c) {
    //     | Empty => Error("Unlambda has no type in the empty context")
    //     | Cons(c', _, _) => switch(infer_typ(c', f)) {
    //         | Ok(Arrow(_, _, ty_b)) => Ok(ty_b)
    //         | Ok(_) => Error("Unlambda body does not have arrow type")
    //         | Error(e) => Error(e)
    //         }   
    //     }
    | Var(x) => lookup_index(c, x)
    | Ap(a1, a2) => switch(infer_typ(c, a1)) {
        | Ok(Arrow(_, _, _, ty2)) => Ok(subst(a2, ty2))
        | Ok(_) => Error("Applied term does not have arrow type")
        | Error(e) => Error(e)
    }
    | Unguard(a) => switch(infer_typ(c, a)) {
        | Ok(Arrow(_, _, _, ty2)) => invert_wk(ty2)
        | Ok(_) => Error("Unguarded term does not have arrow type")
        | Error(e) => Error(e)
    }
    | FreeVar(_) => Error("Inferring from free var")
    | Nonsense => Error("Inferring from nonsense")
}

// if the focus of [s] is c, x : A |- T, refines to goal c |- T' where wk(T') = T
let weaken_goal(s : t) : result(t, error) = {
    let (_, ty, _) = goal_tuple(s);
    let* ty_inv_wk = invert_wk(ty);
    weaken(s, ty_inv_wk)
}


let mp_ty(s : t, ty1 : tm) : result(t, error) = 
    switch(headnormalize(ty1)) {
    | Arrow(_, _, ty_1, _) => implies_elimination(s, ty_1)
    | _ => Error("Cannot 'at' non-arrow type")
    }

let at_ty(s : t, ty1 : tm, a : tm) : result(t, error) = 
    switch(headnormalize(ty1)) {
    | Arrow(_, x, ty_1, ty_2) => forall_elimination(s, x, ty_1, ty_2, a)
    | _ => Error("Cannot 'at' non-arrow type")
    }

// let rec multi_at_ty(s : t, ty : tm, a_list : list(tm)) : result(t, error) = 
//     switch(a_list) {
//     | [] => Ok(s)
//     | [a, ... a_list'] =>
//         let* ty' = switch(ty) {
//         |  Arrow(_, _, _, ty_2) => Ok(subst(a, ty_2))
//         | _ => Error("too many ats")
//         };
//         let* s = multi_at_ty(s, ty', a_list');
//         at_ty(s, ty, a)
//     }

type unfurl_step = 
    | Forall(tm, t => result(t, error))
    | Implies

let rec unfurl_assumption(s : t, ty : tm, steps : list(unfurl_step)) : result(t, error) = switch(steps) {
    | [] => Ok(s)
    | [Forall(a, checker), ... steps'] => 
        let* (x, ty_1, ty_2) = switch(ty) {
        |  Arrow(_, x, ty_1, ty_2) => Ok((x, ty_1, ty_2))
        | _ => Error("can't unfurl_assumption")
        };
        let* s = unfurl_assumption(s, subst(a, ty_2), steps');
        let* s = forall_elimination(s, x, ty_1, ty_2, a);
        let* s = swap(s);
        let* s = checker(s);
        Ok(s)
    | [Implies, ... steps'] => 
        let* (_, ty_1, ty_2) = switch(ty) {
        |  Arrow(_, x, ty_1, ty_2) => Ok((x, ty_1, ty_2))
        | _ => Error("can't unfurl_assumption")
        };
        let* s = unfurl_assumption(s, wk(ty_2), steps');
        let* s = implies_elimination(s, ty_1);
        Ok(s)
}

// tries to discharge goals of the form `t : T`
let rec check(s : t) : result(t, error) = {
    let (c, ty_goal, m) = goal_tuple(s);
    let* s = switch(m, ty_goal) {
        | (Blue, In(_, Prop)) => power_prop(s)
        | (Blue, In(_, Typ)) => power_typ(s)
        | _ => Ok(s)
    }
    switch(ty_goal) {
        | In(Prop, _) => prop_formation(s)
        | In(Typ, _) => typ_formation(s)
        | In(Arrow(_, x, t1, _), _) => {
            let* s = 
                switch(infer_typ(c, t1)) {
                | Ok(Prop) => prop_arrow_formation(s, x);
                | Ok(Typ) => typ_arrow_formation(s, x);
                | Ok(_) => Error("arrow domain is not a prop or type")
                | Error(e) => Error(e)
                };
            let* s = check(s);
            let* s = check(s);
            Ok(s)
        }
        | In(Var(_), _) => 
            let* s = hyp_typ(s);
            check(s)
        | In(Ap(a1, a2), ty_expected) => {
            switch(infer_typ(c, a1)) {
            | Ok(Arrow(_, x, ty1, ty2)) => {
                switch(ap(s, x, ty1, ty2)) {
                | Ok(s) => 
                    let* s = check(s);
                    let* s = check(s);
                    Ok(s)
                | Error(_) => 
                    let ty_found = subst(a2, ty2);
                    Error("Failure checking: " ++ string_of_term(c, In(Ap(a1, a2), ty_expected)) ++ ". \n" ++ string_of_term(c, ty_found) ++ " \n≠ " ++ string_of_term(c, ty_expected));
                }
            }
            | _ => Error("applying a non-arrow")
            }
        }
        | In(Lam(_), _) => 
            let* s = pi_introduction(s);
            let* s = power_typ(s);
            let* s = check(s);
            let* s = check(s);
            Ok(s)
        | In(In(t, _), _) =>
            let* ty = infer_typ(c, t);
            let* s = in_formation(s, ty);
            let* s = check(s);
            let* s = check(s);
            Ok(s)
        | In(Unguard(a), _) => 
            switch(infer_typ(c, a)) {
            | Ok(Arrow(_, x, ty1, _)) => 
                let* s = guard_elimination(s, x, ty1);
                let* s = obvious(s);
                let* s = check(s);
                Ok(s)
            | _ => Error("unguarding a non-arrow")
            }
        | In(Nonsense, _) => skip(s)
        | In(FreeVar(_), _) => skip(s)
        // | In(_, _) => failwith("MISSING TYPE CHECK CASE")
        | _ => Error("not a type obligation: " ++ string_of_term(c, ty_goal))
    }
}

and obvious(s : t) : result(t, error) = {
    let! _ = assumed(s);
    let! _e = check(s);
    Error(_e)
    // Error("not obvious: " ++ string_of_term(goal_ctx(s), goal_type(s)) ++ "\n" ++ string_of_ctx(goal_ctx(s)));
}

and assumed(s : t) : result (t, error) = {
    let (c, ty_goal, _) = tuple_of_judgment(Result.get_ok(focused(s)));
    let* x = find_assumption(c, ty_goal, 0);
    let* s = hyp_prop(s, x);
    obvious(s);
}

let given(s : t, x) : result(t, error) = {
    let (c, ty_goal, _) = goal_tuple(s);
    switch(headnormalize(ty_goal)) {
    | Arrow(_, _, ty1, _) => 
        switch(infer_typ(c, ty1)) {
        | Ok(Prop) => implies_introduction(s, x)
        | _ => forall_introduction(s, x)
        }
    | _ => Error("not an arrow")
    }
}

let rec givenall(s : t) : result(t, error) = 
    switch(headnormalize(goal_type(s))) {
    | Arrow(_, x, _, _) when x != "_" => {
        let* s = given(s, x);
        let* s = obvious(s);
        givenall(s)
    }
    | _ => Ok(s)
}

let given_type(s : t, x, ty_elab) : result(t, error) = {
    switch(goal_type(s)) {
    | Arrow(_, _, ty1, _) when !equiv(ty_elab, ty1) => 
        Error("Wrong given type (should be " ++ x ++ " : " ++ string_of_term(goal_ctx(s), ty1) ++ ")")
    | _ => given(s, x)
    }
}

// // if the goal is (M : prop) -> (A -> M) -> M, refines to goal A.
// let direct(s : t) : result(t, error) = {
//     let* s = forall_introduction(s, "M");
//     let* s = obvious(s);
//     let* s = implies_introduction(s, "h");
//     let* s = obvious(s);
//     let c = goal_ctx(s);
//     let* target = switch(lookup_index(c, 0)) {
//         | Ok(Arrow(_, _, ty_a, _)) => Ok(ty_a) 
//         | _ => Error("cannot prove directly")
//     };
//     let* s = implies_elimination(s, target);
//     let* s = assumed(s);
//     let* s = weaken_goal(s);
//     let* s = weaken_goal(s);
//     Ok(s)
// }

let empty_direct(s : t) : result(t, error) = {
    switch(goal_type(s)) {
    | Arrow(_, _, Prop, Arrow(_, _, Var(0), Var(1))) => {
        let* s = forall_introduction(s, "M");
        let* s = prop_formation(s);
        let* s = implies_introduction(s, "h");
        let* s = hyp_typ(s);
        let* s = prop_formation(s);
        let* s = hyp_prop(s, 0);
        let* s = hyp_typ(s);
        let* s = prop_formation(s);
        Ok(s)
    }
    | _ => Error("wrong shape for empty_direct")
    }
}

// if the goal is (M : prop) -> ((x : P) -> SIG -> M) -> M, refines to goals P and (M : prop) -> (subst(Var(0), SIG) -> M) -> M.
let better_direct(s : t) : result(t, error) = {
    // print_endline("CTX: " ++ string_of_goal_ctx(s));
    // print_endline("GOALS: " ++ string_of_goal_types(s));
    let* (tyP, rest) = switch(goal_type(s)) {
        | Arrow(Weak, _, Prop, Arrow(Weak, _, Arrow(Weak, _, tyP, rest), Var(1))) => Ok((tyP, rest))
        | _ => Error("wrong goal shape for witness: " ++ string_of_term(goal_ctx(s), goal_type(s)))
    };
    let newgoal = Arrow(Weak, "M", Prop, Arrow(Weak, "h", subst(Var(0), rest), Var(1)));
    // print_endline("NEGOAL: " ++ string_of_term(goal_ctx(s), newgoal));
    let* s = cut(s, "premise2", newgoal);
    let* s = swap(s);
    // let* strP = invert_wk(tyP);
    // print_endline("strP: " ++ string_of_term(goal_ctx(s), tyP));
    let* s = cut(s, "premise1", tyP);
    let* s = weaken_goal(s);
    let* s = swap(s);
    // we now prove the goal using the premises
    let* s = forall_introduction(s, "M");
    let* s = obvious(s);
    let* s = implies_introduction(s, "portal");
    let* s = obvious(s);
    let premise2 = 3;
    let* premise2_ty = lookup_index(goal_ctx(s), premise2);
    // print_endline("CHJECKEOPIOTN: " ++ string_of_term(goal_ctx(s), premise2_ty));
    let checker(s : t) = {
        let* s = hyp_typ(s);
        prop_formation(s)
    };
    let* s = unfurl_assumption(s, premise2_ty, [Forall(Var(1), checker), Implies]);
    let* s = hyp_prop(s, premise2);
    let* s = check(s);
    let portal = 0;
    let* portal_ty = lookup_index(goal_ctx(s), portal);
    let* s = mp_ty(s, portal_ty);
    let* s = hyp_prop(s, portal);
    let* s = check(s);
    let premise1 = 2;
    let* s = hyp_prop(s, premise1);
    let* s = check(s);
    // print_endline("CTX: " ++ string_of_goal_ctx(s));
    // print_endline("GOALS: " ++ string_of_goal_types(s));
    // let* s = check(s);
    // print_endline("GOAL2: " ++ string_of_goal_type(s2));
    // let* s3 = skip(s2);
    // print_endline("GOAL3: " ++ string_of_goal_type(s3));
    // let* s = check(s);
    // let* s = check(s);
    Ok(s)
}


// if the goal is (M : prop) -> ((x : A) -> SIG -> M) -> M, refines to goals a : A and (M : prop) -> (SIG[a/x] -> M) -> M.
let witness(s : t, a : tm) : result(t, error) = {
    let* (tyA, rest) = switch(goal_type(s)) {
        | Arrow(Weak, _, Prop, Arrow(Weak, _, Arrow(Weak, _, tyA, rest), Var(1))) => Ok((tyA, rest))
        | _ => Error("wrong goal shape for witness: " ++ string_of_term(goal_ctx(s), goal_type(s)))
    };
    let newgoal = Arrow(Weak, "M", Prop, Arrow(Weak, "h", subst(wk(a), rest), Var(1)));
    let* s = cut(s, "premise2", newgoal);
    let* s = swap(s);
    let a = wk(a);
    let* s = cut(s, "premise1", In(a, tyA));
    let* s = weaken_goal(s);
    let* s = swap(s);
    let a = wk(a);
    // we now prove the goal using the premises
    let* s = forall_introduction(s, "M");
    let* s = obvious(s);
    let a = wk(a);
    let* s = implies_introduction(s, "portal");
    let* s = obvious(s);
    let a = wk(a);
    let premise2 = 3;
    let* premise2_ty = lookup_index(goal_ctx(s), premise2);
    let checker(s : t) = {
        let* s = hyp_typ(s);
        prop_formation(s)
    };
    let* s = unfurl_assumption(s, premise2_ty, [Forall(Var(1), checker), Implies]);
    let* s = hyp_prop(s, premise2);
    let* s = check(s);
    let portal = 0;
    let* portal_ty = lookup_index(goal_ctx(s), portal);
    let* s = at_ty(s, portal_ty, a);
    let* s = hyp_prop(s, portal);
    let* s = check(s);
    let premise1 = 2;
    let* s = hyp_prop(s, premise1);
    let* s = check(s);
    Ok(s)
}

let rec find_refl(c : ctx, eq : int, current : int) : result(int, error) = {
    try { 
        switch(lookup_index(c, current)) {
        | Ok(Arrow(_, _, Typ, Arrow(_, _, Var(0), 
            Ap(Ap(Ap(Var(eq'), Var(1)), Var(0)), Var(0)))))
            when eq == eq'-2  => Ok(current)
        | _ when current > 0 => find_refl(c, eq, current-1)
        | _ => failwith("out of range")
        } 
    } { | _ => Error("couldn't find refl") }
}

let cooler_definition(s : t) : result(t, error) = {
    let rec dissect_eq_ty(eq_ty : tm) : result((list((name, tm)), (int, tm)), error) = switch(eq_ty) {
        | Ap(Ap(Ap(Var(eq), _), _), body) => Ok(([], (eq, body)))
        | Arrow(_, x, ty1, eq_ty') => {
            let* (args, (eq, body)) = dissect_eq_ty(eq_ty');
            Ok(([(x, ty1), ... args], (eq-1, body)))
        }
        | _ => Error("wrong eq_ty")
    };
    let rec build_witness(args : list((name, tm)), body : tm) = switch(args) {
        | [] => body 
        | [(x, ty), ...args'] => Lam(x, ty, build_witness(args', body))
    }
    switch(goal_type(s)) {
    | Arrow(_, _, Prop, Arrow(_, _, Arrow(Weak, _, _, Arrow(Weak, _, eq_ty, Var(2))), Var(1))) => {
        let* (args, (eq, body)) = dissect_eq_ty(eq_ty);
        let* body = invert_wkn(List.length(args), body);
        let* body = invert_wkn(List.length(args), body);
        let* refl = find_refl(goal_ctx(s), eq-2, eq-2);
        let xwitness = build_witness(args, body);
        let* s = witness(s, xwitness);
        let* s = obvious(s);
        let* s = better_direct(s);
        let* s = givenall(s);
        let refl = refl + List.length(args);
        let* refl_ty = lookup_index(goal_ctx(s), refl);
        let* (ty, body) = switch(goal_type(s)) {
            | Ap(Ap(Ap(_, ty), _), body) => Ok((ty, body))
            | _ => Error("error in definition")
        };
        let* s = unfurl_assumption(s, refl_ty, [Forall(ty, obvious), Forall(body, obvious)]);
        let* s = hyp_prop(s, refl);
        let* s = check(s);
        empty_direct(s)
    }
    | _ => Error("wrong shape for definition")
    }
}

// precondition: the [s.focused] is nonempty
// invariant: the root of returned PD.t is the same as that of [s]
// invariant: the focused of returned PD.t is the tail of that of [s]
let rec check_demo(s : t, d : demo) : (t, report) = 
    switch(d) {
    | Hole(r) =>
        let s' = Result.get_ok(skip(s));
        let j = Result.get_ok(focused(s));
        (s', mk_report([(j, r)], []))
    | HypProp(r, x, d) =>
        let c = goal_ctx(s);
        let-& n = (s, arrange(index_of_name(c, x), r));
        check_demo(s, ElabHypProp(r, n, d))
    | ElabHypProp(r, n, d) => 
        let-& s = (s, arrange(hyp_prop(s, n), r));
        check_demo(s, d)
    | HypTyp(r, x, d) =>
        let c = goal_ctx(s);
        let-& n = (s, arrange(index_of_name(c, x), r));
        check_demo(s, ElabHypTyp(r, n, d))
    | ElabHypTyp(r, n, d) =>
        switch(goal_type(s)) {
        | In(Var(n'), _) when n' == n => 
            let-& s = (s, arrange(hyp_typ(s), r));
            check_demo(s, d)
        | In(Var(_), _) => skip_and_error(s, err("typ-of failure: wrong variable", r))
        | _ => skip_and_error(s, err("typ-of failure: not a variable membership", r))
        }
    | InForm(r, ty, d1, d2) =>
        let-& s = (s, arrange(in_formation(s, ty), r));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    | Claim(r, x, ty, d1, d2) => {
        let c = goal_ctx(s);
        let-** ty_elab = tm_of_surface(c, ty);
        let-& s = (s, arrange(cut(s, x, ty_elab), r)); 
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    }
    | Suffices(r, x, ty, d1, d2) => {
        let c = goal_ctx(s);
        let-** ty_elab = tm_of_surface(c, ty);
        let-& s = (s, arrange(cut(s, x, ty_elab), r)); 
        let-& s = (s, arrange(swap(s), r)); 
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    }
    | PropForm(r) => pure(s, prop_formation(s), r)
    | TypForm(r) => pure(s, typ_formation(s), r)
    | PropArrowForm(r, x, d1, d2) => 
        let-& s = (s, arrange(prop_arrow_formation(s, x), r));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    | TypArrowForm(r, x, d1, d2) => 
        let-& s = (s, arrange(typ_arrow_formation(s, x), r));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    | ApTyp(r, x, ty1, ty2, d1, d2) => {
        let c = goal_ctx(s);
        let-** ty1_elab = tm_of_surface(c, ty1);
        let-** ty2_elab = tm_of_surface(Cons(c, x, ty1_elab), ty2);
        check_demo(s, ElabApTyp(r, x, ty1_elab, ty2_elab, d1, d2))
    }
    | ElabApTyp(r, x, ty1, ty2, d1, d2) => {
        let-& s = (s, arrange(ap(s, x, ty1, ty2), r));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    }
    | At(r, d1, a, d2) => {
        let c = goal_ctx(s);
        let-** a_elab = tm_of_surface(c, a);
        check_demo(s, ElabAt(r, d1, a_elab, d2))
    }
    | ElabAt(r, d1, a, d2) => {
        let c = goal_ctx(s);
        let-& d1_ty = (s, infer_proven_ty(c, d1));
        let-& s = (s, arrange(at_ty(s, d1_ty, a), r));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    }
    | Given(r, x, ty, d1, d2) => {
        let c = goal_ctx(s);
        let-** ty_elab = tm_of_surface(c, ty);
        check_demo(s, ElabGiven(r, x, ty_elab, d1, d2));
    }
    | ElabGiven(r, x, ty_elab, d1, d2) => {
        let-& s = (s, arrange(given_type(s, x, ty_elab), r));
        let-* s = check_demo(s, d1);
        check_demo(s, d2)
    }
    | Use(r, d1, d2) => {
        let c = goal_ctx(s);
        let-& d1_ty = (s, infer_proven_ty(c, d1));
        switch(d1_ty) {
        | Arrow(_, _, ty_1, _)  => {
            let-& s = (s, arrange(implies_elimination(s, ty_1), r));
            let-* s = check_demo(s, d1);
            check_demo(s, d2)
        }
        | _ => skip_and_error(s, err("not an arrow", r)) 
        }
    }
    | Obvious(r) => pure(s, obvious(s), r);
    | Tactic(r, Check, ds) => {
        if(ds != []) {
            skip_and_error(s, err("side conditions not supported yet", r))
        } else {
            pure(s, check(s), r);
        }
    }
    | Tactic(r, Schema(Definition), ds) => {
        if (ds != []) {
            skip_and_error(s, err("side conditions not supported yet", r))
        } else {
            pure(s, cooler_definition(s), r);
        }
    }
    | Tactic(r, Direct, ds) => switch(ds) {
        | [d1] => 
            let-& s = (s, arrange(better_direct(s), r));
            let-* s = check_demo(s, d1);
            pure(s, empty_direct(s), r)
        | [d1, d2] =>
            let-& s = (s, arrange(better_direct(s), r));
            let-* s = check_demo(s, d1);
            check_demo(s, d2)
        | _ => skip_and_error(s, err("wrong number of args to direct", r))
    }
    | Tactic(r, Witness(a), ds) => switch(ds) {
        | [d1, d2] =>
            let c = goal_ctx(s);
            let-** a_elab = tm_of_surface(c, a);
            let-& s = (s, arrange(witness(s, a_elab), r));
            let-* s = check_demo(s, d1);
            check_demo(s, d2)
        | _ => skip_and_error(s, err("wrong number of args to witness", r))
    }
    | Tactic(r, GivenAll, ds) => switch(ds) {
        | [d] => 
            let-& s = (s, arrange(givenall(s), r));
            check_demo(s, d)
            // switch(headnormalize(goal_type(s))) {
            // | Arrow(_, x, _, _) when x != "_" => {
            //     let-& s = (s, given(s, x));
            //     let-* s = check_demo(s, Obvious);
            //     check_demo(s,  Tactic(GivenAll, [d]));
            // }
            // | _ => check_demo(s, d)
            // }
        | _ => skip_and_error(s, err("wrong number of args to givenall", r))
    }
    | Nonsense(_) => skip_and_no_error(s)
}

// and definition(s : t) : result(t, error) = {
//     let (c, ty_goal, _) = goal_tuple(s);
//     switch(ty_goal) {
//     | Arrow(_, _, Prop, Arrow(_, _, Arrow(_, xname, ty, Arrow(_, xeq, Ap(Ap(Ap(Var(eq), ty'), Var(0)), xthing), Var(2))), Var(1))) => {
//             let* str_ty = invert_wk(ty);
//             let* str_ty' = invert_wk(ty');
//             let* str_str_ty' = invert_wk(str_ty');
//             if (equiv(str_ty, str_str_ty')) { 
//                 let* refl = find_refl(c, eq-2, eq-2);
//                 let my_subdemo = Use(ElabAt(ElabHypProp(0, Obvious), xthing, Obvious), ElabAt(ElabAt(ElabHypProp(refl+2, Obvious), wk(ty), Obvious), xthing, Obvious))
//                 let my_demo = ElabGiven("M", Prop, PropForm, ElabGiven("h", Arrow(Weak, xname, ty, Arrow(Weak, xeq, Ap(Ap(Ap(Var(eq), ty'), Var(0)), xthing), Var(2))), Tactic(Check, []), my_subdemo));
//                 simplify(check_demo(s, my_demo))
//             } else { Error("not a definition obligation: the term type does not match the equation type: " ++ string_of_term(c, str_ty) ++ " ≠ " ++ string_of_term(c, str_str_ty')) }
//         }
//     | Arrow(_, m, Prop, Arrow(_, _, Arrow(_, _, _, Arrow(_, _, Ap(Ap(Ap(Var(_), _), Var(0)), _), Var(2))), _)) => Error("not a definition obligation: motive is not " ++ m)
//     | Arrow(_, m, Prop, Arrow(_, _, Arrow(_, _, _, Arrow(_, _, Ap(Ap(Ap(Var(_), _), Var(0)), _), _)), _)) => Error("not a definition obligation: inner motive is not " ++ m)
//     | Arrow(_, _, Prop, Arrow(_, _, Arrow(_, _, _, Arrow(_, _, Ap(Ap(Ap(Var(_), _), _), _), _)), _))  => Error("not a definition obligation: LHS of equation is not the declared object")
//     | Arrow(_, _, Prop, Arrow(_, _, Arrow(_, _, _, Arrow(_, _, _, _)), _)) => Error("not a definition obligation: second component is not an equation")
//     | _ => Error("not a definition obligation: not a construction with two components")
//     }
// }


let check_demo_root(root : judgment, d : demo) : report = {
    let (s, r) = check_demo(init(root), d);
    assert(verify(s,root));
    r
}