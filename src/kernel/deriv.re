open Meta
open Term
open Print

module PartialDerivation : {
    type t; 
    let init : judgment => t;
    let verify : (t, judgment) => bool;
    let complete : t => bool;
    let focused : t => result(judgment, error);

    let skip : t => result(t, error);
    let swap : t => result(t, error);

    let fresh_meta : t => (t, meta)
    let solve_meta : (t, meta, tm) => result(t, error)

    let weaken : (t, tm) => result(t, error);
    let cut : (t, name, tm) => result(t, error);

    let hyp : (t, hyp_index) => result(t, error);
    let in_formation : (t, tm) => result(t, error);
    let prop_formation : t => result(t, error);
    let typ_formation : t => result(t, error);    
    let arrow_formation : t => result(t, error);
    let arrow_introduction : t => result(t, error);
    let arrow_elimination : (t, tele, tm, subst) => result(t, error);
    let ap_formation : t => result(t, error);
} = {
    module MetaSet = Set.Make(Meta);
    
    type t = {
        solved_metas : MetaMap.t(tm),
        unsolved_metas : MetaSet.t,
        skipped : list(judgment),
        focused : list(judgment),
        root : judgment
    }

    let init (j : judgment) : t = {
        solved_metas : MetaMap.empty,
        unsolved_metas : MetaSet.empty,
        skipped : [],
        focused : [j],
        root : j
    }

    let verify (s : t, j : judgment) = {
        s.focused == [] && s.root == j
    }

    let complete (s : t) = {
        s.focused == [] && s.skipped == []
    }

    let focused (s : t) : result(judgment, error) = {
        switch(s.focused) {
            | [h, ..._] => Ok(h)
            | [] => Error("nothing focused")
        }
    }

    let skip (s : t) : result(t, error) = {
        switch(s.focused) {
            | [h, ... t] => Ok({...s,
                skipped: [h, ...s.skipped],
                focused: t,
            })
            | [] => Error("nothing to skip")
        }
    }

    let swap (s : t) : result(t, error) = {
        switch(s.focused) {
            | [h1, h2, ... t] => Ok({...s,
                skipped: s.skipped,
                focused: [h2, h1, ... t],
            })
            | _ => Error("nothing to swap")
        }
    }

    let fresh_meta (s : t) : (t, meta) = {
        let m = Meta.mint(MetaMap.cardinal(s.solved_metas) + MetaSet.cardinal(s.unsolved_metas));
        let s' = {...s,
            unsolved_metas: MetaSet.add(m, s.unsolved_metas),
        };
        (s', m)
    }

    let solve_meta (s : t, m : meta, t : tm) : result(t, error) = {
        try {
            let unsolved_metas = MetaSet.remove(m, s.unsolved_metas);
            let t = solve_meta_tm(s.solved_metas, t);
            if(!MetaSet.mem(m, s.unsolved_metas)) {
                Error("Unknown has already been solved")
            } else if(!contains_only_metas(unsolved_metas, t)) {
                Error("Solution contains unknowns that have already been solved")
            } else {
                let sol = MetaMap.of_list([(m, t)]);
                let solved_metas_updated = MetaMap.map(solve_meta_tm(sol), s.solved_metas);
                let solved_metas = MetaMap.add(m, t, solved_metas_updated);
                let skipped = List.map(solve_meta_judgment(sol), s.skipped);
                let focused = List.map(solve_meta_judgment(sol), s.focused);
                Ok({...s, 
                    solved_metas,
                    unsolved_metas,
                    skipped, 
                    focused,
                })
            }
        } {
        | _ => Error("malformed solution")
        }
    }

    let refine (s : t, f : judgment => result(list(judgment), error)) : result(t, error) = {
        switch(s.focused) {
            | [h, ... t] => 
                Result.map(fh => {...s,
                    focused: fh @ t,
                }, f(h))
            | [] => Error("nothing to refine")
        }
    }

    let weaken (s : t, ty : tm) : result(t, error) = refine(s, j => {
        let ty = solve_meta_tm(s.solved_metas, ty);
        switch(j) {
        | J(Cons(c, _), ty_goal) when equiv(ty_goal, wk(ty)) => Ok([J(c, ty)])
        | _ => Error("weaken failure")
        }
    })

    let cut (s : t, z : name, lemma : tm)  : result(t, error) = refine(s, j => {
        let lemma = solve_meta_tm(s.solved_metas, lemma);
        let J(c, goal) = j;
        Ok([J(c, lemma), J(Cons(c, ConsP(EmptyTele, z, wk(lemma))), wk(goal))])
    })

    let hyp (s : t, i : hyp_index) : result(t, error) = refine(s, j => {
        let J(c, p) = j;
        let* found = lookup_index_prop(c, i);
        if (equiv(found, p)) Ok([]) else Error(
            "hyp failure: " 
            ++ string_of_term(c, found)
            ++ " ≠ "
            ++ string_of_term(c, p)
        )
    })


    let in_formation (s : t, ty2 : tm) : result(t, error) = refine(s, j => {
        let ty2 = solve_meta_tm(s.solved_metas, ty2);
        switch(j) {
        | J(c, In(In(a, ty1), Prop)) => Ok([J(c, In(ty1, Typ)), J(c, In(a, ty2))])
        | J(_, In(In(_), _)) => Error("in_formation failure: not inhabiting prop")
        | J(_, In(_, _)) => Error("in_formation failure: not membership of (_ : _)")
        | _ => Error("in_formation failure")
        }
    })

    let prop_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Prop, Typ)) => Ok([])
        | _ => Error("prop_formation failure")
        }
    })

    let typ_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Typ, Typ)) => Ok([])
        | _ => Error("typ_formation failure")
        }
    })

    let rec valid_tele(c : ctx, te : tele) = switch(te) {
        | EmptyTele => []
        | ConsP(te1, _, p) => valid_tele(c, te1) @ [J(c, In(p, Prop))]
        | ConsT(te1, _, te2, t) => valid_tele(c, te1) @ valid_tele(Cons(c, te2), te2) @ [J(Cons(c, te2), In(t, Typ))]
    }

    let arrow_formation (s : t) : result(t, error) = refine(s, j => {
        let J(c, ty) = j;
        switch(ty) {
        | In(Arrow(te, p), Prop) => Ok(valid_tele(Cons(c, te), te) @ [J(Cons(c, te), In(p, Prop))])
        | _ => Error("arrow_formation failure")
        }
    })

    let arrow_introduction (s : t) : result(t, error) = refine(s, j => {
        let J(c, ty) = j;
        switch(ty) {
        | Arrow(te, p) => Ok(valid_tele(Cons(c, te), te) @ [J(Cons(c, te), p)])
        | _ => Error("arrow_introduction failure")
        }
    })

    let rec subst_tele(c : ctx, s : subst, te : tele) = switch(s, te) {
        | (EmptySubst, EmptyTele) => []
        | (s, ConsP(te', _, p)) => subst_tele(c, s, te') @ [J(c, p)]
        | (ConsSubst(s', _, te1, t), ConsT(te', _, te2, ty)) when equiv_tele(te1, te2) => subst_tele(c, s', te') @ [J(Cons(c, te2), In(t, ty))]
        | _ => failwith("misaligned")
    }

    let arrow_elimination (s : t, te : tele, p : tm, su : subst) : result(t, error) = refine(s, j => {
        let te = solve_meta_tele(s.solved_metas, te);
        let p = solve_meta_tm(s.solved_metas, p);
        let su = solve_meta_subst(s.solved_metas, su);
        let J(c, ty) = j;
        try {
            if(equiv(ty, sub(su, p))) { Ok([J(c, Arrow(te, p))] @ subst_tele(c, su, sub_tele(su, te))) } 
            else { Error("arrow_elimination failure (doesn't match goal)") } 
        } { | _ => Error("arrow_elimination failure (misaligned substitution)") }
    })

    let ap_formation (s : t) : result(t, error) = refine(s, j => {
        let J(c, goal) = j;
        switch(goal) {
        | In(Ap(i, su), ty_expected) => {
            let* (te, ty) = lookup_index_term(c, i);
            try {
                let ty_found = sub(su, ty);
                if (equiv(ty_found, ty_expected))
                    Ok(subst_tele(c, su, sub_tele(su, te)))
                else Error(
                    "ap_formation failure: found = " 
                    ++ string_of_term(c, ty_found)
                    ++ " ≠ "
                    ++ string_of_term(c, ty_expected)
                )
            }  { | _ => Error("ap_formation failure: misaligned substitution")  } 
        } 
        | _ => Error(
            "ap_formation failure: goal = " 
            ++ string_of_term(c, goal)
            ++ " ≠ `_ _ : _`"
        )
        }
    })
}

open PartialDerivation

let goal(s : t) : judgment = Result.get_ok(focused(s));
let goal_tuple(s : t) : (ctx, tm) = {
    let J(c, goal) = goal(s);
    (c, goal)
}

let goal_ctx(s : t) : ctx = ctx_of_judgment(goal(s));
let goal_type(s : t) : tm = type_of_judgment(goal(s));

let string_of_goal_ctx(s : t) = string_of_ctx(goal_ctx(s));
let string_of_goal_type(s : t) = string_of_term(goal_ctx(s), goal_type(s));
let rec string_of_goal_types(s : t) = {
    switch(skip(s)) {
    | Ok(s') => string_of_term(goal_ctx(s), goal_type(s)) ++ {
        switch(skip(s')) {
        | Ok(_) => "\n\n > " ++ string_of_goal_types(s')
        | Error(_) => ""
        }
    }
    | Error(_) => ""
    }
}
