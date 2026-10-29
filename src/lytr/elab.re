open Lang.Program

type error = Lang.Term.ranged_error;
let err = Lang.Term.err;
let whole_range = Language.whole_range;

let (let*) (f : ('a, list('b)), b : 'a => ('c, list('b))) : ('c, list('b)) = {
    let (a, l1) = f;
    let (c, l2) = b(a);
    (c, l1 @ l2)
}

let elab_id(t : Language.abstract_term) : (Option.t(string), list(error)) = {
    switch(t) {
    | Atom(Hole, r) => (None, [err("Missing name", r)])
    | Atom(Ident(x), _) => (Some(x), [])
    | _ => (None, [err("Invalid name", whole_range(t))])
    }
}

let elab_id_span(t : Language.abstract_span) : (Option.t(string), list(error)) = {
    switch(t) {
    | Empty(_, r) => (None, [err("Missing name", r)])
    | Single(_, x, _, _) => elab_id(x)
    | Multiple([], _, _) => failwith("impossible")
    | Multiple([x,..._], _, r) => 
        let* x' = elab_id(x);
        (x', [err("Multiple names", r)])
    }
}

let rec elab_id_list(t: Language.abstract_term) = switch(t) {
    | Atom(Ident(x), _) => ([x], [])
    | Ap(_, xs1, _, xs2) => 
        let* xs1' = elab_id_list(xs1);
        let* xs2' = elab_id_list(xs2);
        (xs1' @ xs2', [])
    | _ => ([], [err("Invalid variable", whole_range(t))])
}

let rec elab_arrow_lhs(t : Language.abstract_term) : (Option.t((list(string), Lang.Term.surface_tm)), list(error)) = switch(t) {
    | Parens(_, t) => elab_arrow_lhs_span(t)
    | Infix(Colon,_, xs, _, _, t) => 
        let* xs' = elab_id_list(xs);
        let* t' = elab_term(t);
        (Some((xs', t')), [])
    | _ => 
        let* t' = elab_term(t);
        (Some((["_"], t')), [])
}

and elab_arrow_lhs_span(t : Language.abstract_span) : (Option.t((list(string), Lang.Term.surface_tm)), list(error)) = switch(t) {
    | Empty(_) => failwith("impossible")
    | Single(_, t, _, _) => elab_arrow_lhs(t)
    | Multiple(_) => failwith("impossible")
}

and elab_term(t : Language.abstract_term) : (Lang.Term.surface_tm, list(error)) = {
    switch(t) {
    | Parens(_, t) => elab_term_span(t)
    | Atom(Ident(x), r) => (SurfaceVar(r, x), [])
    | Atom(Prop, r) => (SurfaceProp(r), [])
    | Atom(Type, r) => (SurfaceTyp(r), [])
    | Infix(In, _, t1, _, _, t2) => 
        let* t1' = elab_term(t1);
        let* t2' = elab_term(t2);
        (Lang.Term.SurfaceIn(t1', t2'), [])
    | Ap(_, t1, _, t2) => 
        let* t1' = elab_term(t1);
        let* t2' = elab_term(t2);
        (Lang.Term.SurfaceAp(t1', t2'), [])
    | Infix(Arrow,_, t1, _, _, t2) => 
        let* t1' = elab_arrow_lhs(t1);
        let* t2' = elab_term(t2);
        switch(t1') {
        | None => (t2', [])
        | Some((xs, t1'')) => (Lang.Term.SurfaceArrow(Weak, xs, t1'', t2'), [])
        }
    | Infix(Lambda,_, t1, _, _, t2) => 
        let* t1' = elab_arrow_lhs(t1);
        let* t2' = elab_term(t2);
        switch(t1') {
        | None => (t2', [])
        | Some((xs, t1'')) => (Lang.Term.SurfaceLambda(xs, t1'', t2'), [])
        }
    | Atom(Hole,_) 
    | Atom(Interaction,_) 
    | Atom(Check,_) 
    | Infix(Colon, _, _, _, _, _) 
    | Infix(At, _, _, _, _, _) 
    | Assume(_) 
    | Construct(_) 
    | Commas(_) 
    | Given(_) => (SurfaceNonsense, [err("Invalid term", whole_range(t))])
    }
}

and elab_term_span(t : Language.abstract_span) : (Lang.Term.surface_tm, list(error)) = {
    switch(t) {
    | Empty(_, r) => (SurfaceNonsense, [err("Missing term", r)])
    | Single(_, t, _, _) => elab_term(t)
    | Multiple([], _, _) => failwith("impossible")
    | Multiple([t,..._], _, r) => 
        let* t' = elab_term(t);
        (t', [err("Multiple terms", r)])
    }
}

let rec elab_demo(t : Language.abstract_term) : (Lang.Demo.demo, list(error)) = {
    switch(t) {
    | Atom(Hole, r) => (Hole(r), [])
    | Atom(Interaction, r) => (Hole(r), [])
    | Atom(Ident(x), r) => (HypProp(r, x, Obvious(r)), [])
    | Atom(Check,r) => (Tactic(r, Check, []), [])
    | Parens(_, s) => elab_demo_span(s)
    | Ap(r, t1, _, t2) => 
        let* t1' = elab_demo(t1);
        let* t2' = elab_demo(t2);
        (Lang.Demo.Use(r, t1', t2'), [])
    | Given(r, x, ty, _, d) => 
        let* x' = elab_id_span(x);
        let* ty' = elab_term_span(ty);
        let* d' = elab_demo(d);
        switch(x') {
        | None => (d', [])
        | Some(x'') => (Lang.Demo.Given(r, x'', ty', Obvious(r), d'), [])
        }
    | Infix(At, r, t1, _, _, t2) => 
        let* t1' = elab_demo(t1);
        let* t2' = elab_term(t2);
        (Lang.Demo.At(r, t1', t2', Obvious(r)), [])
    | Atom(Prop,_) 
    | Atom(Type,_) 
    | Infix(In, _, _, _, _, _) 
    | Infix(Colon, _, _, _, _, _) 
    | Infix(Arrow, _, _, _, _, _) 
    | Infix(Lambda, _, _, _, _, _) 
    | Assume(_) 
    | Construct(_) 
    | Commas(_) => (Nonsense(whole_range(t)), [err("Invalid demonstration", whole_range(t))])
    }
}

and elab_demo_span(t : Language.abstract_span) : (Lang.Demo.demo, list(error)) = {
    switch(t) {
    | Empty(_, r) => (Hole(r), [])
    | Single(_ss1, t, _ss2, _r) => elab_demo(t)
    | Multiple([], _, _) => failwith("impossible")
    | Multiple([d,..._], _, r) => 
        let* d' = elab_demo(d);
        (d', [err("Multiple demonstrations", r)])
    }
}

let elab_entry(t : Language.abstract_term) :  (Option.t((string, list(arg_chunk), Lang.Term.surface_tm)), list(error)) = {
    switch(t) {
    | Infix(Colon, _, x, _, _, t) => 
        let* x' = elab_id(x);
        let* t' = elab_term(t);
        switch(x') {
        | None => (None, [])
        | Some(x'') => (Some((x'', [], t')), [])
        }
    | _ => (None, [err("Invalid entry", whole_range(t))])
    }
}

let elab_entry_span(t : Language.abstract_span) : (Option.t((string, list(arg_chunk), Lang.Term.surface_tm)), list(error)) = {
    switch(t) {
    | Empty(_) => (None, [])
    | Single(_ss1, t, _ss2, _r) => elab_entry(t)
    | Multiple([], _, _) => failwith("impossible")
    | Multiple([t,..._], _, r) => 
        let* t' = elab_entry(t);
        (t', [err("Multiple entries", r)])
    }
}

let elab_signature(t : Language.abstract_term) : (surface_signature, list(error)) = {
    switch(t) {
    | Atom(Hole, _) => ([], [])
    | Infix(Colon, _, x, _, _, t) => 
        let* x' = elab_id(x);
        let* t' = elab_term(t);
        switch(x') {
        | None => ([], [])
        | Some(x'') => ([(x'', [], t')], [])
        }
    | Commas(_, first, _, middle, _, last) => 
        let middles = List.map(elab_entry_span, middle);
        let (first', first_errors) = elab_entry(first);
        let (last', last_errors) = elab_entry(last);
        let middle_terms = List.map(fst, middles);
        let middle_errors = List.concat_map(snd, middles);
        (List.filter_map(x => x, [first'] @  middle_terms @ [last']), first_errors @ middle_errors @ last_errors)
    | _ => ([], [err("Invalid signature", whole_range(t))])
    }
}

let elab_signature_span(t : Language.abstract_span) : (surface_signature, list(error)) = {
    switch(t) {
    | Empty(_) => ([], [])
    | Single(_ss1, t, _ss2, _r) => elab_signature(t)
    | Multiple([], _, _) => failwith("impossible")
    | Multiple([t,..._], _, r) =>
        let* sg = elab_signature(t);
        (sg, [err("Multiple signatures", r)])
    }
}

let rec elab_program(t : Language.abstract_term) : (surface_program, list(error)) = {
    switch(t) {
    | Atom(Hole, _) 
    | Atom(Interaction, _) => (SurfaceEmpty, [])
    | Assume(r, sg, demo, _, p) => 
        let (sg', es) = elab_signature_span(sg);
        let* demo' =  elab_demo_span(demo);
        let* p' =  elab_program(p);
        (SurfaceAssume(r, es == [], sg',demo', p'), es)
    | Construct(r, sg, demo, _, p) => 
        let (sg', es) = elab_signature_span(sg);
        let* demo' =  elab_demo_span(demo);
        let* p' =  elab_program(p);
        (SurfaceConstruct(r, es == [], sg',demo', p'), es)
    | _ => (SurfaceEmpty, [err("Invalid program", whole_range(t))])
    }
}

// and elab_rest(t : abstract_right_child) : surface_program = {
//     switch(t) {
//     | None => Empty
//     | Some((_, p)) => elab_program(p)
//     }
// }

let elab(t : Language.abstract_span) : (surface_program, list(error)) = {
    switch(t) {
    | Empty(_) => (SurfaceEmpty, [])
    | Single(_ss1, t, _ss2, _r) => elab_program(t)
    | Multiple([], _, _) => failwith("impossible")
    | Multiple([t, ... _], _, r) => 
        let* p = elab_program(t);
        (p, [err("Multiple programs", r)])
    }
}

// let elab(t : abstract_span) : surface_program = failwith("Todo")