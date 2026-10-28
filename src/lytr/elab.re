open Lang.Program

let elab_id(t : Language.abstract_term) : string = {
    switch(t) {
    | Hole(_) => failwith("Todo id") // TODO (error)
    | Ident(_, x) => x
    | _ => failwith("Todo idd") // TODO (error)
    }
}

let elab_id_span(t : Language.abstract_span) : string = {
    switch(t) {
    | Empty(_) => failwith("todo ID")
    | Single(_, x, _, _) => elab_id(x)
    | Multiple(_) => failwith("todo ID")
    }
}

let rec elab_term(t : Language.abstract_term) : Lang.Term.surface_tm = {
    switch(t) {
    | Parens(_, t) => elab_term_span(t)
    | Ident(r, x) => SurfaceVar(r, x)
    | Prop(r) => SurfaceProp(r)
    | Type(r) => SurfaceTyp(r)
    | In(_ra, l,_, _, r) => SurfaceIn(elab_term(l), elab_term(r))
    | Ap(_ra, l, _, r) => SurfaceAp(elab_term(l), elab_term(r))
    | Arrow(_ra, _l,_, _, _r) => failwith("todo term")
    | Lambda(_ra, _l, _,_, _r) => failwith("todo term")
    | Hole(_) | Interaction(_) | Colon(_) | Assume(_) | Construct(_) | Commas(_) | Given(_)  => SurfaceNonsense
    }
}

and elab_term_span(t : Language.abstract_span) : Lang.Term.surface_tm = {
    switch(t) {
    | Empty(_) => SurfaceNonsense // TODO (error)
    | Single(_, t, _, _) => elab_term(t)
    | Multiple(_) => SurfaceNonsense // TODO (error)
    }
}

let rec elab_demo(t : Language.abstract_term) : Lang.Demo.demo = {
    switch(t) {
    | Hole(r) => Hole(r)
    | Interaction(r) => Hole(r)
    | Ident(r, x) => HypProp(r, x, Obvious(r))
    | Parens(_, s) => elab_demo_span(s)
    | Ap(r, t1, _, t2) => Use(r, elab_demo(t1), elab_demo(t2))
    | Given(r, x, t, _, d) => Given(r, elab_id_span(x), elab_term_span(t), Obvious(r), elab_demo(d))
    | _ => Nonsense(Language.whole_range(t)) // TODO (error)
    }
}

and elab_demo_span(t : Language.abstract_span) : Lang.Demo.demo = {
    switch(t) {
    | Empty(_, r) => Hole(r)
    | Single(_ss1, t, _ss2, _r) => elab_demo(t)
    | Multiple(_) => failwith("Todo demo") 
    }
}

let elab_entry(t : Language.abstract_term) :  Option.t((string, list(arg_chunk), Lang.Term.surface_tm)) = {
    switch(t) {
    | Hole(_) => None // TODO (error)
    | Colon(_, x, _, _, t) => Some((elab_id(x), [], elab_term(t)))
    | _ => None // TODO (error)
    }
}

let elab_entry_span(t : Language.abstract_span) : Option.t((string, list(arg_chunk), Lang.Term.surface_tm)) = {
    switch(t) {
    | Empty(_) => None 
    | Single(_ss1, t, _ss2, _r) => elab_entry(t)
    | Multiple(_) => None // TODO (error)
    }
}

let elab_signature(t : Language.abstract_term) : surface_signature = {
    switch(t) {
    | Hole(_) => [] // TODO (error)
    | Ident(_) => [] // TODO (error)
    | Colon(_, x, _, _, t) => [(elab_id(x), [], elab_term(t))]
    | Commas(_, first, _, middle, _, last) => List.filter_map(x => x, [elab_entry(first)] @ List.map(elab_entry_span, middle) @ [elab_entry(last)] )
    | _ => [] // TODO (error)
    }
}

let elab_signature_span(t : Language.abstract_span) : surface_signature = {
    switch(t) {
    | Empty(_) => []
    | Single(_ss1, t, _ss2, _r) => elab_signature(t)
    | Multiple(_) => [] // TODO (error)
    }
}

let rec elab_program(t : Language.abstract_term) : surface_program = {
    switch(t) {
    | Hole(_) => Empty // TODO (error)
    | Ident(_) => Empty // TODO (error)
    | Assume(_, sg, demo, _, rest) => Assume(elab_signature_span(sg), elab_demo_span(demo), elab_program(rest))
    | Construct(_, sg, demo, _, rest) => Construct(elab_signature_span(sg), elab_demo_span(demo), elab_program(rest))
    | _ => Empty // TODO (error)
    }
}

// and elab_rest(t : Language.abstract_right_child) : surface_program = {
//     switch(t) {
//     | None => Empty
//     | Some((_, p)) => elab_program(p)
//     }
// }

let elab(t : Language.abstract_span) : surface_program = {
    switch(t) {
    | Empty(_) => Empty 
    | Single(_ss1, t, _ss2, _r) => elab_program(t)
    | Multiple(_) => Empty // TODO (error)
    }
}

// let elab(t : Language.abstract_span) : surface_program = failwith("Todo")