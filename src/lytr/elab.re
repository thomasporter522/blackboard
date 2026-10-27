open Lang.Program

let elab_id(t : Language.abstract_term) : string = {
    switch(t) {
    | Hole(_) => failwith("Todo id") // TODO (error)
    | Ident(x) => x
    | _ => failwith("Todo idd") // TODO (error)
    }
}

let rec elab_term(t : Language.abstract_term) : Lang.Term.surface_tm = {
    switch(t) {
    | Parens(t) => elab_term_span(t)
    | Ident(x) => SurfaceVar(x)
    | Prop => SurfaceProp
    | Type => SurfaceTyp
    | In(l,_, _, r) => SurfaceIn(elab_term(l), elab_term(r))
    | Ap(l, _, r) => SurfaceAp(elab_term(l), elab_term(r))
    | Arrow(l,_, _, r) => failwith("todo term")
    | Lambda(l, _,_, r) => failwith("todo term")
    | Hole(_) | Interaction(_) | Colon(_) | Assume(_) | Commas(_) => SurfaceNonsense
    }
}

and elab_term_span(t : Language.abstract_span) : Lang.Term.surface_tm = {
    switch(t) {
    | Empty(_) => SurfaceNonsense // TODO (error)
    | Single(_, t, _, _) => elab_term(t)
    | Multiple(_) => SurfaceNonsense // TODO (error)
    }
}

let elab_demo(t : Language.abstract_term) : Lang.Demo.demo = {
    switch(t) {
    | Hole(r) => Hole(r)
    | Interaction(r) => Hole(r)
    | Ident(x) => HypProp(x, Obvious)
    | _ => failwith("TODO demo") // TODO (error)
    }
}

let elab_demo_span(t : Language.abstract_span) : Lang.Demo.demo = {
    switch(t) {
    | Empty(_, r) => Hole(r)
    | Single(_ss1, t, _ss2, _r) => elab_demo(t)
    | Multiple(_) => failwith("Todo demo") 
    }
}

let elab_entry(t : Language.abstract_term) :  Option.t((string, list(arg_chunk), Lang.Term.surface_tm)) = {
    switch(t) {
    | Hole(_) => None // TODO (error)
    | Colon(x, _, _, t) => Some((elab_id(x), [], elab_term(t)))
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
    | Colon(x, _, _, t) => [(elab_id(x), [], elab_term(t))]
    | Commas(first, _, middle, _, last) => List.filter_map(x => x, [elab_entry(first)] @ List.map(elab_entry_span, middle) @ [elab_entry(last)] )
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
    | Assume(sg, demo, _, rest) => Assume(elab_signature_span(sg), elab_demo_span(demo), elab_program(rest))
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