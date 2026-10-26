open Lang.Program


// let elab_demo(t : Language.abstract_span) : Lang.Demo.demo = {
//     failwith("Todo")
// }

// let elab_entry(t : Language.abstract_term) : (string, list(arg_chunk), Lang.Demo.surface_tm) = {
//     switch(t) {
//     | Hole => Empty // TODO (error)
//     | Ident(_) => Empty // TODO (error)
//     | Term(Assume, None, [sg, demo], rest) => Assume(elab_signature_span(sg), elab_demo(demo), elab_rest(rest))
//     | Term(Construct,  None, [sg, demo], rest) => Construct(elab_signature_span(sg), elab_demo(demo), elab_rest(rest))
//     | Term(_) => Empty // TODO (error)
//     }
// }

// let elab_entry_span(t : Language.abstract_span) : Option.t((string, list(arg_chunk), Lang.Demo.surface_tm)) = {
//     switch(t) {
//     | Empty(_) => None 
//     | Single(_ss1, t, _ss2, _r) => Some(elab_entry(t))
//     | Multiple(_) => None // TODO (error)
//     }
// }


// let elab_entry_left(t : Language.abstract_left_child) : list((string, list(arg_chunk), Lang.Demo.surface_tm)) = {
//     switch(t) {
//     | None => []
//     | Some((t, _)) => [elab_entry(t)]
//     }
// }

// let elab_entry_right(t : Language.abstract_right_child) : list((string, list(arg_chunk), Lang.Demo.surface_tm)) = {
//     switch(t) {
//     | None => []
//     | Some((_, t)) => [elab_entry(t)]
//     }
// }

// let elab_signature(t : Language.abstract_term) : surface_signature = {
//     switch(t) {
//     | Hole => [] // TODO (error)
//     | Ident(_) => [] // TODO (error)
//     | Term(Colon, x, [], t) => [(elab_sig_lhs(x), [], elab_term_right(t))]
//     | Term(Commas, first, middle, last) => elab_entry_left(first) @ List.filter_map(elab_entry_span, middle) @ elab_entry_right(last)
//     | Term(_) => [] // TODO (error)
//     }
// }

// let elab_signature_span(t : Language.abstract_span) : surface_signature = {
//     switch(t) {
//     | Empty(_) => []
//     | Single(_ss1, t, _ss2, _r) => elab_signature(t)
//     | Multiple(_) => [] // TODO (error)
//     }
// }


// let rec elab_program(t : Language.abstract_term) : surface_program = {
//     switch(t) {
//     | Hole => Empty // TODO (error)
//     | Ident(_) => Empty // TODO (error)
//     | Term(Assume, None, [sg, demo], rest) => Assume(elab_signature_span(sg), elab_demo(demo), elab_rest(rest))
//     | Term(Construct,  None, [sg, demo], rest) => Construct(elab_signature_span(sg), elab_demo(demo), elab_rest(rest))
//     | Term(_) => Empty // TODO (error)
//     }
// }

// and elab_rest(t : Language.abstract_right_child) : surface_program = {
//     switch(t) {
//     | None => Empty
//     | Some((_, p)) => elab_program(p)
//     }
// }

// let elab(t : Language.abstract_span) : surface_program = {
//     switch(t) {
//     | Empty(_) => Empty 
//     | Single(_ss1, t, _ss2, _r) => elab_program(t)
//     | Multiple(_) => Empty // TODO (error)
//     }
// }

let elab(t : Language.abstract_span) : surface_program = failwith("Todo")