type range = (int, int)

type token_kind = 
    | Identifier
    | Delimiter
    | Whitespace
    | Rune
    | Cursor

type token = {
    kind : token_kind,
    s : string,
    range : (int, int)
}

type secondary = 
    | Whitespace(token)
    | Rune(token)
    | Shard(token)
    | Cursor

type infix = 
    | Colon
    | In 
    | Arrow 
    | Lambda
    | At

type atom = 
    | Hole 
    | Interaction
    | Ident(string)
    | Prop 
    | Type 
    | Check

type abstract_term =
    | Atom(atom, range)
    | Parens(range, abstract_span)
    | Infix(infix, range, abstract_term, list(secondary), list(secondary), abstract_term)
    | Commas(range, abstract_term, list(secondary), list(abstract_span), list(secondary), abstract_term)
    | Ap(range, abstract_term, list(secondary), abstract_term)
    | Assume(range, abstract_span, abstract_span, list(secondary), abstract_term)
    | Construct(range, abstract_span, abstract_span, list(secondary), abstract_term)
    | Given(range, abstract_span, abstract_span, list(secondary), abstract_term)
    // | Term(term_head, abstract_left_child, list(abstract_span), abstract_right_child)

and abstract_span = 
    | Empty(list(secondary), (int, int)) // entire range
    | Single(list(secondary), abstract_term, list(secondary), (int, int)) // range of term
    | Multiple(list(abstract_term), list(list(secondary)), (int, int)) // range of terms

and abstract_left_child = Option.t((abstract_term, list(secondary)))
and abstract_right_child = Option.t((list(secondary), abstract_term))

// type concrete_left_child = Option.t((abstract_term, list(secondary)))
// type concrete_right_child = Option.t((list(secondary), abstract_term))

let combine_ranges((a, _), (_, b)) = (a, b)

let rec whole_range(a : abstract_term) : range = switch(a) {
    | Parens(r, _) 
    | Atom(_, r) => r
    | Commas(_, t1,_, _, _, t2) 
    | Ap(_, t1, _, t2)
    | Infix(_, _, t1, _, _, t2) => combine_ranges(whole_range(t1), whole_range(t2))
    | Assume(r, _, _, _, t)
    | Construct(r, _, _, _, t) 
    | Given(r, _, _, _, t) => combine_ranges(r, whole_range(t))
}

let rec secondaries_range(ss : list(secondary)) : Option.t(range) = switch(ss) {
    | [] => None
    | [Cursor,... ss] => secondaries_range(ss)
    | [Whitespace(t),... ss]
    | [Shard(t),... ss]
    | [Rune(t),... ss] => switch(secondaries_range(ss)) {
        | None => Some(t.range)
        | Some(r) => Some(combine_ranges(t.range, r))
    }
}

let combine_ranges_optl(o, r2) = switch(o) {
    | None => r2
    | Some(r1) => combine_ranges(r1, r2)
}

let combine_ranges_optr(r1, o) = switch(o) {
    | None => r1
    | Some(r2) => combine_ranges(r1, r2)
}

let range_of_some_lc(c : abstract_left_child) = {
    let (t, ss) = Option.get(c);
    combine_ranges_optr(whole_range(t), secondaries_range(ss))
}

let range_of_some_rc(c : abstract_right_child) = {
    let (ss, t) = Option.get(c);
    combine_ranges_optl(secondaries_range(ss), whole_range(t))
}

type precedence = Precedence(int); 

let precedence_less_than(p1 : precedence, p2 : precedence) : bool = switch(p1, p2) {
    | (Precedence(p1), Precedence(p2)) => p1 < p2
}

type mixfix_interior =
    | Just(string)
    | Child(string, mixfix_interior)
    | Secondary(string, mixfix_interior)

type requirement = 
    | Need 
    | Want 

type tip = 
    | Precedence(requirement, precedence)
    | Uninterested


type builder_type('context) = ('context, abstract_left_child, list(abstract_span), abstract_right_child, range) => abstract_term;

type mixfix_form_of('context) = {
    left_tip : tip,
    interior : mixfix_interior,
    right_tip : tip,
    arity : 'context => ('context, list('context), 'context),
    builder : builder_type('context) ,
}

type repeater_form_of('context) = {
    left_tip : tip,
    delim : string,
    right_tip : tip,
    arity : 'context => 'context,
    builder : builder_type('context) ,
}

type form_of('context) = 
    | Mixfix(mixfix_form_of('context))
    | Repeater(repeater_form_of('context))

module type Language = {
    type context;

    type form = form_of(context);
    let is_whitespace_character : char => bool;
    let is_identifier_char : (bool, char) => bool;
    let forms: list(form);
    let white_precs : Option.t((precedence, precedence));
    let white_arity : context => (context, context);
    let white_builder : (context, abstract_term, list(secondary), abstract_term) => abstract_term;
    let initial_context : unit => context;
}
