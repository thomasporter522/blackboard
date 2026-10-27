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

type abstract_term =
    | Hole(range)
    | Ident(string)
    | Interaction(range)
    | Parens(abstract_span)
    | Prop
    | Type
    | Colon(abstract_term, list(secondary), list(secondary), abstract_term)
    | In(abstract_term, list(secondary), list(secondary), abstract_term)
    | Arrow(abstract_term, list(secondary), list(secondary), abstract_term)
    | Lambda(abstract_term, list(secondary), list(secondary), abstract_term)
    | Assume(abstract_span, abstract_span, list(secondary), abstract_term)
    | Commas(abstract_term, list(secondary), list(abstract_span), list(secondary), abstract_term)
    | Ap(abstract_term, list(secondary), abstract_term)
    // | Term(term_head, abstract_left_child, list(abstract_span), abstract_right_child)

and abstract_span = 
    | Empty(list(secondary), (int, int)) // entire range
    | Single(list(secondary), abstract_term, list(secondary), (int, int)) // range of term
    | Multiple(list(abstract_term), list(list(secondary)), (int, int)) // range of terms

and abstract_left_child = Option.t((abstract_term, list(secondary)))
and abstract_right_child = Option.t((list(secondary), abstract_term))

// type concrete_left_child = Option.t((abstract_term, list(secondary)))
// type concrete_right_child = Option.t((list(secondary), abstract_term))

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
