
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

type term_head = 
    | Interaction
    | Parens
    | In 
    | Colon
    | Arrow 
    | Lambda
    | Ap
    | Construct
    | Commas
    | ITE

type abstract_term =
    | Hole
    | Ident(string)
    | Term(term_head, abstract_left_child, list(abstract_span), abstract_right_child)

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

type mixfix_form_of('context) = {
    left_tip : tip,
    interior : mixfix_interior,
    right_tip : tip,
    arity : 'context => ('context, list('context), 'context),
    head : 'context => term_head,
}

type repeater_form_of('context) = {
    left_tip : tip,
    delim : string,
    right_tip : tip,
    arity : 'context => 'context,
    head : 'context => term_head,
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
    let white_head : context => term_head;
    let initial_context : unit => context;
}
