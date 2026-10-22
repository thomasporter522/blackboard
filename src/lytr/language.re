
type token = Token(string);

let string_of_token(t) = switch(t) {
    | Token(s) => s
};

type secondary = 
    | Other
    | Shard(token)

type abstract_term =
    | Hole
    | Secondary(secondary)

and abstract_left_child = Option.t((abstract_term, list(secondary)))
and abstract_right_child = Option.t((list(secondary), abstract_term))

// type concrete_left_child = Option.t((abstract_term, list(secondary)))
// type concrete_right_child = Option.t((list(secondary), abstract_term))

type precedence = Precedence(int); 

let precedence_less_than(p1 : precedence, p2 : precedence) : bool = switch(p1, p2) {
    | (Precedence(p1), Precedence(p2)) => p1 < p2
}

type mixfix_interior = list(string)

type tip = 
    | Precedence(precedence)
    | Uninterested

type mixfix_form = {
    left_tip : tip,
    interior : mixfix_interior,
    right_tip : tip,
    // builder : (concrete_left_child, list(abstract_term), concrete_right_child) => abstract_term,
}

module type Language = {
    type context;
    let is_whitespace_character : char => bool;
    let is_identifier_char : (bool, char) => bool;
    let forms: list(mixfix_form);
    let initial_context : unit => context;
}
