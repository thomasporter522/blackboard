
type precedence = Precedence(int); 

let precedence_less_than(p1 : precedence, p2 : precedence) : bool = switch(p1, p2) {
    | (Precedence(p1), Precedence(p2)) => p1 < p2
}

type token = Token(string);


type mixfix_interior = 
    | Final(token)
    | Match(token, mixfix_interior)

type tip = 
    | Precedence(precedence)
    | Uninterested

type mixfix_form = {
    left_tip : tip,
    mixfix_interior,
    right_tip : tip,
}

module Grammar : {
    type t; 
    type tip_state;
    let initial_tip_state : (t, token) => Option.t(tip_state);
    let match_tip_state : (t, tip_state, token) => Option.t(tip_state);
    let final_tip_state : (t, tip_state) => bool;
    let left_tip : (t, tip_state) => tip;
    let right_tip : (t, tip_state) => tip;
} = {
    type t = list(mixfix_form);
    type tip_state = token; // should later track which form we're in
    let initial_tip_state(g : t, t : token) = failwith("todo")
    let final_tip_state(g : t, ms : tip_state) = failwith("todo")
    let match_tip_state(g : t, ms : tip_state, t : token) = failwith("todo")
    let left_tip(g : t, ms : tip_state) = failwith("todo")
    let right_tip(g : t, ms : tip_state) = failwith("todo")
}

type shard = Shard(token)


type match = 
    | Head(token, Grammar.tip_state)
    | Match(match, list(molecule), token, Grammar.tip_state) 

// the type of shards or fully matched forms with interiors (but not necessary left or right children)
and molecule = 
    | TotalMatch(match)
    | Shard(shard)

type concrete_term =
    | Shard(shard)
    | Term(left_child, match, right_child)
and left_child = Option.t((concrete_term, list(shard)))
and right_child = Option.t((list(shard), concrete_term))

let tip_state_of_match(pm : match) = switch(pm) {
    | Head(_t, ms) => ms
    | Match(_pm', _child, _t, ms) => ms
}

type partial_object = 
    | PartialMatch(match)
    | Shard(shard)

type open_term = Shard(shard)

type parse_state =
    | Empty 
    | Snoc(parse_state, partial_object)

let rec unmatch(pm : match) : list(molecule) = switch(pm) {
    | Head(t, _ms) => [Shard(Shard(t))]
    | Match(pm', cts, t, _ms) => unmatch(pm') @ cts @ [Shard(Shard(t))]
}

let unmatch_partial_object(g : Grammar.t, po : partial_object) : list(molecule) = switch(po) {
    | PartialMatch(pm) => 
        if(Grammar.final_tip_state(g, tip_state_of_match(pm))) { [TotalMatch(pm)] } 
        else { unmatch(pm) }
    | Shard(sh) => [Shard(sh)]
}

let rec unmatch_partial_objects(g : Grammar.t, pms : list(partial_object)) : list(molecule) =
    List.concat_map(unmatch_partial_object(g), pms)

let rec unmatch_parse_state(g : Grammar.t, ps : parse_state) : list(molecule) = switch(ps) {
    | Empty => [] 
    | Snoc(ps', po) => unmatch_parse_state(g, ps') @ unmatch_partial_object(g, po)
}

type operate_stack = 
    | Empty 
    | Snoc(operate_stack, left_child, match, list(shard))

// completed, stack, reduct
type operate_state = (list(concrete_term), operate_stack, left_child)

let initial_operate_state : operate_state = ([], Empty, None)


let finalize_shard(sh : shard) : concrete_term = Shard(sh);

let finalize_shards = List.map(finalize_shard)

let rec roll_stack_term(stack : operate_stack, t : concrete_term) : list(concrete_term) = switch(stack) {
    | Empty => [t] 
    | Snoc(stack', lc, m, shards) => roll_stack_term(stack', Term(lc, m, Some((shards, t))))
} 

let roll_stack(stack : operate_stack) : list(concrete_term) = switch(stack) {
    | Empty => [] 
    | Snoc(stack', lc, m, shards) => roll_stack_term(stack', Term(lc, m, None)) @ finalize_shards(shards)
}

// precondition: reduct is Some => Prec vs Prec
let rec operate_step(g : Grammar.t, rs : operate_state, m : molecule) : operate_state = {
    let (_, stack, _) = rs; 
    switch(rs, m) {
    | ((c, Empty, None), Shard(sh), ) => (c @ [Shard(sh)], Empty, None)
    | ((c, Snoc(stack', lc, m, shards), None), Shard(sh)) => (c, Snoc(stack', lc, m, shards @ [sh]), None)
    | ((_, _, Some(_)), Shard(_)) => failwith("precondition violated")
    | ((c, Empty, reduct), TotalMatch(pm)) => (c, Snoc(Empty, None, pm, []), reduct)
    | ((c, Snoc(stack', lc, m', shards), reduct), TotalMatch(tm)) => {

        let stack_tip = Grammar.right_tip(g, tip_state_of_match(m'));
        let molecule_tip = Grammar.left_tip(g, tip_state_of_match(tm));

        let roll() = operate_step(g, (c @ roll_stack(stack), Empty, reduct), m);
        let shift() = (c, Snoc(stack, reduct, tm, []), None);
        let reduce() = switch(reduct) {
            | Some((reduct', shards')) => operate_step(g, (c, stack', Some((Term(lc, m', Some((shards, reduct'))), shards'))), m);
            | None => operate_step(g, (c, stack', Some((Term(lc, m', None), shards))), m);
        }

        switch(stack_tip, molecule_tip) {
            | (Uninterested, Uninterested) => roll()
            | (Precedence(_), Uninterested) => shift()
            | (Uninterested, Precedence(_)) => reduce()
            | (Precedence(p1), Precedence(p2)) when precedence_less_than(p1, p2) => shift()
            | (Precedence(_), Precedence(_)) /* when p1 >= p2 */ => reduce()
        }
    }
    }
}

let finalize_operate_state(rs : operate_state) : list(concrete_term) = {
    let (c, s, lc) = rs; 
    let finalize_left_child(lc : left_child) : list(concrete_term) = switch(lc) {
        | None => [] 
        | Some((t, shards)) => [t, ...finalize_shards(shards)]
    }
    c @ roll_stack(s) @ finalize_left_child(lc)
}

let operate(g : Grammar.t, ms : list(molecule)) : list(concrete_term) = {
    let final_operate_state = List.fold_left(operate_step(g), initial_operate_state, ms);
    finalize_operate_state(final_operate_state)
}

let operate_parse_state(g : Grammar.t, s : parse_state) : list(concrete_term) = {
    let ms = unmatch_parse_state(g, s);
    operate(g, ms)
}

let initial_parse_state : parse_state = Empty


// checks whether any match in s matches t, updating the state if so
let match_matches(g : Grammar.t, pm : match, middle : list(partial_object), t : token) : Option.t(match) = {
    let ms = tip_state_of_match(pm);
    switch(Grammar.match_tip_state(g, ms, t)) {
        | Some(ms') => Some(Match(pm, unmatch_partial_objects(g, middle), t, ms'))
        | None => None
    }
}

// checks whether any partial match in s matches t, updating the state if so
let rec scan_for_match(g : Grammar.t, s : parse_state, middle : list(partial_object), t : token) : Option.t(parse_state) = switch(s) {
    | Empty => None
    | Snoc(s', PartialMatch(pm)) => switch(match_matches(g, pm, middle, t)) {
        | Some(pm') => Some(Snoc(s', PartialMatch(pm')))
        | None => scan_for_match(g, s', [PartialMatch(pm), ...middle], t)
    }
    | Snoc(s', Shard(sh)) => scan_for_match(g, s', [Shard(sh), ...middle], t)
}

let parse_step(g : Grammar.t, s : parse_state, t : token) : parse_state = {
    switch(scan_for_match(g, s, [], t)) {
        | Some(s') => s'
        | None => switch(Grammar.initial_tip_state(g, t)) {
            | Some(ms) => Snoc(s, PartialMatch(Head(t, ms)))
            | None => Snoc(s, Shard(Shard(t)))
        }
    }
}

let concrete_parse(g : Grammar.t, tokens : list(token)) : list(concrete_term) = {
    let final_parse_state = List.fold_left(parse_step(g), initial_parse_state, tokens);
    operate_parse_state(g, final_parse_state)
}