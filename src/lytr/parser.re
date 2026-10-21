

type token = Token(string);

type shard = Shard(token)

type abstract_term =
    | Shard(shard);

type left_child = Option.t((abstract_term, list(shard)))
type right_child = Option.t((list(shard), abstract_term))

type precedence = Precedence(int); 

let precedence_less_than(p1 : precedence, p2 : precedence) : bool = switch(p1, p2) {
    | (Precedence(p1), Precedence(p2)) => p1 < p2
}

type mixfix_interior = list(token)

type tip = 
    | Precedence(precedence)
    | Uninterested

type mixfix_form = {
    left_tip : tip,
    interior : mixfix_interior,
    right_tip : tip,
    builder : (left_child, list(abstract_term), right_child) => abstract_term,
}

module Grammar : {
    type t; 
    type matching_state;
    type form;
    type context; 
    let initial_matching_state : (t, token) => Option.t(matching_state);
    let match_matching_state : (t, matching_state, token) => Option.t(matching_state);
    let finalize_matching_state : (t, matching_state) => Option.t(form);
    let left_tip : (t, form) => tip;
    let right_tip : (t, form) => tip;
    let build_whitespace : (t, list(abstract_term)) => abstract_term;
    let build : (t, form, left_child, list(abstract_term), right_child) => abstract_term
} = {
    type t = {
        forms: list(mixfix_form),
        whitespace_builder : list(abstract_term) => abstract_term,
    };
    type possible_state = {
        form_index : int, 
        delimiter_index : int
    }
    type context = unit;
    type matching_state = list(possible_state)

    type form = int // form index
    
    // could be made more performant with a dictionary
    let initial_matching_state(g : t, t : token) : Option.t(matching_state) = {
        let correct_head(form_index, form) = {
            if(List.hd(form.interior) == t) { Some({form_index, delimiter_index: 0}) } else { None}
        };
        let possibilities = List.filter_map(o => o, List.mapi(correct_head, g.forms));
        if (possibilities == []) { None } else { Some(possibilities) }
    }
    let match_matching_state(g : t, ms : matching_state, t : token) : Option.t(matching_state) = {
        let match_possibility(p : possible_state) : Option.t(possible_state) = {
            let form = List.nth(g.forms, p.form_index);
            let next_index = p.delimiter_index + 1; 
            switch(List.nth_opt(form.interior, next_index)) {
                | None => None 
                | Some(t') when t != t' => None
                | Some(_) => Some({form_index: p.form_index, delimiter_index: next_index})
            }
        };
        let possibilities = List.filter_map(match_possibility, ms);
        if (possibilities == []) { None } else { Some(possibilities) }
    }
    let finalize_matching_state(g : t, ms : matching_state) : Option.t(form) = {
        let match_possibility(p : possible_state) : Option.t(possible_state) = {
            let form = List.nth(g.forms, p.form_index);
            let next_index = p.delimiter_index + 1; 
            // keep only those possibilities which *don't* have a next delimiter
            switch(List.nth_opt(form.interior, next_index)) {
                | None => Some(p) 
                | Some(_) => None
            }
        };
        let possibilities = List.filter_map(match_possibility, ms);
        switch(possibilities) {
            | [] => None 
            | [p, ..._] => Some(p.form_index) // picks the first one, if ambiguous
        }
    }
    let left_tip(g : t, ms : form) : tip = List.nth(g.forms, ms).left_tip
    let right_tip(g : t, ms : form) : tip = List.nth(g.forms, ms).right_tip

    let build_whitespace(g : t) = g.whitespace_builder
    let build(g : t, fs : form, lc : left_child, inner : list(abstract_term), rc : right_child) : abstract_term = {
        let form = List.nth(g.forms, fs);
        form.builder(lc, inner, rc)
    }
}

type final_match = 
    | Head(token)
    | Match(final_match, abstract_term, token) 

type meld = (final_match, Grammar.form)

and indivisible = 
    | Meld(meld)
    | Shard(shard)

type partial_match = 
    | Head(token, Grammar.matching_state)
    | Match(partial_match, list(indivisible), token, Grammar.matching_state) 


let matching_state_of_match(pm : partial_match) = switch(pm) {
    | Head(_t, ms) => ms
    | Match(_pm', _child, _t, ms) => ms
}

type operate_stack = 
    | Empty 
    | Snoc(operate_stack, left_child, meld, list(shard))

// completed, stack, reduct
type operate_state = (list(abstract_term), operate_stack, left_child)

let initial_operate_state : operate_state = ([], Empty, None)

let finalize_shard(sh : shard) : abstract_term = Shard(sh);

let finalize_shards = List.map(finalize_shard)

let rec unmatch(pm : partial_match) : list(indivisible) = switch(pm) {
    | Head(t, _) => [Shard(Shard(t))]
    | Match(pm', cts, t, _) => unmatch(pm') @ cts @ [Shard(Shard(t))]
}

let rec children_of_final_match(m : final_match) : list(abstract_term) = switch(m) {
    | Head(_) => [] 
    | Match(m', t, _) => children_of_final_match(m') @ [t]
}

let build_meld(g : Grammar.t, lc : left_child, m : meld, rc : right_child) : abstract_term = {
    let (match, gs) = m;
    let inner_children = children_of_final_match(match);
    Grammar.build(g, gs, lc, inner_children, rc)
}

let rec roll_stack_term(g : Grammar.t, stack : operate_stack, t : abstract_term) : abstract_term = switch(stack) {
    | Empty => t
    | Snoc(stack', lc, m, shards) => 
        let t' = build_meld(g, lc, m, Some((shards, t)));
        roll_stack_term(g, stack', t')
} 

let roll_stack(g : Grammar.t, stack : operate_stack) : list(abstract_term) = switch(stack) {
    | Empty => []
    | Snoc(stack', lc, m, shards) => [roll_stack_term(g, stack', build_meld(g, lc, m, None))] @ finalize_shards(shards)
}

// precondition: reduct is Some => Prec vs Prec
// postcondition: reduct is none
let rec operate_step(g : Grammar.t, rs : operate_state, m : indivisible) : operate_state = {
    let (_, stack, _) = rs; 
    switch(rs, m) {
    | ((c, Empty, None), Shard(sh)) => (c @ [Shard(sh)], Empty, None)
    | ((c, Snoc(stack', lc, m, shards), None), Shard(sh)) => (c, Snoc(stack', lc, m, shards @ [sh]), None)
    | ((_, _, Some(_)), Shard(_)) => failwith("precondition violated")
    | ((c, Empty, reduct), Meld(m)) => (c, Snoc(Empty, None, m, []), reduct)
    | ((c, Snoc(stack', lc, m1, shards), reduct), Meld(m2)) => {
        let stack_tip = Grammar.right_tip(g, snd(m1));
        let meld_tip = Grammar.left_tip(g, snd(m2));

        let roll() = operate_step(g, (c @ roll_stack(g, stack), Empty, reduct), m);
        let shift() = (c, Snoc(stack, reduct, m2, []), None);
        let reduce() = switch(reduct) {
            | Some((reduct', shards')) => operate_step(g, (c, stack', Some((build_meld(g, lc, m1, Some((shards, reduct'))), shards'))), Meld(m2));
            | None => operate_step(g, (c, stack', Some((build_meld(g, lc, m1, None), shards))), m);
        }

        switch(stack_tip, meld_tip) {
            | (Uninterested, Uninterested) => roll()
            | (Precedence(_), Uninterested) => shift()
            | (Uninterested, Precedence(_)) => reduce()
            | (Precedence(p1), Precedence(p2)) when precedence_less_than(p1, p2) => shift()
            | (Precedence(_), Precedence(_)) /* when p1 >= p2 */ => reduce()
        }
    }
    }
}

let finalize_operate_state(g : Grammar.t, rs : operate_state) : abstract_term = {
    let (c, s, lc) = rs; 
    assert(lc == None);
    let terms : list(abstract_term) = c @ roll_stack(g, s);
    Grammar.build_whitespace(g, terms)
}


let operate(g : Grammar.t, ms : list(indivisible)) : abstract_term = {
    let final_operate_state = List.fold_left(operate_step(g), initial_operate_state, ms);
    finalize_operate_state(g, final_operate_state)
}

type partial_meld = 
    | PartialMatch(partial_match)
    | Shard(shard)

type parse_state =
    | Empty 
    | Snoc(parse_state, partial_meld)

let initial_parse_state : parse_state = Empty

let rec finalize_match(g : Grammar.t, m : partial_match) : final_match = switch(m) {
    | Head(t, _) => Head(t)
    | Match(m', cts, t, _) => Match(finalize_match(g, m'), operate(g, cts), t)
}

let unmatch_partial_meld(g : Grammar.t, po : partial_meld) : list(indivisible) = switch(po) {
    | PartialMatch(pm) => 
        switch(Grammar.finalize_matching_state(g, matching_state_of_match(pm))) {
            | None => unmatch(pm)
            | Some(ts) => [Meld((finalize_match(g, pm), ts))]
        }
    | Shard(sh) => [Shard(sh)]
}

let unmatch_partial_melds(g : Grammar.t, pms : list(partial_meld)) : list(indivisible) =
    List.concat_map(unmatch_partial_meld(g), pms)

let rec unmatch_parse_state(g : Grammar.t, ps : parse_state) : list(indivisible) = switch(ps) {
    | Empty => [] 
    | Snoc(ps', po) => unmatch_parse_state(g, ps') @ unmatch_partial_meld(g, po)
}

let match_matches(g : Grammar.t, pm : partial_match, middle : list(partial_meld), t : token) : Option.t(partial_match) = {
    let ms = matching_state_of_match(pm);
    switch(Grammar.match_matching_state(g, ms, t)) {
        | Some(ms') => Some(Match(pm, unmatch_partial_melds(g, middle), t, ms'))
        | None => None
    }
}

let rec scan_for_match(g : Grammar.t, s : parse_state, middle : list(partial_meld), t : token) : Option.t(parse_state) = switch(s) {
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
        | None => switch(Grammar.initial_matching_state(g, t)) {
            | Some(ms) => Snoc(s, PartialMatch(Head(t, ms)))
            | None => Snoc(s, Shard(Shard(t)))
        }
    }
}

let operate_parse_state(g : Grammar.t, s : parse_state) : abstract_term = {
    let ms = unmatch_parse_state(g, s);
    operate(g, ms)
}

let parse(g : Grammar.t, tokens : list(token)) : abstract_term = {
    let final_parse_state = List.fold_left(parse_step(g), initial_parse_state, tokens);
    operate_parse_state(g, final_parse_state)
}