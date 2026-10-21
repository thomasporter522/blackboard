
type precedence = Precedence(int); 

let precedence_less_than(p1 : precedence, p2 : precedence) : bool = switch(p1, p2) {
    | (Precedence(p1), Precedence(p2)) => p1 < p2
}

type token = Token(string);

type mixfix_interior = list(token)

type tip = 
    | Precedence(precedence)
    | Uninterested

type mixfix_form = {
    left_tip : tip,
    interior : mixfix_interior,
    right_tip : tip,
}

module Grammar : {
    type t; 
    type tip_state;
    type final_state;
    let initial_tip_state : (t, token) => Option.t(tip_state);
    let match_tip_state : (t, tip_state, token) => Option.t(tip_state);
    let finalize_tip_state : (t, tip_state) => Option.t(final_state);
    let left_tip : (t, final_state) => tip;
    let right_tip : (t, final_state) => tip;
} = {
    type t = {
        forms: list(mixfix_form)
    };
    type possible_state = {
        form_index : int, 
        delimiter_index : int
    }
    type tip_state = list(possible_state)

    type final_state = int // form index
    
    // could be made more performant with a dictionary
    let initial_tip_state(g : t, t : token) : Option.t(tip_state) = {
        let correct_head(form_index, form) = {
            if(List.hd(form.interior) == t) { Some({form_index, delimiter_index: 0}) } else { None}
        };
        let possibilities = List.filter_map(o => o, List.mapi(correct_head, g.forms));
        if (possibilities == []) { None } else { Some(possibilities) }
    }
    let match_tip_state(g : t, ms : tip_state, t : token) : Option.t(tip_state) = {
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
    let finalize_tip_state(g : t, ms : tip_state) : Option.t(final_state) = {
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
    let left_tip(g : t, ms : final_state) : tip = List.nth(g.forms, ms).left_tip
    let right_tip(g : t, ms : final_state) : tip = List.nth(g.forms, ms).right_tip
}

type shard = Shard(token)

type match = 
    | Head(token, Grammar.tip_state)
    | Match(match, list(meldor), token, Grammar.tip_state) 

and meld = (match, Grammar.final_state)

and meldor = 
    | Match(meld)
    | Shard(shard)

type concrete_term =
    | Term(left_child, meld, right_child)
    | Shard(shard)

and left_child = Option.t((concrete_term, list(shard)))
and right_child = Option.t((list(shard), concrete_term))

let tip_state_of_match(pm : match) = switch(pm) {
    | Head(_t, ms) => ms
    | Match(_pm', _child, _t, ms) => ms
}

let update_tip_state_of_match(pm : match, ms) = switch(pm) {
    | Head(t, _) => Head(t, ms)
    | Match(pm', child, t, _) => Match(pm', child, t, ms)
}

type parse_meld = 
    | PartialMatch(match)
    | Shard(shard)

type parse_state =
    | Empty 
    | Snoc(parse_state, parse_meld)

let initial_parse_state : parse_state = Empty

let rec unmatch(pm : match) : list(meldor) = switch(pm) {
    | Head(t, _ms) => [Shard(Shard(t))]
    | Match(pm', cts, t, _ms) => unmatch(pm') @ cts @ [Shard(Shard(t))]
}

let unmatch_parse_meld(g : Grammar.t, po : parse_meld) : list(meldor) = switch(po) {
    | PartialMatch(pm) => 
        switch(Grammar.finalize_tip_state(g, tip_state_of_match(pm))) {
            | None => unmatch(pm)
            | Some(ts) => [Match((pm, ts))]
        }
    | Shard(sh) => [Shard(sh)]
}

let rec unmatch_parse_melds(g : Grammar.t, pms : list(parse_meld)) : list(meldor) =
    List.concat_map(unmatch_parse_meld(g), pms)

let rec unmatch_parse_state(g : Grammar.t, ps : parse_state) : list(meldor) = switch(ps) {
    | Empty => [] 
    | Snoc(ps', po) => unmatch_parse_state(g, ps') @ unmatch_parse_meld(g, po)
}

let match_matches(g : Grammar.t, pm : match, middle : list(parse_meld), t : token) : Option.t(match) = {
    let ms = tip_state_of_match(pm);
    switch(Grammar.match_tip_state(g, ms, t)) {
        | Some(ms') => Some(Match(pm, unmatch_parse_melds(g, middle), t, ms'))
        | None => None
    }
}

let rec scan_for_match(g : Grammar.t, s : parse_state, middle : list(parse_meld), t : token) : Option.t(parse_state) = switch(s) {
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


type operate_stack = 
    | Empty 
    | Snoc(operate_stack, left_child, meld, list(shard))

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
let rec operate_step(g : Grammar.t, rs : operate_state, m : meldor) : operate_state = {
    let (_, stack, _) = rs; 
    switch(rs, m) {
    | ((c, Empty, None), Shard(sh)) => (c @ [Shard(sh)], Empty, None)
    | ((c, Snoc(stack', lc, m, shards), None), Shard(sh)) => (c, Snoc(stack', lc, m, shards @ [sh]), None)
    | ((_, _, Some(_)), Shard(_)) => failwith("precondition violated")
    | ((c, Empty, reduct), Match(m)) => (c, Snoc(Empty, None, m, []), reduct)
    | ((c, Snoc(stack', lc, m1, shards), reduct), Match(m2)) => {
        let stack_tip = Grammar.right_tip(g, snd(m1));
        let meld_tip = Grammar.left_tip(g, snd(m2));

        let roll() = operate_step(g, (c @ roll_stack(stack), Empty, reduct), m);
        let shift() = (c, Snoc(stack, reduct, m2, []), None);
        let reduce() = switch(reduct) {
            | Some((reduct', shards')) => operate_step(g, (c, stack', Some((Term(lc, m1, Some((shards, reduct'))), shards'))), Match(m2));
            | None => operate_step(g, (c, stack', Some((Term(lc, m1, None), shards))), m);
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

let finalize_operate_state(rs : operate_state) : list(concrete_term) = {
    let (c, s, lc) = rs; 
    let finalize_left_child(lc : left_child) : list(concrete_term) = switch(lc) {
        | None => [] 
        | Some((t, shards)) => [t, ...finalize_shards(shards)]
    }
    c @ roll_stack(s) @ finalize_left_child(lc)
}

let operate(g : Grammar.t, ms : list(meldor)) : list(concrete_term) = {
    let final_operate_state = List.fold_left(operate_step(g), initial_operate_state, ms);
    finalize_operate_state(final_operate_state)
}

let operate_parse_state(g : Grammar.t, s : parse_state) : list(concrete_term) = {
    let ms = unmatch_parse_state(g, s);
    operate(g, ms)
}

let concrete_parse(g : Grammar.t, tokens : list(token)) : list(concrete_term) = {
    let final_parse_state = List.fold_left(parse_step(g), initial_parse_state, tokens);
    operate_parse_state(g, final_parse_state)
}