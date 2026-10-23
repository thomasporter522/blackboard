
open Language

module type Grammar = {
    type form_state;
    type form;
    type context;

    let is_whitespace_character : char => bool;
    let max_delimiter_length : int;
    let is_delimiter : string => bool;
    let is_identifier_char : (bool, char) => bool;

    let initial_form_state : token => Option.t(form_state);
    let match_form_state : (form_state, token) => Option.t(form_state);
    let finalize_form_state : form_state => Option.t(form);
    let left_tip : form => tip;
    let right_tip : form => tip;
    let initial_context : unit => context;
    let propagate_context_whitespace : context => context;

    let propagate_context_left_child : (context, form) => context;
    let propagate_context_right_child : (context, form) => context;
    let propagate_context_inner : (context, form) => list(context);
    let abstract_whitespace : (context, list(abstract_term)) => abstract_term;
    let abstract_secondary : (context, secondary) => abstract_term;
    let abstract_term : (context, form, abstract_left_child, list(abstract_term), abstract_right_child) => abstract_term ;
}

module GrammarOfLanguage = (L : Language) : Grammar => {
    let is_whitespace_character(c : char) : bool = L.is_whitespace_character(c);

    module StringSet = Set.Make(String)
    let delimiters_of_form(s : StringSet.t, f : mixfix_form) : StringSet.t = {
        List.fold_left((ss, s) => StringSet.add(s, ss), s, f.interior)
    }

    let delimiters_of_forms(forms : list(mixfix_form)) : StringSet.t = 
        List.fold_left(delimiters_of_form, StringSet.empty, forms)

    let delimiters = delimiters_of_forms(L.forms);

    let max_delimiter_length = {
        let update_max(s : string, max_so_far : int) = max(String.length(s), max_so_far);
        StringSet.fold(update_max, delimiters, -1);
    }

    let is_delimiter(s : string) = StringSet.mem(s, delimiters);

    let is_identifier_char(is_start : bool, c : char) : bool = L.is_identifier_char(is_start, c);

    type possible_state = {
        form_index : int, 
        delimiter_index : int
    };

    type form_state = list(possible_state);

    type form = int; // form index

    type context = L.context;
    
    // could be made more performant with a dictionary
    let initial_form_state(t : token) : Option.t(form_state) = {
        let correct_head(form_index, form) = {
            if(t == Token(List.hd(form.interior))) { Some({form_index, delimiter_index: 0}) } else { None}
        };
        let possibilities = List.filter_map(o => o, List.mapi(correct_head, L.forms));
        if (possibilities == []) { None } else { Some(possibilities) }
    }
    let match_form_state(ms : form_state, t : token) : Option.t(form_state) = {
        let match_possibility(p : possible_state) : Option.t(possible_state) = {
            let form = List.nth(L.forms, p.form_index);
            let next_index = p.delimiter_index + 1; 
            switch(List.nth_opt(form.interior, next_index)) {
                | None => None 
                | Some(t') when t != Token(t') => None
                | Some(_) => Some({form_index: p.form_index, delimiter_index: next_index})
            }
        };
        let possibilities = List.filter_map(match_possibility, ms);
        if (possibilities == []) { None } else { Some(possibilities) }
    }
    let finalize_form_state(ms : form_state) : Option.t(form) = {
        let match_possibility(p : possible_state) : Option.t(possible_state) = {
            let form = List.nth(L.forms, p.form_index);
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
    let left_tip(ms : form) : tip = List.nth(L.forms, ms).left_tip
    let right_tip(ms : form) : tip = List.nth(L.forms, ms).right_tip

    // let initial_context(g : t) = 

    let initial_context() = L.initial_context();
    let propagate_context_whitespace(c : context) : context = failwith("todo")

    let propagate_context_left_child(c : context, f : form) : context = failwith("todo");
    let propagate_context_right_child(c : context, f : form) : context = failwith("todo");
    let propagate_context_inner(c : context, f : form) : list(context) = failwith("todo");

    let abstract_whitespace(c : context, ats : list(abstract_term)) : abstract_term = failwith("todo");
    let abstract_secondary(c : context, s : secondary) : abstract_term = failwith("todo");

    let abstract_term(c : context, f : form, ls : abstract_left_child, ats : list(abstract_term), rc : abstract_right_child) : abstract_term = failwith("todo");
}

let safe_sub(s : string, n1 : int, n2 : int) : string = {
    if(n1 < 0) { failwith("n1 too low " ++ string_of_int(n1) ++ " vs " ++ s) } 
    // else if (n1 >= String.length(s)) { failwith("n1 too high " ++ string_of_int(n1) ++ " vs " ++ s) } 
    else if (n1 + n2 < 0){ failwith("n1 + n2 too low " ++ string_of_int(n1 + n2) ++ " vs " ++ s) } 
    else if (n1 + n2 > String.length(s)) { failwith("n1 + n2 too high "  ++ string_of_int(n1 + n2) ++ " vs " ++ s) } 
    else String.sub(s, n1, n2)
}

module Lexer (G : Grammar) = {
    let split(s : string, n : int) : (string, string) = 
        (safe_sub(s, 0, n), safe_sub(s, n, String.length(s) - n));

    let rec lex_delimiter_length(l : int, s : string) : Option.t((string, string)) = {
        if (l <= 0) { None } 
        else if (l > String.length(s)) { lex_delimiter_length(min(l, String.length(s)), s) }
        else if (G.is_delimiter(safe_sub(s, 0, l))) { 
            Some(split(s, l)) 
        } else { lex_delimiter_length(l-1, s) }
    }

    let lex_delimiter(s : string) : Option.t((string, string)) = {
        let l = G.max_delimiter_length; 
        lex_delimiter_length(l, s)
    }

    let rec lex_identifier(is_start : bool, s : string) : Option.t((string, string)) = {
        if(s == "") { None } else
        if(G.is_identifier_char(is_start, s.[0])) {
            let (s1, s2) = split(s, 1);
            switch(lex_identifier(false, s2)) {
            | Some((s21, s22)) => Some((s1 ++ s21, s22))
            | None => Some((s1, s2))
            }
        } else None
    }

    type lex_info = {
        lex_errors : list((int, int)),
        delimiters : list((int, int))
    }

    let empty_lex_info : lex_info = {
        lex_errors: [], 
        delimiters: []
    }

    let rec lex_index(i : int, s : string) : (list(token), lex_info) = {
        let munch((s1 : string, s2 : string)) : (list(token), lex_info) = {
            let (ts, es) = lex_index(i + String.length(s1), s2);
            ([Token(s1), ...ts], es)
        };
        if(s == "") { ([], empty_lex_info) } else
        if(G.is_whitespace_character(s.[0])) {
            munch(split(s, 1))
        } else {
            // bug: munches "construct" delimiter out of "construction" identifier
            // bug: x-> is lexed as "x-" ">"
            switch(lex_delimiter(s)) {
            | Some((s1, s2)) => {
                let (ts, li) = lex_index(i + String.length(s1), s2);
                let li' = {lex_errors: li.lex_errors, delimiters: [(i, i+ String.length(s1)), ...li.delimiters]};
                ([Token(s1), ...ts], li')
            };
            | None => switch(lex_identifier(true, s)) {
                | Some((s1, s2)) => munch((s1, s2))
                | None => 
                    let (s1, s2) = split(s, 1);
                    let (ts, li) = lex_index(i+1, s2);
                    let li' = {lex_errors: [(i, i+1), ...li.lex_errors], delimiters: li.delimiters};
                    ([Token(s1), ...ts], li')
                }
            }
        }
    }

    let lex(s : string) : (list(token), lex_info) = lex_index(0, s);
    
}

module Parser = (G : Grammar) => {

    type concrete_term = 
        | Whitespace(list(concrete_term))
        | Secondary(secondary)
        | Term(G.form, concrete_left_child, list(concrete_term), concrete_right_child)

    and concrete_left_child = Option.t((concrete_term, list(secondary)))
    and concrete_right_child = Option.t((list(secondary), concrete_term))

    type final_match = 
        | Head(token)
        | Match(final_match, concrete_term, token) 

    type meld = (final_match, G.form)

    and indivisible = 
        | Meld(meld)
        | Secondary(secondary)

    type partial_match = 
        | Head(token, G.form_state)
        | Match(partial_match, list(indivisible), token, G.form_state) 

    let form_state_of_match(pm : partial_match) = switch(pm) {
        | Head(_t, ms) => ms
        | Match(_pm', _child, _t, ms) => ms
    }

    type associate_stack = 
        | Empty 
        | Snoc(associate_stack, concrete_left_child, meld, list(secondary))

    // completed, stack
    type associate_state = (list(concrete_term), associate_stack)

    let initial_associate_state : associate_state = ([], Empty)

    let finalize_secondary(sh : secondary) : concrete_term = Secondary(sh);

    let finalize_secondarys = List.map(finalize_secondary)

    let rec unmatch(pm : partial_match) : list(indivisible) = switch(pm) {
        | Head(t, _) => [Secondary(Shard(t))]
        | Match(pm', cts, t, _) => unmatch(pm') @ cts @ [Secondary(Shard(t))]
    }

    let rec children_of_final_match(m : final_match) : list(concrete_term) = switch(m) {
        | Head(_) => [] 
        | Match(m', t, _) => children_of_final_match(m') @ [t]
    }

    let build_meld(lc : concrete_left_child, m : meld, rc : concrete_right_child) : concrete_term = {
        let (match, gs) = m;
        let inner_children = children_of_final_match(match);
        Term(gs, lc, inner_children, rc)
    }

    let rec roll_stack_term(stack : associate_stack, t : concrete_term) : concrete_term = switch(stack) {
        | Empty => t
        | Snoc(stack', lc, m, secondarys) => 
            let t' = build_meld(lc, m, Some((secondarys, t)));
            roll_stack_term(stack', t')
    } 

    let roll_stack(stack : associate_stack) : list(concrete_term) = switch(stack) {
        | Empty => []
        | Snoc(stack', lc, m, secondarys) => [roll_stack_term(stack', build_meld(lc, m, None))] @ finalize_secondarys(secondarys)
    }

    // precondition: reduct is Some => Prec vs Prec
    // postcondition: reduct is none
    let rec associate_step(rs : associate_state, reduct : concrete_left_child, m : indivisible) : associate_state = {
        let (_, stack) = rs; 
        switch(rs, reduct, m) {
        | ((c, Empty), None, Secondary(sh)) => (c @ [Secondary(sh)], Empty)
        | ((c, Snoc(stack', lc, m, secondarys)), None, Secondary(sh)) => (c, Snoc(stack', lc, m, secondarys @ [sh]))
        | ((_, _), Some(_), Secondary(_)) => failwith("precondition violated")
        | ((_, Empty), Some(_), Meld(_)) => failwith("precondition violated")
        | ((c, Empty), None, Meld(m)) => (c, Snoc(Empty, None, m, []))
        | ((c, Snoc(stack', lc, m1, secondarys)), reduct, Meld(m2)) => 
            let stack_tip = G.right_tip(snd(m1));
            let meld_tip = G.left_tip(snd(m2));

            let roll() = associate_step((c @ roll_stack(stack), Empty), reduct, m);
            let shift() = (c, Snoc(stack, reduct, m2, []));
            let reduce() = switch(reduct) {
                | Some((reduct', secondarys')) => associate_step((c, stack'), Some((build_meld(lc, m1, Some((secondarys, reduct'))), secondarys')), Meld(m2));
                | None => associate_step((c, stack'), Some((build_meld(lc, m1, None), secondarys)), m);
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

    let full_associate_step(rs : associate_state, m : indivisible) : associate_state = associate_step(rs, None, m)

    let finalize_associate_state(rs : associate_state) : concrete_term = {
        let (c, s) = rs; 
        let terms : list(concrete_term) = c @ roll_stack(s);
        Whitespace(terms)
    }

    let associate(ms : list(indivisible)) : concrete_term = {
        let final_associate_state = List.fold_left(full_associate_step, initial_associate_state, ms);
        finalize_associate_state(final_associate_state)
    }

    type partial_meld = 
        | PartialMatch(partial_match)
        | Secondary(secondary)

    type matching_state =
        | Empty 
        | Snoc(matching_state, partial_meld)

    let initial_matching_state : matching_state = Empty

    let rec finalize_match(m : partial_match) : final_match = switch(m) {
        | Head(t, _) => Head(t)
        | Match(m', cts, t, _) => Match(finalize_match(m'), associate(cts), t)
    }

    let finalize_partial_meld(po : partial_meld) : list(indivisible) = switch(po) {
        | PartialMatch(pm) => 
            switch(G.finalize_form_state(form_state_of_match(pm))) {
                | None => unmatch(pm)
                | Some(ts) => [Meld((finalize_match(pm), ts))]
            }
        | Secondary(sh) => [Secondary(sh)]
    }

    let finalize_partial_melds(pms : list(partial_meld)) : list(indivisible) =
        List.concat_map(finalize_partial_meld, pms)

    let rec finalize_matching_state(ps : matching_state) : list(indivisible) = switch(ps) {
        | Empty => [] 
        | Snoc(ps', po) => finalize_matching_state(ps') @ finalize_partial_meld(po)
    }

    let attempt_match(pm : partial_match, middle : list(partial_meld), t : token) : Option.t(partial_match) = {
        let ms = form_state_of_match(pm);
        switch(G.match_form_state(ms, t)) {
            | Some(ms') => Some(Match(pm, finalize_partial_melds(middle), t, ms'))
            | None => None
        }
    }

    let rec scan_for_match(s : matching_state, middle : list(partial_meld), t : token) : Option.t(matching_state) = switch(s) {
        | Empty => None
        | Snoc(s', PartialMatch(pm)) => switch(attempt_match(pm, middle, t)) {
            | Some(pm') => Some(Snoc(s', PartialMatch(pm')))
            | None => scan_for_match(s', [PartialMatch(pm), ...middle], t)
        }
        | Snoc(s', Secondary(sh)) => scan_for_match(s', [Secondary(sh), ...middle], t)
    }

    let matching_step(s : matching_state, t : token) : matching_state = {
        switch(scan_for_match(s, [], t)) {
            | Some(s') => s'
            | None => switch(G.initial_form_state(t)) {
                | Some(ms) => Snoc(s, PartialMatch(Head(t, ms)))
                | None => Snoc(s, Secondary(Shard(t)))
            }
        }
    }

    let match(tokens : list(token)) = {
        let final_matching_state = List.fold_left(matching_step, initial_matching_state, tokens);
        finalize_matching_state(final_matching_state);
    }

    let rec abstract_context(ctx : G.context, c : concrete_term) : abstract_term = switch(c){
        | Whitespace(cts) => {
            let ctx' : G.context = G.propagate_context_whitespace(ctx);
            let ats : list(abstract_term) = List.map(abstract_context(ctx'), cts);
            G.abstract_whitespace(ctx, ats)
        }
        | Secondary(sh) => G.abstract_secondary(ctx, sh)
        | Term(f, lc, cts, rc) => {
            let lctx : G.context = G.propagate_context_left_child(ctx, f);
            let rctx : G.context = G.propagate_context_right_child(ctx, f);
            let lc' = abstract_left_child(lctx, lc);
            let rc' = abstract_right_child(rctx, rc);
            let ctxs : list(G.context) = G.propagate_context_inner(ctx, f);
            let ats' : list(abstract_term) = List.map2(abstract_context, ctxs, cts);
            G.abstract_term(ctx, f, lc', ats', rc');
        }   
    }

    and abstract_left_child(ctx : G.context, lc : concrete_left_child) : abstract_left_child = switch(lc){
        | None => None
        | Some((ct, secondarys)) => Some((abstract_context(ctx, ct), secondarys))
    }

    and abstract_right_child(ctx : G.context, lc : concrete_right_child) : abstract_right_child = switch(lc){
        | None => None
        | Some((secondarys, ct)) => Some((secondarys, abstract_context(ctx, ct)))
    }

    let abstract(t : concrete_term) : abstract_term = abstract_context(G.initial_context(), t)

    let parse(tokens : list(token)) : abstract_term = {
        let indivisibles = match(tokens);
        let concrete_t = associate(indivisibles);
        let abstract_t = abstract(concrete_t);
        abstract_t
    }
}