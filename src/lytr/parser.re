open Language
open Grammar

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

    let rec lex_index(i : int, s : string, cursor_position : int) : (list(token), lex_info) = {
        let munch(k : token_kind, (s1 : string, s2 : string)) : (token, list(token), lex_info) = {
            let j = i + String.length(s1);
            let (ts, es) = lex_index(j, s2, cursor_position);
            ({kind: k, s : s1, range : (i, j)}, ts, es)
        };
        let prefix = if(i == cursor_position) { [{kind:Cursor, s:"", range:(i, i)}] } else { [] };
        let (suffix, li) = {
            if(s == "") { ([], empty_lex_info) } else
            if(G.is_whitespace_character(s.[0])) {
                let (t, ts, li) = munch(Whitespace, split(s, 1));
                ([t,...ts], li)
            } else {
                // bug: munches "construct" delimiter out of "construction" identifier
                // bug: x-> is lexed as "x-" ">"
                switch(lex_delimiter(s)) {
                | Some((s1, s2)) => {
                    let (t, ts, li) = munch(Delimiter, (s1, s2));
                    let li' = {lex_errors: li.lex_errors, delimiters: [(i, i+ String.length(s1)), ...li.delimiters]};
                    ([t, ...ts], li')
                };
                | None => switch(lex_identifier(true, s)) {
                    | Some((s1, s2)) => 
                        let (t, ts, li) = munch(Identifier, (s1, s2));
                        ([t,...ts], li)
                    | None => 
                        let (s1, s2) = split(s, 1);
                        let (t, ts, li) = munch(Rune, (s1, s2));
                        let li' = {lex_errors: [(i, i+1), ...li.lex_errors], delimiters: li.delimiters};
                        ([t, ...ts], li')
                    }
                }
            }
        };
        (prefix @ suffix, li)
    }

    let lex(s : string, cursor_position : int) : (list(token), lex_info) = lex_index(0, s, cursor_position);
    
}

module Parser = (G : Grammar) => {

    type error_kind =
        | UnmatchedDelimiter
        | MissingLeftChild 
        | MissingRightChild
        | MissingInnerChild
        | ExtraneousChild
        | Multiple
    
    type error_format = 
        | Underline 
        | Color

    let format_of_error_kind(k) = switch(k) {
        | MissingInnerChild 
        | Multiple => Underline
        | _ => Color
    }

    type error = {
        range : (int, int),
        kind : error_kind,
    }

    type concrete_term = 
        | Term(G.form, ((int, int), (int, int)), concrete_left_child, list(concrete_span), concrete_right_child)

    and concrete_span = 
        | Empty(list(secondary), (int, int))
        | Multiple(list(concrete_term), list(list(secondary)))
        | Single(list(secondary), concrete_term, list(secondary))

    and concrete_left_child = Option.t((concrete_term, list(secondary)))
    and concrete_right_child = Option.t((list(secondary), concrete_term))

    type final_match = 
        | Head(token)
        | Match(final_match, concrete_span, token) 

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

    type associate_shelf_entry = 
        | Secondary(secondary)
        | Term(concrete_term)

    type associate_stack = 
        | Empty 
        | Snoc(associate_stack, concrete_left_child, meld, list(secondary))

    // completed, stack
    type associate_state = (list(associate_shelf_entry), associate_stack)

    let initial_associate_state : associate_state = ([], Empty)

    let finalize_secondary(sh : secondary) : associate_shelf_entry = Secondary(sh);

    let finalize_secondarys = List.map(finalize_secondary)

    type match_result = {
        indivisibles: list(indivisible), 
        errors: list(error),
        completions: list(string)
    };

    let empty_match_result = {
        indivisibles: [], 
        errors: [],
        completions: []
    };


    let rec range_of_multiple_opt(cts : list(concrete_term)) : Option.t((int, int)) = {
        switch(cts) {
        | [] => None
        | [Term(_, ((a, _), (_, b)), _, _, _), ...cts'] => switch(range_of_multiple_opt(cts')){
            | Some((_, b')) => Some((a, b'))
            | None => Some((a, b))
            }
        }
    };

    let range_of_multiple(cts : list(concrete_term)) : (int, int) = {
        switch(range_of_multiple_opt(cts)) {
        | None => failwith("impossible: range_of_multiple")
        | Some(r) => r
        }
    };

    let rec unmatch(pm : partial_match) : (list(indivisible), list(error)) = switch(pm) {
        | Head(t, _) => ([Secondary(Shard(t))], [{range: t.range, kind: UnmatchedDelimiter}])
        | Match(pm', cts, t, _) => 
            let (is, es) = unmatch(pm');
            (is @ cts @ [Secondary(Shard(t))], es @ [{range: t.range, kind: UnmatchedDelimiter}])
    }

    let rec children_of_final_match(m : final_match) : list(concrete_span) = switch(m) {
        | Head(_) => [] 
        | Match(m', t, _) => children_of_final_match(m') @ [t]
    }

    let rec ranges_of_final_match(m : final_match) = switch(m) {
        | Head(t) => (t.range, t.range)
        | Match(m', _, t) => 
            let (r, _) = ranges_of_final_match(m');
            (r, t.range)
    }

    let build_meld(lc : concrete_left_child, m : meld, rc : concrete_right_child) : concrete_term = {
        let (match, gs) = m;
        let inner_children = children_of_final_match(match);
        let ranges = ranges_of_final_match(fst(m));
        Term(gs, ranges, lc, inner_children, rc)
    }

    let rec roll_stack_term(stack : associate_stack, t : concrete_term) : associate_shelf_entry = switch(stack) {
        | Empty => Term(t)
        | Snoc(stack', lc, m, secondarys) => 
            let t' = build_meld(lc, m, Some((secondarys, t)));
            roll_stack_term(stack', t')
    } 

    let roll_stack(stack : associate_stack) : list(associate_shelf_entry) = switch(stack) {
        | Empty => []
        | Snoc(stack', lc, m, secondarys) => [roll_stack_term(stack', build_meld(lc, m, None))] @ finalize_secondarys(secondarys)
    }

    // let white_token(m : meld, ss : list(secondary)) : token = {
    //     if(List.length(ss) > 0) {
    //         let i = List.hd(ss).
    //     }
    // }

    // precondition: reduct is Some => _ vs Prec
    // postcondition: reduct is none
    let rec associate_step(rs : associate_state, reduct : concrete_left_child, m : indivisible) : associate_state = {
        let (_, stack) = rs; 
        switch(rs, reduct, m) {
        // bug: mustn't create multiples if whitespace is an operator
        | ((c, Empty), None, Secondary(sh)) => (c @ [Secondary(sh)], Empty)
        | ((c, Snoc(stack', lc, m, secondarys)), None, Secondary(sh)) => (c, Snoc(stack', lc, m, secondarys @ [sh]))
        | ((_, _), Some(_), Secondary(_)) => failwith("precondition violated (reduct with secondary)")
        | ((c, Empty), Some(lc), Meld(m)) => (c, Snoc(Empty, Some(lc), m, []))
        | ((c, Empty), None, Meld(m)) => (c, Snoc(Empty, None, m, []))
        | ((c, Snoc(stack', lc, m1, secondarys)), reduct, Meld(m2)) => 
            let stack_tip = G.right_tip(snd(m1));
            let meld_tip = G.left_tip(snd(m2));
            let insert_white(wf : G.form) = {
                let rec left_token_of_match(m : final_match) = switch(m) {
                | Head(t) => t 
                | Match(m, _, _) => left_token_of_match(m)
                };
                let m2_range = left_token_of_match(fst(m2)).range;
                let range = (fst(m2_range), snd(m2_range));
                let white_token = {kind: Delimiter, s : "", range};
                let white : indivisible = Meld((Head(white_token), wf));
                associate_step(associate_step(rs, None, white), None, m);
            }
            let roll() = associate_step((c @ roll_stack(stack), Empty), reduct, m)
            let shift() = (c, Snoc(stack, reduct, m2, []));
            let reduce() = switch(reduct) {
                | Some((reduct', secondarys')) => associate_step((c, stack'), Some((build_meld(lc, m1, Some((secondarys, reduct'))), secondarys')), Meld(m2));
                | None => associate_step((c, stack'), Some((build_meld(lc, m1, None), secondarys)), m);
            }

            switch(stack_tip, meld_tip) {
                | (Uninterested, Uninterested) => switch(G.white_form) {
                    | None => roll()
                    | Some(wf) => insert_white(wf)
                }
                | (Precedence(_, _), Uninterested) => shift()
                | (Uninterested, Precedence(_)) => reduce()
                | (Precedence(_, p1), Precedence(_, p2)) when precedence_less_than(p1, p2) => shift()
                | (Precedence(_), Precedence(_)) /* when p1 >= p2 */ => reduce()
            }
        }
    }

    let full_associate_step(rs : associate_state, m : indivisible) : associate_state = associate_step(rs, None, m)


    let rec finalize_shelf_entries(ss : list(secondary), ssr : (int, int), es : list(associate_shelf_entry)) : concrete_span = {
        switch(es) {
        | [] => 
            Empty(ss, ssr)
        | [Secondary(s), ... es'] => 
            let b = switch(s) {
            | Cursor => snd(ssr)
            | Shard(t) | Whitespace(t) | Rune(t) => snd(t.range)
            };
            finalize_shelf_entries(ss @ [s], (fst(ssr), b), es')
        | [Term(t), ... es'] => 
            let a = snd(range_of_multiple([t]));
            switch(finalize_shelf_entries([], (a, a), es')) {
                | Empty(ss2, _) => Single(ss, t, ss2)
                | Multiple(ts, ss2) => Multiple([t] @ ts, [ss] @ ss2)
                | Single(ss1, t2, ss2) => Multiple([t, t2], [ss, ss1, ss2])
            }
        }
    }

    let finalize_associate_state(rs : associate_state, r : (int, int)) : concrete_span = {
        let (c, s) = rs; 
        let entries : list(associate_shelf_entry) = c @ roll_stack(s); 
        finalize_shelf_entries([], r, entries)
    }

    let associate(ms : list(indivisible), r : (int, int)) : concrete_span = {
        let final_associate_state = List.fold_left(full_associate_step, initial_associate_state, ms);
        finalize_associate_state(final_associate_state, r)
    }

    type partial_meld = 
        | PartialMatch(partial_match)
        | Secondary(secondary)

    type matching_stack =
        | Empty 
        | Snoc(matching_stack, partial_meld)

    type matching_state = {
        stack : matching_stack, 
        errors : list(error),
        completions : list(string),
    }

    let initial_matching_state : matching_state = {stack : Empty, errors : [], completions : []}

    let right_face_of_partial_match(pm: partial_match) = switch(pm) {
        | Head(t, _)
        | Match(_, _, t, _) => t
    }

    let rec finalize_match(m : partial_match) : (final_match, list(error)) = switch(m) {
        | Head(t, _) => (Head(t), [])
        | Match(m', cts, t, _) => 
            let inner = associate(cts, (snd(right_face_of_partial_match(m').range), fst(t.range)));
            // let es1 = switch(inner, G.accepts_child(fs)) {
            // | (Empty(_), true) => [{
            //     kind: MissingInnerChild,
            //     range: (snd(right_face_of_partial_match(m').range), fst(t.range))
            // }]
            // | (Single(_,Term(_, ((a, _), (_, b)), _, _, _),_), false) => [{
            //     kind: ExtraneousChild,
            //     range: (a, b)
            // }]
            // | (Multiple(cts, _), false) => [{
            //     kind: ExtraneousChild,
            //     range: range_of_multiple(cts)
            // }]
            // | _ => []
            // };
            let (fm, es2) = finalize_match(m'); 
            (Match(fm, inner, t), es2)
    }

    let finalize_partial_meld(po : partial_meld, checking_completions: bool) : match_result = switch(po) {
        | PartialMatch(pm) => 
            switch(G.finalize_form_state(form_state_of_match(pm))) {
                | Failure(completions) => 
                    let (is, es) = unmatch(pm);
                    {
                        indivisibles: is, 
                        errors: es,
                        completions : checking_completions ? completions() : []
                    }
                | Success(ts) => 
                    let (fm, es) = finalize_match(pm);
                    {
                        indivisibles: [Meld((fm, ts))], 
                        errors: es,
                        completions : []
                    }
            }
        | Secondary(sh) => {
            indivisibles: [Secondary(sh)], 
            errors: [],
            completions : []
        }
    }

    let combine_match_results(m1 : match_result, m2 : match_result) : match_result = {
        {
            indivisibles: m1.indivisibles @ m2.indivisibles, 
            errors: m1.errors @ m2.errors,
            completions : m2.completions @ m1.completions // the completions grow to the right
        }
    }

    let concat_map2(f : 'a => match_result, l : list('a)) : match_result =
        List.fold_left((mr, a) => combine_match_results(mr, f(a)), empty_match_result, l)

    let rec finalize_partial_melds_reversed(pms : list(partial_meld), checking_completions: bool) : match_result = switch(pms) {
        | [] => empty_match_result
        | [pm,...pms'] =>
            let checking_completions' = switch(pm) {
                | Secondary(Cursor) => true 
                | _ => checking_completions
            };
            combine_match_results(finalize_partial_melds_reversed(pms', checking_completions'), finalize_partial_meld(pm, checking_completions'));
        }
        
    let finalize_partial_melds(pms : list(partial_meld)) : match_result = finalize_partial_melds_reversed(List.rev(pms), false)

    let rec finalize_matching_stack(ps : matching_stack, checking_completions: bool) : match_result = switch(ps) {
        | Empty => empty_match_result
        | Snoc(ps', po) => 
            let checking_completions' = switch(po) {
                | Secondary(Cursor) => true 
                | _ => checking_completions
            };
            combine_match_results(finalize_matching_stack(ps', checking_completions'), finalize_partial_meld(po, checking_completions))
    }

    let finalize_matching_state(ps : matching_state) : match_result = {
        let mr = finalize_matching_stack(ps.stack, false);
        {...mr, errors: ps.errors @ mr.errors, completions : ps.completions @ mr.completions}
    }

    let attempt_match(pm : partial_match, middle : list(partial_meld), t : token) : Option.t((partial_match, list(error), list(string))) = {
        let ms = form_state_of_match(pm);
        switch(G.match_form_state(ms, t)) {
            | Some(ms') => 
                let mr = finalize_partial_melds(middle);
                Some((Match(pm, mr.indivisibles, t, ms'), mr.errors, mr.completions))
            | None => None
        }
    }

    let rec scan_for_match(s : matching_stack, middle : list(partial_meld), t : token) : Option.t((matching_stack, list(error), list(string))) = switch(s) {
        | Empty => None
        | Snoc(s', PartialMatch(pm)) => switch(attempt_match(pm, middle, t)) {
            | Some((pm', es, cs)) => Some((Snoc(s', PartialMatch(pm')), es, cs))
            | None => scan_for_match(s', [PartialMatch(pm), ...middle], t)
        }
        | Snoc(s', Secondary(sh)) => scan_for_match(s', [Secondary(sh), ...middle], t)
    }

    let matching_step(s : matching_state, t : token) : matching_state = {
        switch(t.kind) {
        | Cursor => {...s, stack: Snoc(s.stack, Secondary(Cursor))}
        | Whitespace => {...s, stack: Snoc(s.stack, Secondary(Whitespace(t)))}
        | Rune => {...s, stack: Snoc(s.stack, Secondary(Rune(t)))}
        | Identifier 
        | Delimiter => 
            switch(scan_for_match(s.stack, [], t)) {
            | Some((s', rs, cs)) => 
                {stack: s', errors: s.errors @ rs, completions : s.completions @ cs}
            | None => switch(G.initial_form_state(t)) {
                | Some(ms) => {...s, stack: Snoc(s.stack, PartialMatch(Head(t, ms)))}
                | None => {...s, stack: Snoc(s.stack, Secondary(Shard(t))), errors: [{range: t.range, kind:UnmatchedDelimiter}, ...s.errors]}
                }
            }
        }
    }

    let match(tokens : list(token)) : match_result = {
        let final_matching_state = List.fold_left(matching_step, initial_matching_state, tokens);
        let result = finalize_matching_state(final_matching_state);
        result
    }

    let rec abstract_span(ctx : G.context, c : concrete_span) : (abstract_span, list(error))  = switch(c){
        | Empty(ss, r) => (Empty(ss, r), [])
        | Multiple(cts, sss) => 
            let recursive_call = List.map(abstract_term(ctx), cts);
            let (ats, rs) = (List.map(fst, recursive_call), List.map(snd, recursive_call));
            let range = range_of_multiple(cts);
            let e : error = {
                kind: Multiple, 
                range,
            };
            (Multiple(ats, sss, range), List.concat(rs) @ [e])
        | Single(ss1, ct, ss2) => 
            let (at, es) =  abstract_term(ctx, ct);
            (Single(ss1, at, ss2, range_of_multiple([ct])), es)
    }
    
    and abstract_term(ctx : G.context, c : concrete_term) : (abstract_term, list(error)) = switch(c) {
        | Term(f, ranges, lc, cts, rc) => 
            let (lctx, ctxs, rctx) : (G.context, list(G.context), G.context) = G.propagate_context(ctx, f);
            let (lc', eslc) = abstract_left_child(lctx, lc);
            let (rc', esrc) = abstract_right_child(rctx, rc);
            let recursive_call = List.map2(abstract_span, ctxs, cts);
            let (ats', esm) = (List.map(fst, recursive_call), List.map(snd, recursive_call));
            let (at, aesa) = G.abstract_term(ctx, f, lc', ats', rc', (fst(fst(ranges)), snd(snd(ranges))));
            let error_of_abstraction_error(ae : G.abstraction_error): error = {
                switch(ae.kind) {
                | MissingLeftChild => {range: ae.range, kind: MissingLeftChild}
                | MissingRightChild => {range: ae.range, kind: MissingRightChild}
                | MissingInnerChild => {range: ae.range, kind: MissingInnerChild}
                | ExtraneousChild => {range: ae.range, kind: ExtraneousChild}
                }
            };
            let esa = List.map(error_of_abstraction_error, aesa);
            (at, eslc @ List.concat(esm) @ esrc @ esa);
    }

    and abstract_left_child(ctx : G.context, lc : concrete_left_child) : (abstract_left_child, list(error)) = switch(lc){
        | None => (None, [])
        | Some((ct, secondarys)) => 
            let (a, es) = abstract_term(ctx, ct);
            (Some((a, secondarys)), es)
    }

    and abstract_right_child(ctx : G.context, lc : concrete_right_child) : (abstract_right_child, list(error)) = switch(lc){
        | None => (None, [])
        | Some((secondarys, ct)) => 
            let (a, es) = abstract_term(ctx, ct);
            (Some((secondarys, a)), es)
    }

    let abstract(t : concrete_span) : (abstract_span, list(error)) = abstract_span(G.initial_context(), t)

    type parse_info = {
        errors : list(error),
        completions : list(string)
    }

    let empty_parse_info : parse_info = {
        errors: [], 
        completions: [], 
    }

    let parse(tokens : list(token)) : (abstract_span, parse_info) = {
        let match_result = match(tokens);
        let range = switch(List.rev(tokens)) {
            | [] => (0, 0)
            | [last, ..._] => (fst(List.hd(tokens).range), snd(last.range))
        };
        let concrete_t = associate(match_result.indivisibles, range);
        let (abstract_t, abstract_errors) = abstract(concrete_t);
        (abstract_t, {errors: match_result.errors @ abstract_errors, completions : match_result.completions})
    }
}