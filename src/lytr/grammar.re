open Language

module type Grammar = {
    type form_state;
    type form;
    type context;

    type abstraction_error_kind = 
        | MissingLeftChild
        | MissingRightChild
        | MissingInnerChild
        | ExtraneousChild

    type abstraction_error = {
        kind : abstraction_error_kind, 
        range : (int, int)
    }

    let is_whitespace_character : char => bool;
    let max_delimiter_length : int;
    let is_delimiter : string => bool;
    let is_identifier_char : (bool, char) => bool;

    let initial_form_state : token => Option.t(form_state);
    let match_form_state : (form_state, token) => Option.t(form_state);
    type finalize_result = 
        | Success(form)
        | Failure(unit => list(string))
    let finalize_form_state : form_state => finalize_result;
    let white_form : Option.t(form);
    let left_tip : form => tip;
    let right_tip : form => tip;
    let initial_context : unit => context;

    let propagate_context: (context, form) => (context, list(context), context);
    let abstract_term : (context, form, abstract_left_child, list(abstract_span), abstract_right_child, (int, int)) => (abstract_term, list(abstraction_error)) ;
}

module GrammarOfLanguage = (L : Language) : Grammar => {

    type abstraction_error_kind = 
        | MissingLeftChild
        | MissingRightChild
        | MissingInnerChild
        | ExtraneousChild

    type abstraction_error = {
        kind : abstraction_error_kind, 
        range : (int, int)
    }

    let is_whitespace_character(c : char) : bool = L.is_whitespace_character(c);

    let rec list_of_interior(i) = switch(i) {
        | Just(s) => [s]
        | Child(s, i) 
        | Secondary(s, i) => [s] @ list_of_interior(i)
    }

    module StringSet = Set.Make(String)
    let delimiters_of_form(s : StringSet.t, f : L.form) : StringSet.t = {
        switch(f) {
            | Mixfix(mf) => List.fold_left((ss, s) => StringSet.add(s, ss), s, list_of_interior(mf.interior))
            | Repeater(rf) => StringSet.add(rf.delim, s)
        }
        
    }

    let delimiters_of_forms(forms : list(L.form)) : StringSet.t = 
        List.fold_left(delimiters_of_form, StringSet.empty, forms)

    let delimiters = delimiters_of_forms(L.forms);

    let max_delimiter_length = {
        let update_max(s : string, max_so_far : int) = max(String.length(s), max_so_far);
        StringSet.fold(update_max, delimiters, -1);
    }

    let is_delimiter(s : string) = StringSet.mem(s, delimiters);

    let is_identifier_char(is_start : bool, c : char) : bool = L.is_identifier_char(is_start, c);

    type possible_state = {
        form : L.form, 
        delimiter_index : int
    };

    type form_state = 
        | Delim(list(possible_state))
        | Ident(string);

    type form = 
        | Mixfix(mixfix_form_of(L.context)) // form index
        | Repeater(repeater_form_of(L.context), int) // form index, length
        | Ident(string)
        | White; 

    type context = L.context;
    
    // could be made more performant with a dictionary
    let initial_form_state(t : token) : Option.t(form_state) = {
        let correct_head(form : L.form) = {
            switch(form) {
            | Mixfix(mf) when t.s == List.hd(list_of_interior(mf.interior)) => Some({form, delimiter_index: 0})
            | Repeater(rf) when t.s == rf.delim => Some({form, delimiter_index: 0})
            | _ => None
            }
        };
        let possibilities = List.filter_map(o => o, List.map(correct_head, L.forms));
        if (possibilities != []) { Some(Delim(possibilities)) } 
        else if (t.kind == Identifier) { Some(Ident(t.s)) }
        else { None }
    }
    let match_form_state(ms : form_state, t : token) : Option.t(form_state) = {
        let match_possibility(p : possible_state) : Option.t(possible_state) = {
            switch(p.form) {
            | Mixfix(mf) => 
                let next_index = p.delimiter_index + 1; 
                switch(List.nth_opt(list_of_interior(mf.interior), next_index)) {
                    | None => None 
                    | Some(t') when t.s != t' => None
                    | Some(_) => Some({form: p.form, delimiter_index: next_index})
                }
            | Repeater(rf) when t.s == rf.delim => Some({form: p.form, delimiter_index: p.delimiter_index + 1})
            | Repeater(_) => None
            }
            
        };
        switch(ms) {
        | Ident(_) => None 
        | Delim(ps) => 
            let possibilities = List.filter_map(match_possibility, ps);
            if (possibilities == []) { None } else { Some(Delim(possibilities)) }
        }
    }

    type finalize_result = 
        | Success(form)
        | Failure(unit => list(string))

    let finalize_form_state(ms : form_state) : finalize_result = {
        let match_possibility(p : possible_state) : Option.t(form) = {
            switch(p.form) {
            | Mixfix(mf) => 
                let next_index = p.delimiter_index + 1; 
                // keep only those possibilities which *don't* have a next delimiter
                switch(List.nth_opt(list_of_interior(mf.interior), next_index)) {
                    | None => Some(Mixfix(mf))
                    | Some(_) => None
                }
            | Repeater(rf) => Some(Repeater(rf, p.delimiter_index+1))
            }
        };
        let rec ntail(n : int, l : list('a)) : list('a) = {
            if(l == []) { [] } else 
            if(n <= 0) { l } else ntail(n-1, List.tl(l)) 
        };
        let get_completions(ps : list(possible_state), _ : unit) : list(string) = {
            if(ps == []) { failwith("impossible get_completions") } else {
                let p = List.hd(ps);
                switch(p.form) {
                | Mixfix(mf) => ntail(p.delimiter_index+1, list_of_interior(mf.interior))
                | Repeater(_) => []
                }
            }
        };
        switch(ms) {
        | Ident(s) => Success(Ident(s)) 
        | Delim(ps) => 
            let possibilities = List.filter_map(match_possibility, ps);
            switch(possibilities) {
            | [] => Failure(get_completions(ps))
            | [p, ..._] => Success(p) // picks the first one, if ambiguous
            }
        }
    }

    let white_form : Option.t(form) = if (L.white_precs == None) { None } else { Some(White) };
    let left_tip(ms : form) : tip = switch(ms) {
        | Mixfix(mf) => mf.left_tip
        | Repeater(rf, _) => rf.left_tip
        | Ident(_) => Uninterested
        | White => Precedence(Need,fst(Option.get(L.white_precs)))
    }
    let right_tip(ms : form) : tip = switch(ms) {
        | Mixfix(mf) => mf.right_tip
        | Repeater(rf, _) => rf.right_tip
        | Ident(_) => Uninterested
        | White => Precedence(Need,snd(Option.get(L.white_precs)))
    }

    let initial_context() = L.initial_context();

    let propagate_context(c : context, f : form) : (context, list(context), context) = switch(f) {
        | Mixfix(mf) => mf.arity(c);
        | Repeater(rf, l) => 
            let c' = rf.arity(c);
            (c', List.init(l-1, _ => c') , c')
        | Ident(_) => 
            let (c1, c2) = L.white_arity(c);
            (c1, [], c2)
        | White => 
            let (c1, c2) = L.white_arity(c);
            (c1, [], c2)
    }

    let needs_outer_children(f : form) : (bool, bool) = {
        let h(t : tip) : bool = switch(t) {
            | Precedence(Need, _) => true 
            | _ => false 
        };
        switch(f) {
        | White => (true, true)
        | Ident(_) => (false, false)
        | Repeater(rf, _) => (h(rf.left_tip), h(rf.right_tip))
        | Mixfix(mf) => (h(mf.left_tip), h(mf.right_tip))
        }
    }

    let rec needs_inner_children_mixfix(n : mixfix_interior, i : int) : bool = switch(n) {
        | Child(_) when i == 0 => true 
        | Secondary(_) when i == 0 => false
        | Child(_, n)
        | Secondary(_, n) => needs_inner_children_mixfix(n, i-1) 
        | Just(_) => failwith("impossible: needs_inner_children_mixfix")
    }

    let needs_inner_children(f : form, i : int) : bool = switch(f) {
        | Mixfix(mf) => needs_inner_children_mixfix(mf.interior, i)
        | Repeater(_) => true
        | Ident(_) | White => failwith("impossible: needs_inner_children")
    }

    let abstract_term(c : context, f : form, lc : abstract_left_child, ats : list(abstract_span), rc : abstract_right_child, range: (int, int)) : (abstract_term, list(abstraction_error)) = {
        switch(f) {
        | Ident(s) => (Ident(range, s), [])
        | _ => {
            let (b1, b2) = needs_outer_children(f);
            let (lc', rs1) = switch(lc) {
                | None => b1 ? (Some((Hole((fst(range), fst(range))), [])), [{kind: MissingLeftChild, range: (fst(range), fst(range))}]) : (None, [])
                | Some(_) => (lc, [])
            };
            let (rc', rs2) = switch(rc) {
                | None => b2 ? (Some(([], Hole((snd(range), snd(range))))), [{kind: MissingRightChild, range: (snd(range), snd(range))}]) : (None, [])
                | Some(_) => (rc, [])
            };
            let (ats', rs3, _) = List.fold_left({
                ((acc_ats, acc_rs, i), at) => {
                    switch(at, needs_inner_children(f, i)) {
                    | (Empty(ss, r), true) => (acc_ats @ [Single(ss, Hole(r), [], r)], [{kind: MissingInnerChild, range: r}] @ acc_rs, i+1)
                    | (Single(_, _, _, r), false) => (acc_ats @ [at], [{kind: ExtraneousChild, range: r}] @ acc_rs, i+1)
                    | (Multiple(_, _, r), false) => (acc_ats @ [at], [{kind: ExtraneousChild, range: r}] @ acc_rs, i+1)
                    | _ => (acc_ats @ [at], acc_rs, i+1)
                    }
                }
            }, ([], [], 0), ats);
            let term : abstract_term = switch(f) {
                | Ident(_) => failwith("impossible")
                | White => switch(lc', rc') {
                    | (Some((lc'', ss)), Some(([], rc''))) => L.white_builder(c, lc'', ss, rc'')
                    | _ => failwith("impossible")
                }
                | Mixfix(mf) => mf.builder(c, lc', ats', rc', range)
                | Repeater(rf, _) => rf.builder(c, lc', ats', rc', range)
            };
            (term, rs1 @ rs2 @ rs3);
            }
        }
    }
}