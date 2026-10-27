type text = S(string)


// dialogue state is
// - state 
// - dialogue
// - stack 

// when an end is reached in the dialogue, pull everything from the stack until a chunk is hit (unless that's nothing)



type speaker = 
    | Player 
    | Puter

type message = (speaker, text)

// type of dialogues where the first word is always X, the last is always Y 

// type puterPuter('state) = 
//     | Say(text)

// type puterPlayer('state) = 
//     | Hi

// type playerPlayer('state) = 
//     | Say(text)

// type playerPuter('state) = 
//     | SeqPuter(playerPuter('state), puterPuter('state))

// type dia('state) = 
//     | Loop(playerPuter('state))

// type puterSays('state) = 
//     | Player(playerSays('state)) 
//     | Say(text)
//     | Seq(puterSays('state), puterSays('state))
//     | Check('state => bool, puterSays('state), puterSays('state))
//     | While('state => bool, puterSays('state), puterSays('state))
//     | Do('state => 'state)

// and playerSays('state) = 
//     | Puter(puterSays('state))
//     | Say(text)
//     | 


type dialogue('state) = 
    | S(message)
    | Check('state => bool)
    | Do('state => 'state)
    // | Check('state => bool, dialogue('state))
    // | Do(dialogue('state), 'state => 'state)
    // | Skip
    // | Null
    | Seq(dialogue('state), dialogue('state))
    | Alt(dialogue('state), dialogue('state))
    // | Star(dialogue('state))
    | Loop(dialogue('state))
    | Chunk(dialogue('state))
    // | Par(list(dialogue('state)))
    | Par(dialogue('state), dialogue('state))

type stack('state) = 
    | Chunk(stack('state))
    | Loop(dialogue('state))
    | Seq(dialogue('state), stack('state))
    | Par(dialogue('state), stack('state))

type dialogue_state('state) = ('state, dialogue('state), stack('state))

type message_option = 
    | Say(text)
    | Skip

// type continuation('state) = 
//     | Next(dialogue_state('state))
//     // | End('state)

type state_option('state) = 
    | PlayerTurn(list((message_option, dialogue_state('state))))
    | PuterTurn(text, dialogue_state('state))
    | End

let pre0 : 'state => bool = _ => true
let act0 : 'state => 'state = s => s

let rec combine_alts(s1 :  state_option('state), s2 :  state_option('state)) :  state_option('state) = switch(s1, s2) {
    | (s1, End) => s1
    | (End, s2) => s2
    | (PlayerTurn(_), PuterTurn(_)) => failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PlayerTurn(_)) => failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PuterTurn(_)) => failwith("DIALOGUE ERROR: BRANCHING NPC DIALOGUE")
    | (PlayerTurn(l1), PlayerTurn(l2)) => PlayerTurn(l1 @ l2)
}


// let rec dialogue_of_stack(k) : dialogue('state)= switch(k) {
//     | Empty => End
//     | Loop(d) => Loop(d)
//     | Seq(d, k') => Seq(d, dialogue_of_stack(k'))
//     | Par(d, k') => Par(d, dialogue_of_stack(k'))
// }

// let continue(s : 'state, k : stack('state)) : continuation('state) = {
//     Next((s, dialogue_of_stack(d)))
// }


let rec find_split_opt(p, l)  = switch(l) {
    | [] => None 
    | [h, ...t] => switch(p(h)) {
        | Some(x) => Some((x, t))
        | None => switch(find_split_opt(p, t)){
            | None => None 
            | Some((a, rest)) => Some((a, [h,...rest]))
        }
    }
}

// let rec pars_of_stack(k : stack('state)) = switch(k) {
//     | Empty
//     | Loop(_)
//     | Seq(_) => ([], k)
//     | Par(d, k) => 
//         let (ds, k') = pars_of_stack(k); 
//         ([d,...ds], k')
// }

// let option_of_message(m : message, rest : stack('state)) : 'state => state_option('state) = switch(m) {
//     | (Player, m) => s => PlayerTurn([(Say(m), continue(s, rest))])
//     | (Puter, m) =>  s => PuterTurn(m, continue(s, rest))
// }

// // should also track "other options"
// // par adds to other options
// // every construct adds the other options to the result of options, except chunk, which defers them
// let rec options_cont(s : 'state, d: dialogue('state), k : stack('state)) : state_option('state) = switch(d) {
//     | S(m) => option_of_message(m, k, s)
//     | Check(pre) => pre(s) ? options_cont(s, dialogue_of_stack(k), Empty) : End
//     | Do(act) => options_cont(act(s), dialogue_of_stack(k), Empty)
//     // | Skip => PlayerTurn([(Skip, continue(s, k))])
//     // | Null | Seq([]) => options_cont(s, dialogue_of_stack(k), Empty)
//     | Seq(d1, d2) => options_cont(s, d1, Seq(d2, k));
//     | Alt(d1, d2) => combine_alts(options_cont(s, d1, k), options_cont(s, d2, k))
//     // List.fold_left(combine_alts, End, List.map(d => options_cont((s, d), k), ds))
//     // | Star(d) => combine_alts(options_cont(s, d, Star(d)), options_cont(s, Null, k))
//     | Loop(d) => options_cont(s, d, Loop(d))
//     | Chunk(d) => 
//         let (ds, k') = pars_of_stack(k); 
//         options_context((s, Focused(d, ds)))
//     | Par(d1, d2) => combine_alts(options_cont(s, d1, Par(d2, k)), options_cont(s, d2, Par(d1, k)))
//     | End => End
// }

// and options_dia(s : 'state, d: dialogue('state)) : state_option('state) = options_cont(s, d, Empty)


// and options_context((s, d) : dialogue_state('state)) : state_option('state) = switch(d) {
//     // | Parallel(ds) => {
//     //     if(ds == []) { End } else {
//     //     let is_puter(r) = switch(options_dia(s,r)) {
//     //         | PuterTurn(m, c) => Some((m, c))
//     //         |_ => None
//     //     };
//     //     let par_opt(c: continuation('state), rest: list(dialogue('state))) : continuation('state) = switch(c, rest) {
//     //         | (End(s), []) => End(s);
//     //         | (End(s), rest) => Next((s, Parallel(rest)));
//     //         | (Next((s, c)), rest) => switch(c) {
//     //             | Parallel(ds) => Next((s, Parallel(ds @ rest)));
//     //             | Focused(d, ds) => Next((s, Focused(d, ds @ rest)));
//     //         }
//     //     }
//     //     let extract_player_opts(d: dialogue('state)) = switch(options_dia(s,d)) {
//     //         | PlayerTurn(os) => os 
//     //         | _ => failwith("extract_player_opts")
//     //     }
//     //     switch(find_split_opt(is_puter, ds)){
//     //     | Some(((m, c), rest)) => PuterTurn(m, par_opt(c, rest))
//     //     | None => PlayerTurn(List.concat_map(extract_player_opts, ds))
//     //     }
//     //     }
//     // }
//     | Just(d) => failwith("Todo")
//     | Focused(d, ds) => 
//         let focus_opt(c: continuation('state), unfocused: list(dialogue('state))) : continuation('state) = switch(c, unfocused) {
//             | (End(s), []) => End(s);
//             | (End(s), unfocused) => Next((s, Just(Par(unfocused))));
//             | (Next((s, c)), unfocused) => Next((s, Focused(c, unfocused)));
//         }
//         let f(ds: list(dialogue('state)), (m, c) : (message_option, continuation('state))) = (m, focus_opt(c, ds));
//         switch(options_context((s, d))) {
//             | PlayerTurn(os) => PlayerTurn(List.map(f(ds), os)) 
//             | PuterTurn(m, c) => PuterTurn(m, focus_opt(c, ds))
//             | End => PuterTurn(S(""), Next((s, Just(Par(ds)))))
//         }
// }

// let options(c : continuation('state)) : state_option('state) = switch(c) {
//     | Next(sd) => options_cont(sd, End)
//     | End => End 
// }


let combine(s1 :  state_option('state), s2 :  state_option('state)) :  state_option('state) = switch(s1, s2) {
    | (s1, End) => s1
    | (End, s2) => s2
    | (PlayerTurn(_), PuterTurn(_)) => failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PlayerTurn(_)) => failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PuterTurn(_)) => failwith("DIALOGUE ERROR: BRANCHING NPC DIALOGUE")
    | (PlayerTurn(l1), PlayerTurn(l2)) => PlayerTurn(l1 @ l2)
}

let rec proceed_acc(s : 'state, acc : Option.t(dialogue('state)), k : stack('state)) : dialogue_state('state) = switch(acc, k) {
    | (None, Chunk(k)) => proceed_acc(s, None, k)
    | (Some(d), Chunk(k)) => (s, d, Chunk(k))
    | (None, Loop(d)) => (s, d, Loop(d))
    | (Some(d1), Loop(d2)) => (s, d1, Loop(d2))
    | (None, Seq(d, k)) => proceed_acc(s, Some(d), k)
    | (Some(d1), Seq(d2, k)) => proceed_acc(s, Some(Seq(d1, d2)), k)
    | (None, Par(d, k)) => proceed_acc(s, Some(d), k)
    | (Some(d1), Par(d2, k)) => proceed_acc(s, Some(Par(d1, d2)), k)
}

let proceed(s : 'state, k : stack('state)) = proceed_acc(s, None, k);

let option_of_message(m : message, rest : stack('state)) : 'state => state_option('state) = switch(m) {
    | (Player, m) => s => PlayerTurn([(Say(m), proceed(s, rest))])
    | (Puter, m) =>  s => PuterTurn(m, proceed(s, rest))
}

let rec options_state((s, d, k) : dialogue_state('state)) : state_option('state) = switch(d) {
    | S(m) => option_of_message(m, k, s)
    | Check(pre) => pre(s) ? options_state(proceed(s, k)) : End
    | Do(act) => options_state(proceed(act(s), k))
    | Seq(d1, d2) => options_state((s, d1, Seq(d2, k)))
    | Alt(d1, d2) => combine(options_state((s, d1, k)), options_state((s, d2, k)))
    | Loop(d) => options_state((s, d, Loop(d)))
    | Chunk(d) => options_state((s, d, Chunk(k)))
    | Par(d1, d2) => combine(options_state((s, d1, Par(d2, k))), options_state((s, d2, Par(d1, k))))
}


let me(s) = S((Puter, S(s)))
let you(s) = S((Player, S(s)))
// let opt(d) = Alt(d, Skip)
let branch(check : 'state => bool, d1, d2) = Alt(Seq(Check(check), d1), Seq(Check(s => !check(s)), d2))