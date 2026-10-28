type text = S(string)

type speaker = 
    | Player 
    | Puter

type message = (speaker, text)

type dialogue('state) = 
    | S(message)
    | Check('state => bool, dialogue('state))
    | Do('state => 'state, dialogue('state))
    | Seq(dialogue('state), dialogue('state))
    | Alt(dialogue('state), dialogue('state))
    | Loop(dialogue('state))
    | Star(dialogue('state), dialogue('state))
    | Chunk(dialogue('state))
    | Par(dialogue('state), dialogue('state))

type stack('state) = 
    | Chunk(stack('state))
    | Loop(dialogue('state))
    | Seq(dialogue('state), stack('state))
    | Par(dialogue('state), stack('state))

type dialogue_state('state) = ('state, dialogue('state), stack('state))

type state_option('state) = 
    | PlayerTurn(list((text, dialogue_state('state))))
    | PuterTurn(text, dialogue_state('state))
    | End


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

let combine(par : bool, s1 :  state_option('state), s2 :  state_option('state)) :  state_option('state) = switch(s1, s2) {
    | (s1, End) => s1
    | (End, s2) => s2
    | (PlayerTurn(_), PuterTurn(_)) => par ? s2 : failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PlayerTurn(_)) => par ? s1 : failwith("DIALOGUE ERROR: TURN CONFLICT")
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
    | (Player, m) => s => PlayerTurn([(m, proceed(s, rest))])
    | (Puter, m) =>  s => PuterTurn(m, proceed(s, rest))
}

let rec continue(s : 'state, k : stack('state)) : dialogue_state('state) = switch(k) {
    | Chunk(k) => continue(s, k)
    | Loop(d) => (s, d, Loop(d))
    | Seq(d, k) => (s, d, k)
    | Par(d, k) => (s, d, k)
}

let rec options((s, d, k) : dialogue_state('state)) : state_option('state) = switch(d) {
    | S(m) => option_of_message(m, k, s)
    | Check(pre, d) => pre(s) ? options((s, d, k)) : End
    | Do(act, d) => options((act(s), d, k))
    | Seq(d1, d2) => options((s, d1, Seq(d2, k)))
    | Alt(d1, d2) => combine(false, options((s, d1, k)), options((s, d2, k)))
    | Loop(d) => options((s, d, Seq(Loop(d), k)))
    | Star(d1, d2) => combine(false, options((s, d1, Seq(Star(d1, d2), k))), options((s, d2, k)))
    | Chunk(d) => options((s, d, Chunk(k)))
    | Par(d1, d2) => combine(true, options((s, d1, Par(d2, k))), options((s, d2, Par(d1, k))))
}


let me(s) = S((Puter, S(s)))
let you(s) = S((Player, S(s)))
let branch(check : 'state => bool, d1, d2) = Alt(Check(check, d1), Check(s => !check(s), d2))
let seq(ds : list(dialogue('state))) = switch(ds) {
    | [] => failwith("empty seq")
    | [h,...t] => List.fold_left((a : dialogue('state), b) => Seq(a, b), h, t)
}

let alt(ds : list(dialogue('state))) = switch(ds) {
    | [] => failwith("empty alt")
    | [h,...t] => List.fold_left((a : dialogue('state), b) => Alt(a, b), h, t)
}