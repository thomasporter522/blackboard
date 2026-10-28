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
    | Star(dialogue('state), dialogue('state))
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
    // | Skip

// type continuation('state) = 
//     | Next(dialogue_state('state))
//     // | End('state)

type state_option('state) = 
    | PlayerTurn(list((message_option, dialogue_state('state))))
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
    | (Player, m) => s => PlayerTurn([(Say(m), proceed(s, rest))])
    | (Puter, m) =>  s => PuterTurn(m, proceed(s, rest))
}

let rec continue(s : 'state, k : stack('state)) : dialogue_state('state) = switch(k) {
    | Chunk(k) => continue(s, k)
    | Loop(d) => (s, d, Loop(d))
    | Seq(d, k) => (s, d, k)
    | Par(d, k) => (s, d, k)
}

let rec guarded(d : dialogue('state)) : bool = switch(d) {
    | S(_) => true
    | Check(_) => false
    | Do(_) => false
    | Seq(d1, d2) => guarded(d1) || guarded(d2)
    | Alt(d1, d2) => guarded(d1) && guarded(d2)
    | Loop(d) => guarded(d)
    | Star(_, d2) => guarded(d2)
    | Chunk(d) => guarded(d)
    | Par(d1, d2) => guarded(d1) || guarded(d2)
}

let rec options((s, d, k) : dialogue_state('state)) : state_option('state) = switch(d) {
    | S(m) => option_of_message(m, k, s)
    | Check(pre) => pre(s) ? options(continue(s, k)) : End
    | Do(act) => options(continue(act(s), k))
    | Seq(d1, d2) => options((s, d1, Seq(d2, k)))
    | Alt(d1, d2) => combine(false, options((s, d1, k)), options((s, d2, k)))
    | Loop(d) => options((s, d, Seq(Loop(d), k)))
    | Star(d1, d2) => combine(false, options((s, d1, Seq(Star(d1, d2), k))), options((s, d2, k)))
    | Chunk(d) => options((s, d, Chunk(k)))
    | Par(d1, d2) => 
        if(!guarded(d1) || !guarded(d2)) { failwith("dialogue has unguarded pars") } else
        combine(true, options((s, d1, Par(d2, k))), options((s, d2, Par(d1, k))))
}


let me(s) = S((Puter, S(s)))
let you(s) = S((Player, S(s)))
let null = Check(_ => true)
let block = Check(_ => false)
let opt(d) = Alt(d, null)
let branch(check : 'state => bool, d1, d2) = Alt(Seq(Check(check), d1), Seq(Check(s => !check(s)), d2))
let seq(ds : list(dialogue('state))) = List.fold_left((a : dialogue('state), b) => Seq(a, b), null, ds)
let alt(ds : list(dialogue('state))) = List.fold_left((a : dialogue('state), b) => Alt(a, b), block, ds)