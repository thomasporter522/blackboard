type text = S(string)

type speaker = 
    | Player 
    | Puter

type message = (speaker, text)

type dialogue('state) = 
    | S(message)
    | Check('state => bool, message)
    | Do(message, 'state => 'state)
    | CheckDo('state => bool, message, 'state => 'state)
    | Skip
    | Seq(list(dialogue('state)))
    | Alt(list(dialogue('state)))
    | Star(dialogue('state))
    | Loop(dialogue('state))
    | Chunk(dialogue('state))
    | Par(list(dialogue('state)))
    | End

let me(s) = S((Puter, S(s)))
let you(s) = S((Player, S(s)))
let opt(d) = Alt([d, Skip])

type dialogue_state('state) = ('state, dialogue('state))

type message_option = 
    | Say(text)
    | Skip

type continuation('state) = 
    | Next(dialogue_state('state))
    | End

type state_option('state) = 
    | PlayerTurn(list((message_option, continuation('state))))
    | PuterTurn(text, continuation('state))
    | Empty

let continue(s : 'state, d : dialogue('state)) : continuation('state) = {
    Next((s, d))
}

let option_of_message(m : message, c : 'state => continuation('state)) : 'state => state_option('state) = switch(m) {
    | (Player, m) => s => PlayerTurn([(Say(m), c(s))])
    | (Puter, m) =>  s => PuterTurn(m, c(s))
}

let option_of_triple(s : 'state, pre : 'state => bool, m : message, act : 'state => 'state, rest : dialogue('state)) : state_option('state) = {
    pre(s) ? option_of_message(m, s => continue(act(s), rest), s) : Empty
}

let pre0 : 'state => bool = _ => true
let act0 : 'state => 'state = s => s

let rec combine_alts(s1 :  state_option('state), s2 :  state_option('state)) :  state_option('state) = switch(s1, s2) {
    | (s1, Empty) => s1 
    | (Empty, s2) => s2
    | (PlayerTurn(_), PuterTurn(_)) => failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PlayerTurn(_)) => failwith("DIALOGUE ERROR: TURN CONFLICT")
    | (PuterTurn(_), PuterTurn(_)) => failwith("DIALOGUE ERROR: BRANCHING NPC DIALOGUE")
    | (PlayerTurn(l1), PlayerTurn(l2)) => PlayerTurn(l1 @ l2)
}

let rec options_cont((s, d) : dialogue_state('state), rest : dialogue('state)) : state_option('state) = switch(d) {
    | S(m) => option_of_triple(s, pre0, m, act0, rest)
    | Check(pre, m) => option_of_triple(s, pre, m, act0, rest)
    | Do(m, act) => option_of_triple(s, pre0, m, act, rest)
    | CheckDo(pre, m, act) => option_of_triple(s, pre, m, act, rest)
    | Skip | Seq([]) => PlayerTurn([(Skip, continue(s, rest))])
    | Seq([d, ...ds]) => options_cont((s, d), Seq(ds @ [rest]));
    | Alt(ds) => List.fold_left(combine_alts, Empty, List.map(d => options_cont((s, d), rest), ds))
    | Star(d) => combine_alts(options_cont((s, d), Star(d)), options_cont((s, Skip), rest))
    | Loop(d) => options_cont((s, d), Loop(d))
    | Chunk(_d) =>failwith("Todo") // options(s, d)
    | Par(_ds) => failwith("Todo") //List.concat_map(options(s), ds)
    | End => Empty
}

let options(c : continuation('state)) : state_option('state) = switch(c) {
    | Next(sd) => options_cont(sd, End)
    | End => Empty 
}