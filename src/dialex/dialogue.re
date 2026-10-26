type text = S(string)

type speaker = 
    | Player 
    | Puter

type message = (speaker, text)

type dialogue('state) = 
    | S(message)
    | Check('state => bool)
    | Do('state => 'state)
    // | Check('state => bool, dialogue('state))
    // | Do(dialogue('state), 'state => 'state)
    | Skip
    | Seq(list(dialogue('state)))
    | Alt(list(dialogue('state)))
    | Star(dialogue('state))
    | Loop(dialogue('state))
    | Chunk(dialogue('state))
    | Par(list(dialogue('state)))
    | End

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
    | End

let continue(s : 'state, d : dialogue('state)) : continuation('state) = {
    Next((s, d))
}

let option_of_message(m : message, rest : dialogue('state)) : 'state => state_option('state) = switch(m) {
    | (Player, m) => s => PlayerTurn([(Say(m), continue(s, rest))])
    | (Puter, m) =>  s => PuterTurn(m, continue(s, rest))
}

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

// should also track "other options"
// par adds to other options
// every construct adds the other options to the result of options, except chunk, which defers them
let rec options_cont((s, d) : dialogue_state('state), rest : dialogue('state)) : state_option('state) = switch(d) {
    | S(m) => option_of_message(m, rest, s)
    | Check(pre) => pre(s) ? options_cont((s, rest), End) : End
    | Do(act) => options_cont((act(s), rest), End)
    | Skip | Seq([]) => PlayerTurn([(Skip, continue(s, rest))])
    | Seq([d, ...ds]) => options_cont((s, d), Seq(ds @ [rest]));
    | Alt(ds) => List.fold_left(combine_alts, End, List.map(d => options_cont((s, d), rest), ds))
    | Star(d) => combine_alts(options_cont((s, d), Star(d)), options_cont((s, Skip), rest))
    | Loop(d) => options_cont((s, d), Loop(d))
    | Chunk(_d) => failwith("Todo") // options(s, d)
    | Par(_ds) => failwith("Todo") //List.concat_map(options(s), ds)
    | End => End
}

let options(c : continuation('state)) : state_option('state) = switch(c) {
    | Next(sd) => options_cont(sd, End)
    | End => End 
}


let me(s) = S((Puter, S(s)))
let you(s) = S((Player, S(s)))
let opt(d) = Alt([d, Skip])
let branch(check : 'state => bool, d1, d2) = Alt([Seq([Check(check), d1]), Seq([Check(s => !check(s)), d2])])