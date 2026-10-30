open Dialogue 

type myinnerstate = {count : int, solved : bool};
let init : myinnerstate = {count: 0, solved: false};
type dia = dialogue(myinnerstate);
type mystate = dialogue_state(myinnerstate);

let c1 : dia = seq([you("What's up?"), me("Nothin."), you("Cool.")])
let c2 : dia = seq([you("What's your fav color?"), me("Blue? Idk."), you("Word up."), you("I like red.")])
let monday_resp : dia = branch(s => s.count > 4, PuterSaysSmart(s => S("YOU ALREADY ASKED ME THAT " ++ string_of_int(s.count) ++ " TIMES")), me("Monday"));

let c3 : dia = seq([you("What day is it?"), Do(s => {...s, count : s.count + 1}, monday_resp)])
let errorchunk : dia = Loop(Chunk(seq([PlayerSaysEnv(S("explain_error")), me("This is an error"), you("")])));
let solvechunk : dia = Chunk(seq([Check(s => s.solved, you("Yooo I did it!")), me("Congrats!")]));
let mydia : dia = par([solvechunk, seq([me("Hello! _Italics!_"), Loop(seq([alt([c1, c2, c3]), me(":)")]))]), errorchunk]);

let myinit() : mystate = (init, mydia, Loop(me("DONE.")));
