open Dialogue 

type myinnerstate = int;
type dia = dialogue(myinnerstate);
type mystate = dialogue_state(myinnerstate);

let c1 : dia = seq([you("What's up?"), me("Nothin."), you("Cool.")])
let c2 : dia = seq([you("What's your fav color?"), me("Blue? Idk."), you("Word up."), you("I like red.")])
let monday_resp : dia = branch(i => i > 4, me("YOU ALREADY ASKED ME THAT A BUNCH OF TIMES"), me("Monday"));

let c3 : dia = seq([you("What day is it?"), Do(i => i + 1), monday_resp])
let mydia : dia = seq([me("Hello! _Italics!_"), Loop(seq([alt([c1, c2, c3]), me(":)")]))
]);

let myinit() : mystate = (0, mydia, Loop(me("DONE.")));
