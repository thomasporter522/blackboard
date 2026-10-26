open Dialogue 

type myinnerstate = int;
type dia = dialogue(myinnerstate);
type mystate = continuation(myinnerstate);

let c1 : dia = Seq([you("What's up?"), me("Nothin."), you("Cool.")])
let c2 : dia = Seq([you("What's your fav color?"), me("Blue? Idk."), you("Word up."), you("I like red.")])
let monday_resp : dia = branch(i => i > 4, me("YOU ALREADY ASKED ME THAT A BUNCH OF TIMES"), me("Monday"));

let c3 : dia = Seq([you("What day is it?"), Do(i => i + 1), monday_resp])
let mydia : dia = Loop(Alt([c1, c2, c3]));

let myinit() : mystate = Next((0, mydia));
