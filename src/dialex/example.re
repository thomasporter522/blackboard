open Dialogue 

type myinnerstate = unit;
type dia = dialogue(myinnerstate);
type mystate = continuation(myinnerstate);

let c1 : dia = Seq([you("What's up?"), me("Nothin."), you("Cool.")])
let c2 : dia = Seq([you("What's your fav color?"), me("Blue? Idk."), you("Word up."), you("I like red.")])
let c3 : dia = Seq([you("What day is it?"), me("MONDAY"), me("So."), you("Oh no"), me("It's okay.")])
let mydia : dia = Loop(Alt([c1, c2, c3]));

let myinit() : mystate = Next(((), mydia));
