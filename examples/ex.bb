construct 
and (p1 p2 : prop) : prop,
andi : (p1 p2 : prop) -> p1 -> p2 -> (and [p1]) [p2],
ande : (p1 p2 : prop) -> (h : (and [p1]) [p2]) -> (M : prop) -> (p1 -> p2 -> M) -> M,
by 
witness ((p1 : prop) => (p2 : prop) => ((M : prop) -> (h : (p1 -> p2 -> M)) -> M)) 
direct (
    givenall
    given h1 : p1, 
    given h2 : p2, 
    givenall
    h h1 h2
)
direct (
    given p1 : prop,
    given p2 : prop, 
    given h : (M : prop) -> (h : p1 -> p2 -> M) -> M,
    h
)

construct 
exists (A : type) (P : A -> prop) : prop,
existsi : (A : type) -> (P : A -> prop) -> (a : A) -> (h : P [a]) -> (exists [A]) [P],
existse : (A : type) -> (P : A -> prop) -> (h : (exists [A]) [P]) -> (M : prop) -> ((a : A) -> (h : P [a]) -> M) -> M,
by 
witness ((A : type) => (P : A -> prop) => ((M : prop) -> ((a : A) -> (h : P [a]) -> M) -> M))
direct (
    givenall
    given e : (a : A) -> (h : P[a]) -> M,
    e @ a h
)
direct (
    given A : type, 
    given P : A -> prop, 
    given h : (M : prop) -> ((a : A) -> (h : P [a]) -> M) -> M,
    h
)