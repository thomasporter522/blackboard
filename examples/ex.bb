construct 
and (p1 p2 : prop) : prop,
andi : (p1 p2 : prop) -> p1 -> p2 -> and p1 p2,
ande : (p1 p2 : prop) -> (h : and p1 p2) -> (M : prop) -> (p1 -> p2 -> M) -> M,
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
    givenall 
    h @ M
)


construct 
exists (A : type) (P : A -> prop) : prop,
existsi : (A : type) -> (P : A -> prop) -> (a : A) -> (h : P a) -> exists A P,
existse : (A : type) -> (P : A -> prop) -> (h : exists A P) -> (M : prop) -> ((a : A) -> (h : P a) -> M) -> M,
by 
witness ((A : type) => (P : A -> prop) => ((M : prop) -> ((a : A) -> (h : P a) -> M) -> M))
direct (
    givenall
    given e : (a : A) -> (h : P a) -> M,
    e @ a h
)
direct (
    given A : type, 
    given P : A -> prop, 
    given h : (M : prop) -> ((a : A) -> (h : P a) -> M) -> M,
    h
)

construct 
eq (A : type) (a b : A) : prop, 
refl : (A : type) -> (a : A) -> eq A a a,
subst : (A : type) -> (a b : A) -> (P : A -> prop) -> (q : eq A a b) -> (h : P a) -> P b,
by 
witness ((A : type) => (a : A) => (b : A) => (P : A -> prop) -> (h : P a) -> P b)
direct (
    givenall 
    h
)
direct (
    given A : type, 
    given a : A, 
    given b : A, 
    given P : A -> prop, 
    given q : (P : A -> prop) -> (h : P a) -> P b, 
    q @ P
)

construct 
sym : (A : type) -> (a b : A) -> (h : eq A a b) -> eq A b a
by 
direct (
givenall 
subst @ A @ a @ b @ ((x : A) => eq A x a) h (refl @ A @ a)
)

construct 
nat : type, 
zero : nat, 
suc (n : nat) : nat, 
by 
witness ((A : type) -> (A -> A) -> (A -> A))
witness ((A : type) => (f : A -> A) => (a : A) => a)
witness ((n : (A : type) -> (A -> A) -> (A -> A)) => (A : type) => (f : A -> A) => (a : A) => n A f (f a))
?