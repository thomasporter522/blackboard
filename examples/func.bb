construct 
and (p1 p2 : prop) : prop,
andi : (p1 p2 : prop) -> p1 -> p2 -> and p1 p2,
ande : (p1 p2 : prop) -> (h : and p1 p2) -> (M : prop) -> (p1 -> p2 -> M) -> M,
by 
witness ((p1 : prop) => (p2 : prop) => ((M : prop) -> (h : (p1 -> p2 -> M)) -> M)),
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
witness ((A : type) => (P : A -> prop) => ((M : prop) -> ((a : A) -> (h : P a) -> M) -> M)),
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
witness ((A : type) => (a : A) => (b : A) => (P : A -> prop) -> (h : P a) -> P b),
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
existsforall : (A B : type) -> (P : A -> B -> prop) -> 
    (h : exists A ((a : A) => (b : B) -> P a b)) ->
    (b : B) -> exists A ((a : A) => P a b)
by 
direct (
    givenall 
    (existse @ A @ ((a : A) => ((b : B) -> P a b)) h) 
    @ (exists A ((a : A) => P a b)) (
        givenall
        existsi @ A @ ((a : A) => P a b) @ a (h @ b)
    )
)

construct 
sub (A B : type) : prop, 
sub-eq : (A B : type) -> eq prop (sub A B) ((x : A) -> x :: B)
by
definition

assume 
small : type -> prop,
pi-small : 
    (A : type) -> (sA : small A) -> 
    (B : (a : A) -> type) -> (sB : (a : A) -> small (B a)) -> 
    small ((a : A) -> B a),
abs-id : (X : type) -> (sX : small X) -> (x : X) -> X,
abs-id-eq : (X : type) -> (sX : small X) -> (x : X) -> eq X (abs-id X . x) x,
abs-k : (X A : type) -> (sX : small X) -> (sA : small A) -> (a : A) -> (x : X) -> A,
abs-k-eq : (X A : type) -> (sX : small X) -> (sA : small A) -> (a : A) -> (x : X) -> eq A (abs-k X A . . a x) a,
abs-ap : (X A B : type) -> (sX : small X) -> (sA : small A) -> (sB : small B) -> (f : X -> A -> B) -> (a : X -> A) -> (x : X) -> B,
abs-ap-eq : (X A B : type) -> (sX : small X) -> (sA : small A) -> (sB : small B) -> (f : X -> A -> B) -> (a : X -> A) -> (x : X) -> eq B (abs-ap X A B . . . f a x) (f x (a x)),
valid by 
check

assume 
nat : type, 
nat-small : small nat,
zero : nat, 
suc : nat -> nat,
valid by check

construct 
addtwo : nat -> nat, 
addtwo-eq : (n : nat) -> eq nat (addtwo n) (suc (suc n))
by
?

construct 
addtwo : nat -> nat, 
addtwo-eq : (n : nat) -> eq nat (addtwo n) (suc (suc n))
by
given M : prop, 
given h : (addtwo : nat -> nat) -> (addtwo-eq : (n : nat) -> eq nat (addtwo n) (suc (suc n))) -> M,
h @ (abs-ap nat nat nat . . . (abs-k nat (nat -> nat) . . suc) suc) valid by ? (
given n : nat, 
claim e1 : eq nat (abs-ap nat nat nat . . . (abs-k nat (nat -> nat) . . suc) suc n) (abs-k nat (nat -> nat) . . suc n (suc n)) by ?,
claim e2 : eq nat (abs-k nat (nat -> nat) . . suc n (suc n)) (suc (suc n)) by ?,
trans @ nat
    @ (abs-ap nat nat nat . . . (abs-k nat (nat -> nat) . . suc) suc n) valid by ?
    @ (abs-k nat (nat -> nat) . . suc n (suc n)) valid by ?
    @ (suc (suc n)) (e1 valid by ?) (e2 valid by ?)
)
