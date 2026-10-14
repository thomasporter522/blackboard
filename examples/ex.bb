assume 
eq : (A : type) -> (a b : A) -> prop,
refl : (A : type) -> (a : A) -> eq A a a,
subst : (A : type) -> 
    (P : A -> prop) -> 
    (a b : A) -> 
    (h : eq A a b) -> 
    (P[a]) -> (P[b]),
valid by check

construct 
trans : (A : type) -> (a b c : A) -> (e1 : eq A a b) -> (e2 : eq A b c) -> eq A a c
by 
direct 
givenall
subst @ A @ ((x : A) => eq A a x) @ b @ c e2 e1

construct 
cast : (P Q : prop) -> (h : eq prop P Q) -> (p : P) -> Q
by 
direct 
givenall 
subst @ prop @ ((P : prop) => P) @ P @ Q h p

assume 
sub : (A B : type) -> prop, 
sub-eq : (A B : type) -> eq prop (sub A B) ((a : A) -> a :: B)
valid by check

construct 
sub-cast : (A B : type) -> (h : sub A B) -> (a : A) -> a :: B
by 
direct
given A : type, 
given B : type,
cast @ (sub A B) @ ((a : A) -> a :: B) (sub-eq @ A @ B)

assume 
small : type -> prop,
pi-small : 
    (A : type) -> (sA : small A) -> 
    (B : (a : A) -> type) -> (sB : (a : A) -> small (B[a])) -> 
    small ((a : A) -> B[a]),
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
