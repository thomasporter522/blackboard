assume 
eq : (A : type) -> (a b : A) -> prop,
(refl) (A : type) -> (a : A) -> eq A a a,
(subst) (A : type) -> 
    (P : A -> prop) -> 
    (a b : A) -> 
    (h : eq A a b) -> 
    (P[a]) -> (P[b]),
valid by
check

construct 
(sym) (A : type) -> (a b : A) -> (h : eq A a b) -> eq A b a 
by 
direct
givenall
((subst @ A @ ((x : A) => eq A x a) @ a @ b) h) (refl @ A @ a)

assume
nat : type, 
zero : nat, 
suc : nat -> nat, 
plus : nat -> nat -> nat
valid by check

construct
my-nat : nat,
my-nat-eq : eq nat my-nat zero
by 
definition