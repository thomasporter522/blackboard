assume 
eq : (A B : type) -> (a : A) -> (b : B) -> type,
refl : (A : type) -> (a : A) -> eq A A a a,
subst : (A : type) -> (p : A -> type) -> (a b : A) -> (h1 : eq A A a b) -> (h2 : p b) -> p a
valid by check

construct
my-type : type,
my-type-eq : eq type type my-type (type -> type)
by definition

construct 
sym : (A : type) -> (a b : A) -> (h : eq A A a b) -> eq A A b a,
by direct givenall
subst @ A @ (eq A A b) @ a @ b h (refl @ A @ b)

construct
trans : (A : type) -> (a b c : A) -> (h1 : eq A A a b) -> (h2 : eq A A b c) -> eq A A a c,
by 
direct givenall 
subst @ A @ (eq A A a) @ c @ b (sym @ A @ b @ c h2) h1

assume
abs-const : (X A : type) -> (a : A) -> (X -> A),
abs-const-eq : (X A : type) -> (a : A) -> (x : X) -> eq A A (abs-const X A a x) a,
abs-id : (X : type) -> X -> X, 
abs-id-eq : (X : type) -> (x : X) -> eq X X (abs-id X x) x,
abs-ap : (X A B : type) -> (f : X -> A -> B) -> (a : X -> A) -> (X -> B),
abs-ap-eq : (X A B : type) -> (f : X -> A -> B) -> (a : X -> A) -> (x : X) -> eq B B (abs-ap X A B f a x) (f x (a x)),
valid by check

assume 
nat : type,
zero : nat,
suc : nat -> nat, 
plus : nat -> nat -> nat
valid by check