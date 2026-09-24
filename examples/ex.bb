assume 
eq : (A : type) -> (a b : A) -> type,
refl : (A : type) -> (a : A) -> eq A a a,
subst : (A : type) -> (p : A -> type) -> (a b : A) -> (h1 : eq A a b) -> (h2 : p b) -> p a
valid by check

construct
my-type : type,
my-type-eq : eq type my-type (type -> type)
by definition

construct 
sym : (A : type) -> (a b : A) -> (h : eq A a b) -> eq A b a,
by direct givenall
subst @ A @ (eq A b) @ a @ b h (refl @ A @ b)

construct
trans : (A : type) -> (a b c : A) -> (h1 : eq A a b) -> (h2 : eq A b c) -> eq A a c,
by 
direct givenall 
subst @ A @ (eq A a) @ c @ b (sym @ A @ b @ c h2) h1

assume
abs-const : (X A : type) -> (a : A) -> (X -> A),
abs-const-eq : (X A : type) -> (a : A) -> (x : X) -> eq A (abs-const X A a x) a,
abs-id : (X : type) -> X -> X, 
abs-id-eq : (X : type) -> (x : X) -> eq X (abs-id X x) x,
abs-ap : (X A B : type) -> (f : X -> A -> B) -> (a : X -> A) -> (X -> B),
abs-ap-eq : (X A B : type) -> (f : X -> A -> B) -> (a : X -> A) -> (x : X) -> eq B (abs-ap X A B f a x) (f x (a x)),
valid by check

assume 
nat : type,
zero : nat,
suc : nat -> nat, 
plus : nat -> nat -> nat
valid by check

construct 
double : nat -> nat,
double-eq : (n : nat) -> eq nat (double n) (plus n n)
by
given M : type,
given portal : (double : nat -> nat) -> (double-eq : (n : nat) -> eq nat (double n) (plus n n)) -> M,
claim equation : (n : nat) -> eq nat (abs-ap nat nat nat plus (abs-id nat) n) (plus n n) by 
    given n : nat, 
    trans @ nat @ (abs-ap nat nat nat plus (abs-id nat) n) @ (plus n (abs-id nat n)) @ (plus n n) 
    (abs-ap-eq @ nat @ nat @ nat @ plus @ (abs-id nat) @ n)
    (?)
,
portal @ (abs-ap nat nat nat plus (abs-id nat)) equation

construct 
cong-ap-arg : (A B : type) -> (f : A -> B) -> (a b : A) -> (h : eq A a b) -> eq B (f a) (f b)
by
direct 
givenall
?