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

construct
my-type : type,
my-type-eq : eq type my-type (type -> type)
by 
given M : prop, 
given h : (my-type : type) -> (my-type-eq : eq type my-type (type -> type)) -> M,
h @ (type -> type) (refl @ type @ (type -> type))