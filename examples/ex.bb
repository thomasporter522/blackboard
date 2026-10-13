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
claim lemma : (h2 : eq A a a) -> eq A b a
    by 
    (subst @ A @ ((x : A) => eq A x a) @ a @ b) h, 
lemma (refl @ A @ a)