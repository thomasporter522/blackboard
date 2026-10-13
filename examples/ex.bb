assume 
eq : (A : type) -> (a b : A) -> prop,
(refl) (A : type) -> (a : A) -> eq A a a,
(subst) (A : type) -> 
    (P : A -> prop) -> 
    (a b : A) -> 
    (h : eq A a b) -> 
    (P[a]) -> (P[b]),
valid by check

construct 
(cast) (P Q : prop) -> (h : eq prop P Q) -> (p : P) -> Q
by 
direct 
givenall 
subst @ prop @ ((P : prop) => P) @ P @ Q h p

assume 
sub : (A B : type) -> prop, 
(sub-eq) (A B : type) -> eq prop (sub A B) ((a : A) -> a :: B)
valid by check

construct 
(sub-cast) (A B : type) -> (h : sub A B) -> (a : A) -> a :: B
by 
direct
given A : type, 
given B : type,
cast @ (sub A B) @ ((a : A) -> a :: B) (sub-eq @ A @ B)