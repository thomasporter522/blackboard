assume 
eq : (A : type) -> (a b : A) -> type,
refl : (A : type) -> (a : A) -> eq A a a,
fav-cong : (A : type) -> (B1 B2 : A -> type) -> 
    ((a : A) -> eq type (B1 [a]) (B2 [a])) -> 
    eq type ((a : A) -> B1 [a]) ((a : A) -> B2 [a]),
valid by check

construct 
mythm : eq type type type
by 
given M : type,
given portal : (mythm : eq type type type) -> M valid by check,
portal @ type