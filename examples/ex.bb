assume 
eq : (A : type) -> (a b : A) -> type,
refl : (A : type) -> (a : A) -> eq A a a,
cast : (A B : type) -> (eq type A B) -> A -> B,
fav-cong : (A : type) -> (B1 B2 : A -> type) -> 
    ((a : A) -> eq type (B1 [a]) (B2 [a])) -> 
    eq type ((a : A) -> B1 [a]) ((a : A) -> B2 [a]),
valid by
check