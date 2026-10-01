assume 
eq : (A : type) -> (a b : A) -> type,
fav-cong : (A : type) -> (B1 B2 : A -> type) -> 
    ((a : A) -> eq type (B1 [a]) (B2 [a])) -> 
    eq type ((a : A) -> B1 [a]) ((a : A) -> B2 [a]),
valid by
arrow-type M check (arrow-type portal (arrow-type eq check (arrow-type fav-cong (arrow-type A check (arrow-type B1 check (arrow-type B2 check (arrow-type h 
(
arrow-type a check (ap ty2 type type ? (unlambda-type check))
) 

?)))) check)) check)