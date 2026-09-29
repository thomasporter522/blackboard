assume 
eq : (A : type) -> (a b : A) -> type,
refl : (A : type) -> (a : A) -> eq A a a,
cast : (A B : type) -> (h1 : eq type A B) -> A -> B
valid by check

assume 
cong-pi-cod : (A : type) -> (B1 B2 : [x : A] type) -> 
    ((x : A) -> eq type B1 B2) -> eq type ((x : A) -> B1) ((x : A) -> B2)
valid by
arrow-type M obvious (arrow-type portal (
    
    arrow-type thing ? 

obvious) obvious)