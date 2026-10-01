assume 
eq : (A : type) -> (a b : A) -> type,
refl : (A : type) -> (a : A) -> eq A a a,
subst : (A : type) -> (p : A -> type) -> (a b : A) -> (h1 : eq A a b) -> (h2 : p b) -> p a
valid by
arrow-type M check (arrow-type portal ? check)