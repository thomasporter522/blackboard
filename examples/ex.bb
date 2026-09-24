assume 
eq : (A B : type) -> (a : A) -> (b : B) -> type,
refl : (A : type) -> (a : A) -> eq A A a a
valid by check

construct
my-type : type,
my-type-eq : eq type type my-type (type -> type)
by 
definition