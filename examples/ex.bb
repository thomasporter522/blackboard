assume 
eq : (A B : type) -> (a : A) -> (b : B) -> type,
refl : (A : type) -> (a : A) -> eq A A a a
valid by check

construct
my-type : type,
my-type-eq : eq type type my-type (type -> type)
by 
given M : type,
given portal : ((my-type : type) -> (my-type-eq : eq type type my-type (type -> type)) -> M) valid by check,
((portal @ (type -> type)) (refl @ type @ (type -> type)))
