assume
eq (A : type) (a b : A) : prop, 
refl : (A : type) -> (a : A) -> eq A a a,
subst : (A : type) -> (a b : A) -> (P : A -> prop) -> (q : eq A a b) -> (h : P a) -> P b,
valid by check

assume 
thing : type, 
boo : thing
valid by check

construct 
sub (A B C : type) : thing, 
sub-eq : (A B C : type) -> eq thing (sub A B C) boo
by
witness ((A B C : type) => boo)
direct (
    givenall 
    refl @ thing @ boo
)