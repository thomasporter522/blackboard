construct 
eq (A : type) (a b : A) : prop, 
refl : (A : type) -> (a : A) -> eq A a a,
subst : (A : type) -> (a b : A) -> (P : A -> prop) -> (q : eq A a b) -> (h : P a) -> P b,
by 
witness ((A : type) => (a : A) => (b : A) => (P : A -> prop) -> (h : P a) -> P b)
direct (
    givenall 
    h
)
direct (
    given A : type, 
    given a : A, 
    given b : A, 
    given P : A -> prop, 
    given q : (P : A -> prop) -> (h : P a) -> P b, 
    q @ P
)

construct 
sub (A B : type) : prop, 
sub-eq : (A B : type) -> eq prop (sub A B) ((x : A) -> x :: B)
by
definition