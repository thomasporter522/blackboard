prove
(A B C : type) -> (A -> B) -> (B -> C) -> (A -> C)
by
given A : type,
given B : type,
given C : type,
given h1 : A -> B [valid by arrow-type x (type-of A) (type-of B)],
given h2 : B -> C [valid by arrow-type x obvious obvious],
given a : A,
suffices b : B by h2 a,
?