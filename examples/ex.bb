prove
(A B C : type) -> (A -> B -> C) -> (B -> A -> C)
by
given A : type [valid by type-type],
given B : type,
given C : type,
given h : (A -> B -> C) [valid by ?],
given b : B,
given a : A,
h a b