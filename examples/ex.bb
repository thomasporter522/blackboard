prove
(A B C : type) -> (A -> B) -> (B -> C) -> (A -> C)
by
given A : type [valid by type-type],
given B : type,
given C : type,
given h1 : (A -> B) [valid by ?],
given h2 : (B -> C) [valid by ?],
given a : A,
h2 (h1 a)