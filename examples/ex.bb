prove
(A B C : type) -> (A -> B) -> (B -> C) -> (A -> C)
by
given A : type [valid by type-type],
given B : type,
given C : type,
given h1 : (A -> B) [valid by ?],
given h2 : (B -> C) [valid by ?],
given a : A,
suffices l1 : B by 
    h2 l1,
h1 a