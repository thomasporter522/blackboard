prove
(A B : type) -> (A -> B) -> (A -> B)
by
given A : type [valid by type-type],
given B : type,
given h : (A -> B) [valid by ?],
given a : A,
MP A ? ?