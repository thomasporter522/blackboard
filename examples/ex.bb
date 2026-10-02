assume 
eq : (A : type) -> (a b : A) -> type,
refl : (A : type) -> (a : A) -> eq A a a,
fav-cong : (A : type) -> (B1 B2 : A -> type) -> 
    ((a : A) -> eq type (B1 [a]) (B2 [a])) -> 
    eq type ((a : A) -> B1 [a]) ((a : A) -> B2 [a]),
valid by check

construct
thm : (A1 A2 : type) -> 
    (eq type A1 A2) ->
    eq type ((A : type) -> eq type A A1) ((A : type) -> eq type A A2)
by 
direct 
givenall
given h : eq type A1 A2,
claim h2 : (B1 B2 : type -> type) -> 
    ((a : type) -> eq type (B1 [a]) (B2 [a])) -> 
    eq type ((a : type) -> B1 [a]) ((a : type) -> B2 [a])
by fav-cong @ type,
claim h3 :
    ((a : type) -> eq type (((A : type) => eq type A A1) [a]) (((A : type) => eq type A A2) [a])) -> 
    eq type ((a : type) -> ((A : type) => eq type A A1) [a]) ((a : type) -> ((A : type) => eq type A A2) [a])
by h2 @ ((A : type) => eq type A A1) @ ((A : type) => eq type A A2),
?