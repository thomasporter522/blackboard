assume 
SIGIL : prop
valid by check 

construct 
and (p1 p2 : prop) : prop,
andi : (p1 p2 : prop) -> (and [p1]) [p2],
ande : (m p1 p2 : prop) -> (h1 : (and [p1]) [p2]) -> (h2 : (a : p1) -> (b : p2) -> m) -> m,
by 
witness ((p1 : prop) => (p2 : prop) => SIGIL) ?