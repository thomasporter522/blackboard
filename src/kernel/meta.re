

module Meta = {
    type t = Meta(int);
    let mint (n : int) = Meta(n);
    let equiv (Meta(n1), Meta(n2)) = n1 == n2;
    let compare(Meta(n1), Meta(n2)) = n1 - n2;
    let string_of_meta(Meta(n)) = string_of_int(n)
}

type meta = Meta.t;
