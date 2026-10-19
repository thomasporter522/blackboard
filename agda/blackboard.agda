open import Data.Nat renaming (ℕ to nat)
open import Data.List hiding (ap)

mutual 
    data ctx : Set where 
        emtpy : ctx 
        cons : (c : ctx) -> term c -> ctx

    data var : ctx -> Set where 
        z : ∀{c a} -> var (cons c a)
        s : ∀{c a} -> var c -> var (cons c a)

    data term (c : ctx) : Set where 
        typ : term c 
        prop : term c
        mem : term c -> term c -> term c
        strongarrow : (a : term c) -> term (cons c a) -> term c
        arrow : (a : term c) -> term (cons c a) -> term c
        lambda : (a : term c) -> term (cons c a) -> term c
        x : var c -> term c
        ap : term c -> term c -> term c
        -- unguard : term c -> term c

wk : {c : ctx} -> (a : term c) -> term c -> term (cons c a)
wk a t = {!   !}

data ⊢x : (c : ctx) -> var c -> term c -> Set where 
    XZ : {c : ctx} ->
        {a : term c} -> 
        (z : var (cons c a)) -> 
        ⊢x (cons c a) z (wk a a)
    
