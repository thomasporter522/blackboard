open import Data.Nat renaming (ℕ to nat)
open import Data.List hiding (ap)

data term : Set where 
    var : nat -> term 
    mem : term -> term -> term 
    typ : term 
    pi : term -> term -> term 
    ap : term -> term -> term 

ctx : Set 
ctx = List term

inctx : nat -> term -> ctx -> Set 
inctx = {!   !}


data _⊢_ : ctx -> term -> Set where 
    Var : ∀{x T c} -> 
        inctx x T c ->
        c ⊢ mem (var x) T
    ø : ∀{x T c} -> 
        inctx x T c ->
        c ⊢ mem (var x) T