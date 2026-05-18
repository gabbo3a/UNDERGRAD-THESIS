namespace CurryHoward.Lambda.Syntax
  inductive LType where
    | base  : String → LType
    | arrow : LType → LType → LType
    | prod  : LType → LType → LType
    | sum   : LType → LType → LType
    | unit  : LType
    | void  : LType
  deriving Repr, DecidableEq

  inductive Term where
    | var    : Nat → Term
    | lam    : LType → Term → Term
    | app    : Term → Term → Term
    | pair   : Term → Term → Term
    | fst    : Term → Term
    | snd    : Term → Term
    | inl    : LType → Term → Term
    | inr    : LType → Term → Term
    | cases  : Term → Term → Term → Term
    | unit   : Term
    | absurd : LType → Term → Term
  deriving Repr, DecidableEq
end CurryHoward.Lambda.Syntax
