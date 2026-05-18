namespace CurryHoward.Logic.Syntax
  inductive Formula where
    | atom : String → Formula
    | impl : Formula → Formula → Formula
    | and  : Formula → Formula → Formula
    | or   : Formula → Formula → Formula
    | top  : Formula
    | bot  : Formula
  deriving Repr, DecidableEq
end CurryHoward.Logic.Syntax
