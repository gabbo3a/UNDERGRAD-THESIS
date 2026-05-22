import CurryHoward.Logic.Syntax
import CurryHoward.Context

namespace CurryHoward.Logic.Derivation
  open CurryHoward.Context
  open CurryHoward.Logic.Syntax

  inductive Derivation : Context Formula → Formula → Type where
    | hyp (i : Fin Γ.length) :
      Derivation Γ (Γ.get i)

    | implI (A B : Formula) :
      Derivation (A :: Γ) B
      → Derivation Γ (Formula.impl A B)

    | implE (A B : Formula) :
      Derivation Γ (Formula.impl A B)
      → Derivation Γ A
      → Derivation Γ B

    | andI (A B : Formula) :
      Derivation Γ A
      → Derivation Γ B
      → Derivation Γ (Formula.and A B)

    | andE1 (A B : Formula) :
      Derivation Γ (Formula.and A B)
      → Derivation Γ A

    | andE2 (A B : Formula) :
      Derivation Γ (Formula.and A B)
      → Derivation Γ B

    | orI1 (A B : Formula) :
      Derivation Γ A
      → Derivation Γ (Formula.or A B)

    | orI2 (A B : Formula) :
      Derivation Γ B
      → Derivation Γ (Formula.or A B)

    | orE (A B C : Formula) :
      Derivation Γ (Formula.or A B)
      → Derivation (A :: Γ) C
      → Derivation (B :: Γ) C
      → Derivation Γ C

    | topI :
      Derivation Γ Formula.top

    | botE (A : Formula) :
      Derivation Γ Formula.bot
      → Derivation Γ A
  deriving Repr

  def bind (depth : Nat) (A : Formula) (Γ : Context Formula) : Context Formula :=
    (Γ.take depth) ++ (A :: Γ.drop depth)

  axiom subst {Γ : Context Formula} {A B : Formula} (depth : Nat) :
    Derivation (bind depth A Γ) B → Derivation Γ A → Derivation Γ B

  noncomputable def instantiate {Γ : Context Formula} {A B : Formula}
      (body : Derivation (A :: Γ) B) (arg : Derivation Γ A) : Derivation Γ B :=
    subst 0 body arg
end CurryHoward.Logic.Derivation
