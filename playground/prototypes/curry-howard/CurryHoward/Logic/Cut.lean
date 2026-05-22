import CurryHoward.Logic.Syntax
import CurryHoward.Logic.Derivation
import CurryHoward.Context

namespace CurryHoward.Logic.Cut
  open CurryHoward.Context
  open CurryHoward.Logic.Syntax
  open CurryHoward.Logic.Derivation

  noncomputable def step {Γ : Context Formula} {A : Formula}
    (d : Derivation Γ A) : Option (Derivation Γ A) :=
    match d with
    -- Implication
    | .implI A B body =>
      match step body with
      | some body' => some (.implI A B body')
      | none       => none

    | .implE _ _ (.implI A B body) arg =>
      some (instantiate body arg)
    | .implE A B d₁ d₂ =>
      match step d₁ with
      | some d₁' => some (.implE A B d₁' d₂)
      | none =>
        match step d₂ with
        | some d₂' => some (.implE A B d₁ d₂')
        | none => none

    -- And
    | .andI A B d₁ d₂ =>
      match step d₁ with
      | some d₁' => some (.andI A B d₁' d₂)
      | none     =>
        match step d₂ with
        | some d₂' => some (.andI A B d₁ d₂')
        | none     => none

    | .andE1 A _ (.andI _ _ d_A _) =>
      some d_A
    | .andE1 A B d' =>
      match step d' with
      | some d'' => some (.andE1 A B d'')
      | none     => none

    | .andE2 _ B (.andI _ _ _ d_B) =>
      some d_B
    | .andE2 A B d' =>
      match step d' with
      | some d'' => some (.andE2 A B d'')
      | none     => none

    -- Or
    | .orI1 A B d' =>
      match step d' with
      | some d'' => some (.orI1 A B d'')
      | none     => none
    | .orI2 A B d' =>
      match step d' with
      | some d'' => some (.orI2 A B d'')
      | none     => none

    | .orE _ _ _ (.orI1 A B d_A) d_C1 _ =>
      some (instantiate d_C1 d_A)
    | .orE _ _ _ (.orI2 A B d_B) _ d_C2 =>
      some (instantiate d_C2 d_B)
    | .orE A B C d₀ d₁ d₂ =>
      match step d₀ with
      | some d₀' => some (.orE A B C d₀' d₁ d₂)
      | none     =>
        match step d₁ with
        | some d₁' => some (.orE A B C d₀ d₁' d₂)
        | none     =>
          match step d₂ with
          | some d₂' => some (.orE A B C d₀ d₁ d₂')
          | none     => none

    -- 4. Absurd
    | .botE A d' =>
      match step d' with
      | some d'' => some (.botE A d'')
      | none     => none

    -- 5. Atomic Normal Forms
    | .hyp _ => none
    | .topI  => none

  noncomputable def normalize {Γ : Context Formula} {A : Formula} (fuel : Nat) (d : Derivation Γ A) : Derivation Γ A :=
    match fuel with
    | 0         => d
    | fuel' + 1 =>
      match step d with
      | some d' => normalize fuel' d'
      | none    => d

  noncomputable def isNormalForm {Γ : Context Formula} {A : Formula} (d : Derivation Γ A) : Bool :=
    (step d).isNone

  theorem normalize_converged {Γ : Context Formula} {A : Formula} {d : Derivation Γ A} {n : Nat} :
      (h : normalize (n + 1) d = normalize n d) → isNormalForm (normalize n d) := by
    sorry
end CurryHoward.Logic.Cut
