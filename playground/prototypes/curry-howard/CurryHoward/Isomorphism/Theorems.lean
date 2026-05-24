import CurryHoward.Lambda.Syntax
import CurryHoward.Lambda.Typing
import CurryHoward.Lambda.Reduction
import CurryHoward.Logic.Syntax
import CurryHoward.Logic.Derivation
import CurryHoward.Logic.Cut
import CurryHoward.Isomorphism.ToLambda
import CurryHoward.Isomorphism.ToLogic
import CurryHoward.Context

namespace CurryHoward.Isomorphism.Theorems
  open CurryHoward.Lambda.Syntax
  open CurryHoward.Lambda.Typing
  open CurryHoward.Lambda.Reduction
  open CurryHoward.Logic.Syntax
  open CurryHoward.Logic.Derivation
  open CurryHoward.Logic.Cut
  open CurryHoward.Isomorphism.ToLambda
  open CurryHoward.Isomorphism.ToLogic
  open CurryHoward.Context

  theorem iφ_φ_eq : iφ ∘ φ = id := by
    funext A
    induction A with
    | atom s => rfl
    | impl a b ha hb =>
      simp [Function.comp, id] at ha hb
      simp [φ, iφ]
      rw [ha, hb]
      exact ⟨rfl, rfl⟩
    | and a b ha hb =>
      simp [Function.comp, id] at ha hb
      simp [φ, iφ]
      rw [ha, hb]
      exact ⟨rfl, rfl⟩
    | or a b ha hb =>
      simp [Function.comp, id] at ha hb
      simp [φ, iφ]
      rw [ha, hb]
      exact ⟨rfl, rfl⟩
    | top => rfl
    | bot => rfl

  theorem iφ_lift_φ_lift_eq : iφ_lift ∘ φ_lift = id := by
    funext Γ
    simp [Function.comp, id]
    induction Γ with
    | nil         => rfl
    | cons A Γ ih =>
      simp [φ_lift, iφ_lift]
      simp [φ_lift, iφ_lift] at ih
      have hA : iφ (φ A) = A := by
        change (iφ ∘ φ) A = id A
        rw [iφ_φ_eq]
      constructor
      · exact hA
      · exact ih

end CurryHoward.Isomorphism.Theorems
