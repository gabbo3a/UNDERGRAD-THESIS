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

  inductive Coherent : Derivation Γ A → (Σ (t : Term), Typing (φ_lift Γ) t (φ A)) → Prop where
    | hyp
      (Γ : Context Formula)
      (i : Fin Γ.length) :
      Coherent (.hyp i) (extract (.hyp i))

    | implI
      (Γ : Context Formula)
      (A B : Formula)
      (d : Derivation (A :: Γ) B)
      (jp : Σ (t : Term), Typing (φ_lift (A :: Γ)) t (φ B)) :
        Coherent d jp →
        Coherent (.implI A B d) ⟨Term.lam (φ A) jp.1, .lam (φ A) (φ B) jp.1 (ctx_extend_eq A Γ ▸ jp.2)⟩

    | implE
      (Γ : Context Formula)
      (A B : Formula)
      (d₁ : Derivation Γ (Formula.impl A B))
      (d₂ : Derivation Γ A)
      (jt₁ jt₂) :
        Coherent d₁ jt₁ →
        Coherent d₂ jt₂ →
        Coherent (.implE A B d₁ d₂) ⟨Term.app jt₁.1 jt₂.1, .app jt₁.1 jt₂.1 (φ A) (φ B) jt₁.2 jt₂.2⟩

    | andI
      (Γ : Context Formula)
      (A B : Formula)
      (d₁ : Derivation Γ A)
      (d₂ : Derivation Γ B)
      (jt₁ jt₂) :
        Coherent d₁ jt₁ →
        Coherent d₂ jt₂ →
        Coherent (.andI A B d₁ d₂) ⟨Term.pair jt₁.1 jt₂.1, .pair jt₁.1 jt₂.1 (φ A) (φ B) jt₁.2 jt₂.2⟩

    | andE1
      (Γ : Context Formula)
      (A B : Formula)
      (d : Derivation Γ (Formula.and A B)) (jt) :
        Coherent d jt →
        Coherent (.andE1 A B d) ⟨Term.fst jt.1, .fst jt.1 (φ A) (φ B) jt.2⟩

    | andE2
      (Γ : Context Formula)
      (A B : Formula)
      (d : Derivation Γ (Formula.and A B)) (jt) :
        Coherent d jt →
        Coherent (.andE2 A B d) ⟨Term.snd jt.1, Typing.snd jt.1 (φ A) (φ B) jt.2⟩

    | orI1 (Γ : Context Formula) (A B : Formula) (d : Derivation Γ A) (jt) :
        Coherent d jt →
        Coherent (.orI1 A B d) ⟨Term.inl (φ B) jt.1, .inl jt.1 (φ A) (φ B) jt.2⟩

    | orI2 (Γ : Context Formula) (A B : Formula) (d : Derivation Γ B) (jt) :
        Coherent d jt →
        Coherent (.orI2 A B d) ⟨Term.inr (φ A) jt.1, .inr jt.1 (φ A) (φ B) jt.2⟩

    | orE
      (Γ : Context Formula)
      (A B C : Formula)
      (d₀ : Derivation Γ (Formula.or A B))
      (d₁ : Derivation (A :: Γ) C)
      (d₂ : Derivation (B :: Γ) C) :
        Coherent d₀ (extract d₀) →
        Coherent d₁ (extract d₁) →
        Coherent d₂ (extract d₂) →
        Coherent (.orE A B C d₀ d₁ d₂) (extract (.orE A B C d₀ d₁ d₂))

    | topI (Γ : Context Formula) :
        Coherent .topI ⟨Term.unit, .unit⟩

    | botE
      (Γ : Context Formula)
      (A : Formula)
      (d : Derivation Γ .bot) :
        Coherent d (extract d) →
        Coherent (.botE A d) (extract (.botE A d))

  theorem extract_is_coherent {Γ : Context Formula} {A : Formula}
    (d : Derivation Γ A) :  Coherent d (extract d) := by
    induction d with
    | hyp i =>
      rename_i Γ_locale
      dsimp [extract]
      exact .hyp Γ_locale i

    | implI A B d ih =>
      rename_i Γ_locale
      dsimp [extract]
      exact .implI Γ_locale A B d (extract d) ih

    | implE A B d₁ d₂ ih₁ ih₂ =>
      rename_i Γ_locale
      dsimp [extract]
      exact .implE Γ_locale A B d₁ d₂ (extract d₁) (extract d₂) ih₁ ih₂

    | andI A B d₁ d₂ ih₁ ih₂ =>
      rename_i Γ_locale
      dsimp [extract]
      exact .andI Γ_locale A B d₁ d₂ (extract d₁) (extract d₂) ih₁ ih₂

    | andE1 A B d ih =>
      rename_i Γ_locale
      dsimp [extract]
      exact .andE1 Γ_locale A B d (extract d) ih

    | andE2 A B d ih =>
      rename_i Γ_locale
      dsimp [extract]
      exact .andE2 Γ_locale A B d (extract d) ih

    | orI1 A B d ih =>
      rename_i Γ_locale
      dsimp [extract]
      exact .orI1 Γ_locale A B d (extract d) ih

    | orI2 A B d ih =>
      rename_i Γ_locale
      dsimp [extract]
      exact .orI2 Γ_locale A B d (extract d) ih

    |  orE A B C d₀ d₁ d₂ ih₀ ih₁ ih₂ =>
      rename_i Γ_locale
      exact .orE Γ_locale A B C d₀ d₁ d₂ ih₀ ih₁ ih₂

    | topI =>
      rename_i Γ_locale
      dsimp [extract]
      exact .topI Γ_locale

    | botE A d ih =>
      rename_i Γ_locale
      exact .botE Γ_locale A d ih

  theorem embed_is_coherent {Γ : Context Formula} {A : Formula} {t : Term}
    (jt : Typing (φ_lift Γ) t (φ A)) :
    Coherent (
      have h_ctx : iφ_lift (φ_lift Γ) = Γ := by
        change (iφ_lift ∘ φ_lift) Γ = id Γ
        rw [iφ_lift_φ_lift_eq]
      have h_type : iφ (φ A) = A := by
        change (iφ ∘ φ) A = id A
        rw [iφ_φ_eq]
      h_ctx ▸ h_type ▸ (embed jt)
    ) ⟨t, jt⟩ := by sorry

end CurryHoward.Isomorphism.Theorems
