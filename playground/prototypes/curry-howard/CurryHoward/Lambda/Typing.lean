import CurryHoward.Lambda.Syntax
import CurryHoward.Context

namespace CurryHoward.Lambda.Typing
  open CurryHoward.Lambda.Syntax
  open CurryHoward.Context

  inductive Typing : Context LType → Term → LType → Type where
    | var {Γ : Context LType} (i : Fin Γ.length) :
        Typing Γ (Term.var i) (Γ.get i)

    | lam {Γ : Context LType} (σ₁ σ₂ : LType) (t : Term) :
        Typing (σ₁ :: Γ) t σ₂
        → Typing Γ (Term.lam σ₁ t) (LType.arrow σ₁ σ₂)

    | app {Γ : Context LType} (t₁ t₂ : Term) (σ₁ σ₂ : LType) :
        Typing Γ t₁ (LType.arrow σ₁ σ₂)
        → Typing Γ t₂ σ₁
        → Typing Γ (Term.app t₁ t₂) σ₂

    | pair {Γ : Context LType} (t₁ t₂ : Term) (σ₁ σ₂ : LType) :
        Typing Γ t₁ σ₁
        → Typing Γ t₂ σ₂
        → Typing Γ (Term.pair t₁ t₂) (LType.prod σ₁ σ₂)

    | fst {Γ : Context LType} (t : Term) (σ₁ σ₂ : LType) :
        Typing Γ t (LType.prod σ₁ σ₂)
        → Typing Γ (Term.fst t) σ₁

    | snd {Γ : Context LType} (t : Term) (σ₁ σ₂ : LType) :
        Typing Γ t (LType.prod σ₁ σ₂)
        → Typing Γ (Term.snd t) σ₂

    | inl {Γ : Context LType} (t : Term) (σ₁ σ₂ : LType) :
        Typing Γ t σ₁
        → Typing Γ (Term.inl σ₂ t) (LType.sum σ₁ σ₂)

    | inr {Γ : Context LType} (t : Term) (σ₁ σ₂ : LType) :
        Typing Γ t σ₂
        → Typing Γ (Term.inr σ₁ t) (LType.sum σ₁ σ₂)

    | cases {Γ : Context LType} (t₀ t₁ t₂ : Term) (σ₀ σ₁ σ₂ : LType) :
        Typing Γ t₀ (LType.sum σ₁ σ₂)
        → Typing (σ₁ :: Γ) t₁ σ₀
        → Typing (σ₂ :: Γ) t₂ σ₀
        → Typing Γ (Term.cases t₀ t₁ t₂) σ₀

    | unit {Γ : Context LType} :
        Typing Γ Term.unit LType.unit

    | absurd {Γ : Context LType} (σ : LType) (t : Term) :
        Typing Γ t LType.void
        → Typing Γ (Term.absurd σ t) σ
  deriving Repr

  def derive (Γ : Context LType) (t : Term) : Option (Σ σ, Typing Γ t σ) :=
    match t with
    | .var i =>
      if h : i < Γ.length then
        let idx : Fin Γ.length := ⟨i, h⟩
        some ⟨Γ.get idx, .var idx⟩
      else none

    | .lam σ₁ t => do
      let ⟨σ₂, tree⟩ ← derive (σ₁ :: Γ) t
      some ⟨.arrow σ₁ σ₂, .lam σ₁ σ₂ t tree⟩

    | .app t₁ t₂ => do
      let ⟨σ_fun, tree₁⟩ ← derive Γ t₁
      let ⟨σ_arg, tree₂⟩ ← derive Γ t₂
      match σ_fun with
      | .arrow τ₁ τ₂ =>
        if h : τ₁ = σ_arg then
          some ⟨τ₂, .app t₁ t₂ τ₁ τ₂ tree₁ (h ▸ tree₂)⟩
        else none
      | _ => none

    | .pair t₁ t₂ => do
      let ⟨σ₁, tree₁⟩ ← derive Γ t₁
      let ⟨σ₂, tree₂⟩ ← derive Γ t₂
      some ⟨.prod σ₁ σ₂, .pair t₁ t₂ σ₁ σ₂ tree₁ tree₂⟩

    | .fst t => do
      let ⟨σ, tree⟩ ← derive Γ t
      match σ with
      | .prod σ₁ _ => some ⟨σ₁, .fst t σ₁ _ tree⟩
      | _ => none

    | .snd t => do
      let ⟨σ, tree⟩ ← derive Γ t
      match σ with
      | .prod _ σ₂ => some ⟨σ₂, .snd t _ σ₂ tree⟩
      | _ => none

    | .inl σ₂ t => do
      let ⟨σ₁, tree⟩ ← derive Γ t
      some ⟨.sum σ₁ σ₂, .inl t σ₁ σ₂ tree⟩

    | .inr σ₁ t => do
      let ⟨σ₂, tree⟩ ← derive Γ t
      some ⟨.sum σ₁ σ₂, .inr t σ₁ σ₂ tree⟩

    | .cases t₀ t₁ t₂ => do
      let ⟨σ_sum, tree₀⟩ ← derive Γ t₀
      match σ_sum with
      | .sum σ₁ σ₂ =>
        let ⟨ρ₁, tree₁⟩ ← derive (σ₁ :: Γ) t₁
        let ⟨ρ₂, tree₂⟩ ← derive (σ₂ :: Γ) t₂
        if h : ρ₁ = ρ₂ then
          some ⟨ρ₁, .cases t₀ t₁ t₂ ρ₁ σ₁ σ₂ tree₀ tree₁ (h ▸ tree₂)⟩
        else none
      | _ => none

    | .unit =>
      some ⟨.unit, .unit⟩

    | .absurd σ t => do
      let ⟨σ_t, tree⟩ ← derive Γ t
      match σ_t with
      | .void => some ⟨σ, .absurd σ t tree⟩
      | _ => none
end CurryHoward.Lambda.Typing
