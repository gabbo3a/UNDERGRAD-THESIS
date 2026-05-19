import CurryHoward.Lambda.Syntax
import CurryHoward.Lambda.Typing
import CurryHoward.Logic.Syntax
import CurryHoward.Logic.Derivation
import CurryHoward.Context

namespace CurryHoward.Isomorphism.ToLogic
  open CurryHoward.Lambda.Syntax
  open CurryHoward.Lambda.Typing
  open CurryHoward.Logic.Syntax
  open CurryHoward.Logic.Derivation
  open CurryHoward.Context

  def iφ : LType → Formula
    | .base  s   => .atom s
    | .arrow a b => .impl (iφ a) (iφ b)
    | .prod  a b => .and  (iφ a) (iφ b)
    | .sum   a b => .or   (iφ a) (iφ b)
    | .unit      => .top
    | .void      => .bot

  def iφ_lift (Γ : Context LType) : Context Formula :=
    Γ.map iφ

  theorem ctx_extend_eq (σ : LType) (Γ : Context LType) :
    iφ_lift (σ :: Γ) = (iφ σ) :: (iφ_lift Γ) := by
    rfl

  theorem iφ_lift_get_eq (Γ : Context LType) :
    ∀ (i : Fin Γ.length),
    let hl : (iφ_lift Γ).length = Γ.length := by simp [iφ_lift]
    let i' : Fin (iφ_lift Γ).length := ⟨i.val, hl.symm ▸ i.isLt⟩
    iφ (Γ.get i) = (iφ_lift Γ).get i' := by simp [iφ_lift]

  def embed {Γ : Context LType} {t : Term} {σ : LType}
    (p : Typing Γ t σ) : Derivation (iφ_lift Γ) (iφ σ) :=
    match p with
    | .var i =>
      have h_len : Γ.length = (iφ_lift Γ).length := by simp [iφ_lift]
      let i' := Fin.cast h_len i
      let hyp_proof := Derivation.hyp i'
      (iφ_lift_get_eq Γ i).symm ▸ hyp_proof

    | .lam σ₁ σ₂ t tree =>
      have h_ctx := ctx_extend_eq σ₁ Γ
      let sproof := embed tree
      let casted_tree := h_ctx ▸ sproof
      .implI (iφ σ₁) (iφ σ₂) casted_tree

    | .app t₁ t₂ σ₁ σ₂ tree₁ tree₂ =>
      let proof₁ := embed tree₁
      let proof₂ := embed tree₂
      .implE (iφ σ₁) (iφ σ₂) proof₁ proof₂

    | .pair t₁ t₂ σ₁ σ₂ tree₁ tree₂ =>
      let proof₁ := embed tree₁
      let proof₂ := embed tree₂
      .andI (iφ σ₁) (iφ σ₂) proof₁ proof₂

    | .fst t σ₁ σ₂ tree =>
      let proof := embed tree
      .andE1 (iφ σ₁) (iφ σ₂) proof

    | .snd t σ₁ σ₂ tree =>
      let proof := embed tree
      .andE2 (iφ σ₁) (iφ σ₂) proof

    | .inl t σ₁ σ₂ tree =>
      let proof := embed tree
      .orI1 (iφ σ₁) (iφ σ₂) proof

    | .inr t σ₁ σ₂ tree =>
      let proof := embed tree
      .orI2 (iφ σ₁) (iφ σ₂) proof

    | .cases t₀ t₁ t₂ σ₀ σ₁ σ₂ tree₀ tree₁ tree₂ =>
      let proof₀ := embed tree₀
      let proof₁ := embed tree₁
      let proof₂ := embed tree₂
      have h_ctx₁ := ctx_extend_eq σ₁ Γ
      have h_ctx₂ := ctx_extend_eq σ₂ Γ
      .orE (iφ σ₁) (iφ σ₂) (iφ σ₀)
        proof₀ (h_ctx₁ ▸ proof₁) (h_ctx₂ ▸ proof₂)

    | .unit =>
      .topI

    | .absurd σ t tree =>
      let proof := embed tree
      .botE (iφ σ) proof

end CurryHoward.Isomorphism.ToLogic
