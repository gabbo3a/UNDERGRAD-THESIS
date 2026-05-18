import Init.Data.Vector
import CurryHoward.Lambda.Syntax
import CurryHoward.Lambda.Typing
import CurryHoward.Logic.Syntax
import CurryHoward.Logic.Derivation
import CurryHoward.Context

namespace CurryHoward.Isomorphism.ToLambda
  open CurryHoward.Lambda.Syntax
  open CurryHoward.Lambda.Typing
  open CurryHoward.Logic.Syntax
  open CurryHoward.Logic.Derivation
  open CurryHoward.Context

  def φ : Formula → LType
    | .atom s    => .base s
    | .impl a b  => .arrow (φ a) (φ b)
    | .and  a b  => .prod  (φ a) (φ b)
    | .or   a b  => .sum   (φ a) (φ b)
    | .top       => .unit
    | .bot       => .void

  def φ_lift {n : Nat} : (Γ : Context Formula n) → Context LType n :=
    Vector.map φ

  theorem φ_lift_get_eq
    {n : Nat} (Γ : Context Formula n) (i : Fin n) :
    (φ_lift Γ).get i = φ (Γ.get i) := by sorry

  theorem ctx_extend_eq
    {n : Nat} (A : Formula) (Γ : Context Formula n) :
    φ_lift (extend A Γ) = extend (φ A) (φ_lift Γ) := by sorry

  def extract
    {n : Nat} {Γ : Context Formula n} {A : Formula} (d : Derivation Γ A) :
    Σ (t : Term), Typing (φ_lift Γ) t (φ A) :=
    match d with
    | .hyp i =>
      ⟨Term.var i, (φ_lift_get_eq Γ i)▸ .var i⟩

    | .implI A B tree =>
      have h_ctx := ctx_extend_eq A Γ
      let ⟨t_sub, tree_sub⟩ := extract tree
      let casted_tree := h_ctx ▸ tree_sub
      ⟨Term.lam (φ A) t_sub, .lam (φ A) (φ B) t_sub casted_tree⟩

    | .implE A B tree₁ tree₂ =>
      let ⟨t₁, proof₁⟩ := extract tree₁
      let ⟨t₂, proof₂⟩ := extract tree₂
      ⟨Term.app t₁ t₂, .app t₁ t₂ (φ A) (φ B) proof₁ proof₂⟩

    | .andI A B tree₁ tree₂ =>
      let ⟨t₁, proof₁⟩ := extract tree₁
      let ⟨t₂, proof₂⟩ := extract tree₂
      ⟨Term.pair t₁ t₂, .pair t₁ t₂ (φ A) (φ B) proof₁ proof₂⟩

    | .andE1 A B tree =>
      let ⟨t, proof⟩ := extract tree
      ⟨Term.fst t, .fst t (φ A) (φ B) proof⟩

    | .andE2 A B tree =>
      let ⟨t, proof⟩ := extract tree
      ⟨Term.snd t, .snd t (φ A) (φ B) proof⟩

    | .orI1 A B tree =>
      let ⟨t, proof⟩ := extract tree
      ⟨Term.inl (φ B) t, .inl t (φ A) (φ B) proof⟩

    | .orI2 A B tree =>
      let ⟨t, proof⟩ := extract tree
      ⟨Term.inr (φ A) t, .inr t (φ A) (φ B) proof⟩

    | .orE A B C tree₀ tree₁ tree₂ =>
      let ⟨t₀, proof₀⟩ := extract tree₀
      let ⟨t₁, proof₁⟩ := extract tree₁
      let ⟨t₂, proof₂⟩ := extract tree₂
      have h_ctx₁ := ctx_extend_eq A Γ
      have h_ctx₂ := ctx_extend_eq B Γ
      ⟨Term.cases t₀ t₁ t₂, .cases t₀ t₁ t₂ (φ C) (φ A) (φ B)
        proof₀ (h_ctx₁ ▸ proof₁) (h_ctx₂ ▸ proof₂)⟩

    | .topI =>
      ⟨Term.unit, .unit⟩

    | .botE A tree =>
      let ⟨t, proof⟩ := extract tree
      ⟨Term.absurd (φ A) t, .absurd (φ A) t proof⟩
end CurryHoward.Isomorphism.ToLambda
