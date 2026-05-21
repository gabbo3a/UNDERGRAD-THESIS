import CurryHoward.Lambda.Syntax

namespace CurryHoward.Lambda.Reduction
  open CurryHoward.Lambda.Syntax

  def shift (d : Nat) (cutoff : Nat) (t : Term) : Term :=
    match t with
    | .var i          => if i >= cutoff then .var (i + d) else .var i
    | .lam σ body     => .lam σ (shift d (cutoff + 1) body)
    | .app t₁ t₂      => .app   (shift d cutoff t₁) (shift d cutoff t₂)
    | .pair t₁ t₂     => .pair  (shift d cutoff t₁) (shift d cutoff t₂)
    | .fst t'         => .fst   (shift d cutoff t')
    | .snd t'         => .snd   (shift d cutoff t')
    | .inl σ t'       => .inl σ (shift d cutoff t')
    | .inr σ t'       => .inr σ (shift d cutoff t')
    | .cases t₀ t₁ t₂ => .cases (shift d cutoff t₀) (shift d (cutoff + 1) t₁) (shift d (cutoff + 1) t₂)
    | .unit           => .unit
    | .absurd σ t'    => .absurd σ (shift d cutoff t')

  def subst (depth : Nat) (t : Term) (s : Term) : Term :=
    match t with
    | .var i =>
      if i == depth then shift depth 0 s
      else if i > depth then .var (i - 1)  -- Decrementa l'indice perché abbiamo rimosso un binder (quello ridotto)
      else /-(if i < depth)-/ .var i
    | .lam σ body     => .lam σ (subst (depth + 1) body s)
    | .app t₁ t₂      => .app (subst depth t₁ s) (subst depth t₂ s)
    | .pair t₁ t₂     => .pair (subst depth t₁ s) (subst depth t₂ s)
    | .fst t'         => .fst (subst depth t' s)
    | .snd t'         => .snd (subst depth t' s)
    | .inl σ t'       => .inl σ (subst depth t' s)
    | .inr σ t'       => .inr σ (subst depth t' s)
    | .cases t₀ t₁ t₂ => .cases (subst depth t₀ s) (subst (depth + 1) t₁ s) (subst (depth + 1) t₂ s)
    | .unit           => .unit
    | .absurd σ t'    => .absurd σ (subst depth t' s)

  def instantiate (body : Term) (arg : Term) : Term :=
    subst 0 body arg

  def step (t : Term) : Option Term :=
    match t with
    -- 1. Implication
    | .lam σ t =>
      match step t with
      | some t' => some (.lam σ t')
      | none    => none

    | .app (.lam _ t) arg =>
      some (instantiate t arg)
    | .app t₁ t₂ =>
      match step t₁ with
      | some t₁' => some (.app t₁' t₂)
      | none =>
        match step t₂ with
        | some t₂' => some (.app t₁ t₂')
        | none => none

    -- 2. Product
    | .pair t₁ t₂ =>
      match step t₁ with
      | some t₁' => some (.pair t₁' t₂)
      | none     =>
        match step t₂ with
        | some t₂' => some (.pair t₁ t₂')
        | none     => none

    | .fst (.pair M _) =>
      some M
    | .fst t' =>
      match step t' with
      | some t'' => some (.fst t'')
      | none     => none

    | .snd (.pair _ N) =>
      some N
    | .snd t' =>
      match step t' with
      | some t'' => some (.snd t'')
      | none     => none

    -- 3. Sum
    | .inl σ t' =>
      match step t' with
      | some t'' => some (.inl σ t'')
      | none     => none
    | .inr σ t' =>
      match step t' with
      | some t'' => some (.inl σ t'')
      | none     => none

    | .cases (.inl _ M) t₁ _ =>
      some (instantiate t₁ M)
    | .cases (.inr _ M) _ t₂ =>
      some (instantiate t₂ M)
    | .cases t₀ t₁ t₂ =>
      match step t₀ with
      | some t₀' => some (.cases t₀' t₁ t₂)
      | none     =>
        match step t₁ with
        | some t₁' => some (.cases t₀ t₁' t₂)
        | none     =>
          match step t₂ with
          | some t₂' => some (.cases t₀ t₁ t₂')
          | none     => none

    -- 4. Absurd
    | .absurd σ t' =>
      match step t' with
      | some t'' => some (.absurd σ t'')
      | none     => none

    -- 5. Atomic Normal Forms
    | .var _ => none
    | .unit  => none

  /- partial def normalize (t : Term) : Term :=
    match step t with
    | some t' => normalize t'
    | none    => t -/

  def normalize (fuel : Nat) (t : Term) : Term :=
    match fuel with
    | 0         => t
    | fuel' + 1 =>
      match step t with
      | some t' => normalize fuel' t'
      | none    => t

  def isNormalForm (t : Term) : Bool :=
    (step t).isNone

  theorem normalize_converged {t : Term} {n : Nat} :
    (h : normalize (n + 1) t = normalize n t) → isNormalForm (normalize n t) := by
  sorry
end CurryHoward.Lambda.Reduction
