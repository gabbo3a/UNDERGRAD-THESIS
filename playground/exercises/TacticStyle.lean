open Classical

-- PropositionalLogic
variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    cases h with
    | intro hp hq =>
      constructor
      exact hq
      exact hp
  · intro h
    cases h with
    | intro hq hp =>
      constructor
      exact hp
      exact hq

example : p ∨ q ↔ q ∨ p := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      right
      exact hp
    | inr hq =>
      left
      exact hq
  · intro h
    cases h with
    | inl hq =>
      right
      exact hq
    | inr hp =>
      left
      exact hp

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro h
    match h with
    | ⟨⟨hp, hq⟩, hr⟩ => exact ⟨hp, ⟨hq, hr⟩⟩
  · intro h
    match h with
    | ⟨hp, ⟨hq, hr⟩⟩=> exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro h
    match h with
    | .inl hl =>
      match hl with
      | .inl hp => exact .inl hp
      | .inr hq => exact .inr (.inl hq)
    | .inr hr => exact .inr (.inr hr)
  · intro h
    match h with
    | .inl hp => exact .inl (.inl hp)
    | .inr hr =>
      match hr with
      | .inl hq => exact .inl (.inr hq)
      | .inr hr => exact .inr hr

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    match h with
    | ⟨hp, .inl hq⟩ => exact .inl ⟨hp, hq⟩
    | ⟨hp, .inr hr⟩ => exact .inr ⟨hp, hr⟩
  · intro h
    match h with
    | .inl ⟨hp, hq⟩ => exact ⟨hp, .inl hq⟩
    | .inr ⟨hp, hr⟩ => exact ⟨hp, .inr hr⟩

-- Other properties

-- Curry Haskell law
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  · intro h
    intro hand
    match hand with
    | ⟨hp, hq⟩ => exact h hp hq
  · intro h
    intro hp hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · intro h
    constructor
    · intro hp
      apply h
      exact .inl hp
    · intro hq
      apply h
      exact .inr hq
  · intro h
    match h with
    | ⟨hl, hr⟩ =>
      intro hor
      match hor with
      | .inl hp =>
        exact hl hp
      | .inr hq =>
        exact hr hq

-- De morgan law
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (.inl hp)
    · intro hq
      exact h (.inr hq)
  · intro h
    match h with
    | ⟨hnp, hnq⟩ =>
      intro hor
      match hor with
      | .inl hp => exact hnp hp
      | .inr hq => exact hnq hq

example : ¬p ∨ ¬q ↔ ¬(p ∧ q) := by
  constructor
  · intro hor ⟨hp, hq⟩
    match hor with
    | .inl hnp => exact hnp hp
    | .inr hnq => exact hnq hq
  · intro h
    match Classical.em p with
    | .inl hp =>
      apply Or.inr
      intro hq
      exact h ⟨hp, hq⟩
    | .inr hnp =>
      exact .inl hnp

example : ¬(p ∧ ¬p) := by
  intro h
  match h with
  | ⟨hp, hnp⟩ => exact hnp hp

example : p ∧ ¬q → ¬(p → q) := by
  intro h
  match h with
  | ⟨hp, hnq⟩ =>
    intro hf
    exact hnq (hf hp)

-- Deep intro
example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ hf
  exact hnq (hf hp)

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro hor hp
  match hor with
  | .inl hnp => contradiction
  | .inr hq => exact hq

example : p ∨ False ↔ p := by
  constructor
  · intro h
    match h with
    | .inl hp => exact hp
    | .inr hf => contradiction
  · intro hp
    exact .inl hp

example : p ∧ False ↔ False := by
  constructor
  · intro ⟨hp, hf⟩
    exact hf
  · intro hf
    contradiction

example : (p → q) → (¬q → ¬p) := by
  intro hf hnq hp
  exact hnq (hf hp)

-- FirstOrderLogic
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro ⟨w, hr⟩; exact hr

example (a : α) : r → (∃ _ : α, r) := by
  intro h; exact ⟨a, h⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  · intro ⟨w, ⟨hpw, hr⟩⟩
    exact ⟨⟨w, hpw⟩, hr⟩
  · intro ⟨⟨w, hpw⟩, hr⟩
    exact ⟨w, ⟨hpw, hr⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro ⟨w, hor⟩
    match hor with
    | .inl hp => exact .inl ⟨w, hp⟩
    | .inr hq => exact .inr ⟨w, hq⟩
  · intro hor
    match hor with
    | .inl ⟨w, hp⟩ => exact ⟨w, .inl hp⟩
    | .inr ⟨w, hq⟩ => exact ⟨w, .inr hq⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  · intro h₁ ⟨w, hnpw⟩
    exact hnpw (h₁ w)
  · intro h w
    by_cases hpw : p w
    · exact hpw
    · exact absurd ⟨w, hpw⟩ h

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  · intro ⟨w, hpw⟩ h
    exact h w hpw
  · intro h
    apply byContradiction
    intro hngoal
    have hnpx : ∀ x, ¬ p x :=
      (fun x hpx => hngoal ⟨x, hpx⟩)
    exact h hnpx

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  · intro h x hpx
    exact h ⟨x, hpx⟩
  · intro h ⟨w, hpw⟩
    exact h w hpw

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  · intro h
    apply byContradiction
    intro hng
    have hall: ∀ x, p x :=
      (fun x =>
        byContradiction
        (fun hnpx => hng ⟨x, hnpx⟩))
    exact absurd hall h
  · intro ⟨w, hnpw⟩ h
    exact hnpw (h w)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  · intro h ⟨w, hpw⟩
    exact h w hpw
  · intro h w hpw
    exact h ⟨w, hpw⟩

-- Not constructive proof are difficult
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  · intro ⟨w, hw⟩ hux
    exact hw (hux w)
  · sorry

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  · intro ⟨w, hw⟩ hr
    have f : r → p w :=
      fun hr => hw hr
    exact ⟨w, f hr⟩
  · intro h
    by_cases hr: r
    · have hex := h hr
      match hex with
      | ⟨w, hpw⟩ => exact ⟨w, (fun _ => hpw)⟩
    · exact ⟨a, fun hr_falsa => (hr hr_falsa).elim⟩

-- Use tactic combinators to obtain a one-line proof of the following:
example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat constructor <;> simp [hp]
