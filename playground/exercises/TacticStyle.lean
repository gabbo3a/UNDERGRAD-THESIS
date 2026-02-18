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
