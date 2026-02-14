variable (p q r : Prop)

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (h: p ∧ q) => And.intro (And.right h) (And.left h))
    (fun (h: q ∧ p) => And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (h : p ∨ q) =>
      match h with
      | Or.inl hp => Or.inr hp
      | Or.inr hq => Or.inl hq
    )
    (fun (h : q ∨ p) =>
      match h with
        | Or.inl hq => Or.inr hq
        | Or.inr hp => Or.inl hp
    )

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  /-(fun (h : (p ∧ q) ∧ r) =>
      let hpq := And.left h
      let hp  := And.left hpq
      let hq  := And.right hpq
      let hr  := And.right h
      And.intro hp (And.intro (hq) (hr))
    )-/
  Iff.intro
    (fun (⟨⟨hp, hq⟩, hr⟩)  => ⟨hp, ⟨hq, hr⟩⟩)
    (fun (⟨hp, ⟨hq, hr⟩⟩)  => ⟨⟨hp, hq⟩, hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨
    (fun
      | .inl (.inl hp) => .inl hp
      | .inl (.inr hq) => .inr (.inl hq)
      | .inr hr        => .inr (.inr hr)),
    (fun
      | .inl hp        => .inl (.inl hp)
      | .inr (.inl hq) => .inl (.inr hq)
      | .inr (.inr hr) => .inr hr)
⟩

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨
    (fun (⟨hp, hor⟩) =>
      match hor with
        | .inl hq => Or.inl (And.intro hp hq)
        | .inr hr => Or.inr (And.intro hp hr)
    ),
    (fun
    | Or.inl hl => And.intro hl.left (Or.inl hl.right)
    | Or.inr hr => And.intro hr.left (Or.inr hr.right)
    )
  ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
    (fun
      | .inl hl => .intro (.inl hl) (.inl hl)
      | .inr hr => .intro (.inr hr.left) (.inr hr.right)
    ),
    (fun
      | ⟨.inl hp, _⟩       => .inl hp
      | ⟨_, .inl hp⟩       => .inl hp
      | ⟨.inr hq, .inr hr⟩ => .inr (.intro hq hr)
    )
  ⟩

-- Other properties

-- Curry Haskell law
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    (fun f ⟨hp, hq⟩ =>
      f hp hq),
    (fun f hp hq =>
      f ⟨hp, hq⟩)
  ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    (fun (f : (p ∨ q) → r) =>
      And.intro
        (fun (hp: p) => f (.inl hp))
        (fun (hq: q) => f (.inr hq))
    ),
    (fun ⟨f, g⟩ =>
      fun hor =>
        match hor with
        | .inl hp => f hp
        | .inr hq => g hq
    )
  ⟩

-- De morgan law
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    (fun hnor =>
      And.intro
        (fun hp => hnor (.inl hp))
        (fun hq => hnor (.inr hq))
    ),
    (fun ⟨hnp, hnq⟩ =>
      fun
      | .inl hp => hnp hp
      | .inr hq => hnq hq
    )
  ⟩

example : ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
  ⟨
    (fun
      | .inl np => (fun ⟨hp, hq⟩ => np hp)
      | .inr nq => (fun ⟨hp, hq⟩ => nq hq)
    ),
    (sorry)
  ⟩

example : ¬(p ∧ ¬p) :=
  (fun ⟨hp, hnp⟩ =>
    hnp hp)

example : p ∧ ¬q → ¬(p → q) :=
  (fun ⟨hp, nq⟩ =>
    fun f => nq (f hp)
  )

example : ¬p → (p → q) :=
  (fun (hnp: ¬p) =>
    fun (hp: p) =>
      False.elim (hnp hp)
  )

example : (¬p ∨ q) → (p → q) :=
  (fun (hor: ¬p ∨ q) =>
    match hor with
    | .inl hnp => (fun hp: p => absurd hp hnp)
    | .inr hq  => (fun hp: p => hq)
  )

example : p ∨ False ↔ p :=
  ⟨
    (fun hor =>
      match hor with
      | .inl hp => hp
      | .inr hf => False.elim hf
    ),
    (fun hp =>
      .inl hp
    )
  ⟩

example : p ∧ False ↔ False :=
  ⟨
    (fun ⟨_, hf⟩ => hf),
    (fun hf => False.elim hf)
  ⟩

example : (p → q) → (¬q → ¬p) :=
  (fun (f : p → q) =>
    (fun nq =>
      (fun hp =>
        nq (f hp)
      )
    )
  )
