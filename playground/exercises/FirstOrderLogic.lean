open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
    (fun h =>
        Exists.elim h (fun (_: α) (hr: r) => hr))

example (a : α) : r → (∃ _ : α, r) :=
    (fun h => Exists.intro a h)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    ⟨(fun h =>
        match h with
        | ⟨w, ⟨hp, hr⟩⟩ => ⟨⟨w, hp⟩, hr⟩
    ),
    (fun h =>
        match h with
        |  ⟨⟨w, hp⟩, hr⟩ => ⟨w, ⟨hp, hr⟩⟩
    )⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    ⟨(fun h =>
        match h with
        | ⟨w, .inl hp⟩ => .inl (⟨w, hp⟩)
        | ⟨w, .inr hq⟩ => .inr (⟨w, hq⟩)
    ),
    (fun h =>
        match h with
        | .inl ⟨w, hp⟩ => ⟨w, .inl hp⟩
        | .inr ⟨w, hq⟩ => ⟨w, .inr hq⟩
    )⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    ⟨(fun h₁ =>
        (fun h₂ =>
            match h₂ with
            | ⟨w, npw⟩ => npw (h₁ w)
        )),
    (fun h₁ =>
        byContradiction
            (fun h₂ =>
                let hall : ∀ x, p x :=
                    (fun x =>
                        byContradiction
                            (fun hnp => h₁ ⟨x, hnp⟩)
                    )
                h₂ hall
            )
    )⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    ⟨(fun h₁ =>
        fun h₂ =>
            match h₁ with
            | ⟨w, hpw⟩ => h₂ w hpw
    ),
    (fun h₁ =>
        byContradiction
            (fun h₂ =>
                let hnpx : ∀ x, ¬ p x :=
                    fun x => fun hpx => h₂ ⟨x, hpx⟩
                h₁ hnpx)
    )⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    ⟨(fun h₁ =>
        (fun x =>
            (fun hpx => h₁ ⟨x, hpx⟩))),
    (fun h₁ =>
        fun h₂ =>
            match h₂ with
            | ⟨w, hpw⟩ => (h₁ w) hpw
    )⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    ⟨(fun h₁ =>
        -- Use contradiction until you have all logical item to obtain false with h₁ function
        byContradiction
            (fun h₂ =>
                let hall: ∀ x, p x :=
                    (fun x =>
                        byContradiction
                            (fun hnpx => h₂ ⟨x, hnpx⟩)
                    )
                h₁ hall
            )
    ),
    (fun h₁ =>
        fun h₂ =>
            match h₁ with
            | ⟨w, hnpx⟩ => hnpx (h₂ w))⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    ⟨(fun h₁ =>
        fun h₂ =>
            match h₂ with
            | ⟨w, hpw⟩ => h₁ w hpw
    ),
    (fun h₁ =>
        fun x =>
            fun hpx =>
                h₁ ⟨x, hpx⟩)⟩

-- Not constructive proof are difficult
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    ⟨(fun h₁ =>
        fun h₂ =>
            match h₁ with
            | ⟨w, hpw⟩ => hpw (h₂ w)
    ),
    (fun h₁ =>
        byContradiction
            (fun h₂ =>
               let hallp : ∀ x, p x :=
                    (fun x =>
                        byContradiction (
                            fun h_not_px =>
                            let hex : ∃ x, p x → r :=
                                ⟨x, (fun hpx => False.elim (h_not_px hpx))⟩
                            h₂ hex
                        )
                    )
                let hr : r := h₁ hallp
                h₂ ⟨a, fun _ => hr⟩
            )
    )⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    ⟨(fun h₁ =>
        match h₁ with
        | ⟨w, f⟩ =>
            (fun hr => ⟨w, f hr⟩)
    ),
    (fun h₁ =>
        match Classical.em r with
        | .inl hr =>
            match (h₁ hr) with
            | ⟨w, hpw⟩ => ⟨w, fun _ => hpw⟩
        | .inr hnr =>
            ⟨a, fun hr => False.elim (hnr hr)⟩
    )⟩
