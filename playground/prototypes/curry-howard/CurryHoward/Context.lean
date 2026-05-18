import Init.Data.Vector

namespace CurryHoward.Context
  abbrev Context (α : Type u) := List α

  -- abbrev Context (α : Type u) (n : Nat) := Vector α n
  -- def Empty {α : Type u} : Context α 0 := ⟨#[], rfl⟩
  -- def extend {α : Type u} {n : Nat} (x : α) (Γ : Context α n) : Context α (n + 1) :=
  --  ⟨(x :: Γ.toList).toArray, by simp⟩
end CurryHoward.Context
