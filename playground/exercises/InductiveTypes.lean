-- TODO: ex 1

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

open List

local notation "[]"    => nil
local infixr : 67 " :: " => cons

def length (xs: List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: xs => 1 + length xs

def append (xs ys: List α) : List α :=
  match xs, ys with
  | [], ys       => ys
  | x :: xs', ys => x :: (append xs' ys)

local infixr : 65 " ++ " => append

/-
def reverse (xs: List α) : List α :=
  aux xs []
where
  aux : List α → List α → List α
  | [], acc       => acc
  | x :: xs', acc => aux xs' (x :: acc)
-/

def reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ (x :: [])

-- Prove some properties, such as the following:
variable {α : Type} (xs ys zs : List α)

theorem length_add : length (xs ++ ys) = length xs + length ys := by
  induction xs with
  | nil =>
    calc
      length (nil ++ ys)
        = length ys               := by rw [append]
      _ = 0 + length ys           := by rw [Nat.zero_add]
      _ = length nil + length ys  := by rw [length]
  | cons x xs' ih =>
    calc
      length ((cons x xs') ++ ys)
        = length (cons x (xs' ++ ys))     := by rw [append]
      _ = 1 + length (xs' ++ ys)          := by rw [length]
      _ = 1 + (length xs' + length ys)    := by rw [ih]
      _ = (1 + length xs') + length ys    := by rw [Nat.add_assoc]
      _ = length (cons _ xs') + length ys := by rw [length]

example : length (reverse xs) = length xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih  =>
    calc
      length (reverse (x :: xs'))
        = length (reverse xs' ++ (x :: []))       := by rw [reverse]
      _ = length (reverse xs') + length (x :: []) := by rw [length_add]
      _ = length xs' + length (x :: [])           := by rw [ih]
      _ = length xs' + 1                          := by simp [length]
      _ = 1 + length xs'                          := by rw [Nat.add_comm]
      _ = length (x :: xs')                       := by rw [length]

theorem append_nil (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    calc
      (a :: as') ++ []
        = a :: (as' ++ []) := by rw [append]
      _ = a :: as'         := by rw [ih]

theorem append_assoc : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil =>
    calc
      ([] ++ ys) ++ zs
        = ys ++ zs          := by rw[append]
      _ = [] ++  (ys ++ zs) := by rw[append]
  | cons x xs' ih =>
    calc
      ((x :: xs') ++ ys) ++ zs
        = (x :: (xs' ++ ys)) ++ zs  := by rw[append]
      _ = x :: ((xs' ++ ys) ++ zs)  := by rw[append]
      _ = x :: (xs' ++ (ys ++ zs))  := by rw[ih]
      _ = (x :: xs' ++ (ys ++ zs))  := by rw[append]

theorem reverse_antidistrib
  : reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  induction xs with
  | nil =>
    calc
      reverse (nil ++ ys)
        = reverse ys                := by rw [append]
      _ = reverse ys ++ []          := by rw [append_nil]
      _ = reverse ys ++ reverse []  := by rw [reverse]
  | cons x xs' ih =>
    calc
       reverse (x :: xs' ++ ys)
      _ = reverse (x :: (xs' ++ ys))                    := by rw[append]
      _ = reverse (xs' ++ ys) ++ (x :: [])              := by rw[reverse]
      _ = (reverse (ys) ++ reverse xs') ++ (x :: [])    := by rw[ih]
      _ = reverse (ys) ++ (reverse xs' ++ (x :: []))    := by rw[append_assoc]
      _ = reverse (ys) ++ reverse (x :: xs')            := by rw[reverse]

-- Can be replaced with da simp[append]
-- theorem singleton_append : (x :: []) ++ xs = (x :: xs) := by
--  sorry

example : reverse (reverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    calc
      reverse (reverse (cons x xs'))
        = reverse (reverse xs' ++ (x :: []))          := by rw[reverse]
      _ = reverse (x :: []) ++ reverse (reverse xs')  := by rw[reverse_antidistrib]
      _ = reverse (x :: []) ++ xs'                    := by rw[ih]
      _ = (reverse [] ++ (x :: [])) ++ xs'            := by simp[reverse]
      _ = ([] ++ (x :: [])) ++ xs'                    := by rw[reverse]
      _ = (x :: []) ++ xs'                            := by rw[append]
      _ = x :: xs'                                    := by simp[append]

end MyList

-- TODO: ex 3 and 4
