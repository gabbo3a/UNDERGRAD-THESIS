namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
open Nat

def sum (n m : Nat) : Nat :=
  match n with
  | zero    => m
  | succ n' => succ (sum n' m)

def mult (n m : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => sum m (mult n' m)

def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'

def sub (n m : Nat) : Nat :=
  match m with
  | zero    => n
  | succ m' => pred (sub n m')

def exp (base power : Nat) : Nat :=
  match power with
  | zero        => succ zero
  | succ power' => mult base (exp base power')

theorem sum_zero (n : Nat) : sum n zero = n := by
  induction n with
  | zero       => rfl
  | succ n' ih =>
    calc
      sum (succ n') zero
        = succ (sum n' zero)  := by rw[sum]
      _ = succ n'             := by rw[ih]

theorem sum_succ (m n : Nat) : sum m (succ n) = succ (sum m n) := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    calc
      sum (succ m') (succ n)
          = succ (sum m' (succ n)) := by rw [sum]
        _ = succ (succ (sum m' n)) := by rw [ih]
        _ = succ (sum (succ m') n) := by rw [sum]

theorem sum_comm (n m : Nat) : sum n m = sum m n := by
  induction n with
  | zero =>
    calc
      sum zero m
        = m          := by rw[sum]
      _ = sum m zero := by rw[sum_zero]
  | succ n' ih =>
    calc
      sum (succ n') m
        = succ (sum n' m) := by rw[sum]
      _ = succ (sum m n') := by rw[ih]
      _ = sum m (succ n') := by rw[sum_succ]

theorem sum_assoc (n m k : Nat) : sum n (sum m k) = sum (sum n m) k := by
  induction n with
  | zero =>
    calc
      sum zero (sum m k)
        = sum m k             := by rw[sum]
      _ = sum (sum zero m) k  := by rw[sum]
  | succ n' ih =>
    calc
      sum (succ n') (sum m k)
        = succ (sum n' (sum m k))   := by rw[sum]
      _ = succ (sum (sum n' m) k)   := by rw[ih]
      _ = succ (sum k (sum n' m))   := by rw[sum_comm]
      _ = sum k (succ (sum n' m))   := by rw[sum_succ]
      _ = sum k (sum (succ n') m)   := by rw[sum]
      _ = sum (sum (succ n') m) k   := by rw[sum_comm]

theorem mult_zero (n : Nat) : mult n zero = zero := by
  induction n with
  | zero =>
    calc
      mult zero zero = zero := by rfl
  | succ n' ih =>
    calc
      mult (succ n') zero
        = sum zero (mult n' zero) := by rw[mult]
      _ = sum zero zero           := by rw[ih]
      _ = zero                    := by rw[sum]

theorem mult_distrib_right (n m k : Nat) : mult (sum n m) k = sum (mult n k) (mult m k) := by
  induction n with
  | zero       => rfl
  | succ n' ih =>
    calc
      mult (sum (succ n') m) k
        = mult (succ (sum n' m)) k            := by rw[sum]
      _ = sum k (mult (sum n' m) k)           := by rw[mult]
      _ = sum k (sum (mult n' k) (mult m k))  := by rw[ih]
      _ = sum (sum k (mult n' k)) (mult m k)  := by rw[sum_assoc]
      _ = sum ((mult (succ n') k)) (mult m k)  := by rw[mult]

theorem succ_eq_sum_one (n : Nat) : sum n (succ zero) = succ n := by
  induction n with
  | zero    => rfl
  | succ n' ih =>
    calc
      sum (succ n') (succ zero)
        = succ (sum n' (succ zero)) := by rw[sum]
      _ = succ (succ n')            := by rw[ih]

/-
  To make the proof less verbose and convoluted, you should define
  a tactic/macro that receives a parse tree of Expr (defined in Lean)
  and returns a list or multiset of addends.

  To be able to process and permute them without going crazy,
  you would obviously also need theorems of invariance of the
  sum and a function for reversing.
-/
theorem mult_succ (m n : Nat) : mult m (succ n) = sum m (mult m n) := by
  induction m with
  | zero =>
    calc
      mult zero (succ n)
        = zero                    := by rw [mult]
      _ = sum zero zero           := by rw [sum]
      _ = sum zero (mult zero n)  := by rw [mult]
  | succ m' ih =>
    calc
      mult (succ m') (succ n)
        = sum (succ n) (mult m' (succ n))               := by rw[mult]
      _ = sum (succ n) (sum m' (mult m' n))             := by rw[ih]
      _ = sum (sum n (succ zero)) (sum m' (mult m' n))  := by rw[succ_eq_sum_one]
      _ = sum (sum (succ zero) n) (sum m' (mult m' n))  := by rw[sum_comm (succ zero) n]
      _ = sum (succ zero) (sum n (sum m' (mult m' n)))  := by rw[sum_assoc (succ zero)]
      _ = sum (succ zero) (sum (sum m' (mult m' n)) n)  := by rw[sum_comm n]
      _ = sum (succ zero) (sum m' (sum (mult m' n) n))  := by rw[sum_assoc m']
      _ = sum (sum (succ zero) m') (sum (mult m' n) n)  := by rw[sum_assoc (succ zero)]
      _ = sum (succ m') (sum (mult m' n) n)             := by simp[sum]
      _ = sum (succ m') (sum n (mult m' n))             := by rw[sum_comm n]
      _ = sum (succ m') (mult (succ m') n)              := by rw[mult]

theorem mult_comm (n m : Nat) : mult n m = mult m n := by
  induction n with
  | zero    =>
    calc
      mult zero m
        = zero        := by rw[mult]
      _ = mult m zero := by rw[mult_zero]
  | succ n' ih =>
    calc
      mult (succ n') m
        = sum m (mult n' m) := by rw[mult]
      _ = sum m (mult m n') := by rw[ih]
      _ =  mult m (succ n') := by rw[mult_succ]


theorem mult_distrib_left (m n k : Nat) :
  mult m (sum n k) = sum (mult m n) (mult m k) := by
  calc
    mult m (sum n k)
      = mult (sum n k) m          := by rw [mult_comm]
    _ = sum (mult n m) (mult k m) := by rw [mult_distrib_right]
    _ = sum (mult m n) (mult m k) := by rw [mult_comm n m, mult_comm k m]

end Hidden

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

namespace MyExp

inductive Term where
  | const (n : Nat)    : Term
  | var   (n : Nat)    : Term
  | plus  (s t : Term) : Term
  | times (s t : Term) : Term
open Term

def eval (env : Nat → Nat) : Term → Nat
  | const n   => n
  | var n     => env n
  | plus s t  => eval env s + eval env t
  | times s t => eval env s * eval env t

-- Test with (var 0 + 2) * var 1
def tenv : Nat → Nat
  | 0 => 5
  | 1 => 10
  | _ => 0

def tterm : Term :=
  Term.times (Term.plus (Term.var 0) (Term.const 2)) (Term.var 1)

#eval eval tenv tterm

def simpc : Term → Term
  | plus  (const n₁) (const n₂) => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Term → Term
  | const n   => const n
  | var n     => var n
  | plus s t  => simpc (plus  (fuse s) (fuse t))
  | times s t => simpc (times (fuse s) (fuse t))

theorem simp_eq (env : Nat → Nat) : ∀ e : Term, eval env (simpc e) = eval env e := by
  intro e
  induction e with
  | const n  => rfl
  | var n    => rfl
  | plus s t =>
    unfold simpc
    split
    · rename_i _ n₁ n₂ h
      calc
        eval env (const (n₁ + n₂))
          = n₁ + n₂                                     := by rfl
          _ = eval env (const n₁) + eval env (const n₂) := by rfl
          _ = eval env (plus (const n₁) (const n₂))     := by rfl
          _ = eval env (plus s t)                       := by rw[h]
    · contradiction
    · rfl
  | times s t ih_s ih_t =>
    unfold simpc
    split
    · contradiction
    · rename_i _ n₁ n₂ h
      calc
        eval env (const (n₁ * n₂))
          = n₁ * n₂                                     := by rfl
          _ = eval env (const n₁) * eval env (const n₂) := by rfl
          _ = eval env (times (const n₁) (const n₂))    := by rfl
          _ = eval env (times s t)                      := by rw[h]
    · rfl

theorem fuse_eq (env : Nat → Nat) : ∀ e : Term, eval env (fuse e) = eval env e := by
  intro e
  induction e with
  | const n => rfl
  | var n   => rfl
  | plus s t ih_s ih_t =>
      calc
        eval env (fuse (plus s t))
          = eval env (simpc (plus (fuse s) (fuse t)))   := by rw[fuse]
        _ = eval env (plus (fuse s) (fuse t))           := by rw[simp_eq]
        _ = eval env (fuse s) + eval env (fuse t)       := by rfl
        _ = eval env s + eval env t                     := by rw[ih_s, ih_t]
        _ = eval env (plus s t)                         := by rw[eval]
  | times s t ih_s ih_t =>
     calc
        eval env (fuse (times s t))
          = eval env (simpc (times (fuse s) (fuse t)))  := by rw[fuse]
        _ = eval env (times (fuse s) (fuse t))          := by rw[simp_eq]
        _ = eval env (fuse s) * eval env (fuse t)       := by rfl
        _ = eval env s * eval env t                     := by rw[ih_s, ih_t]
        _ = eval env (times s t)                        := by rw[eval]

end MyExp

namespace MyProp

inductive PropExp where
  | trh                  : PropExp
  | fls                  : PropExp
  | var  (n : Nat)       : PropExp
  | conj (p q : PropExp) : PropExp
  | disj (p q : PropExp) : PropExp
  | impl (p q : PropExp) : PropExp
open PropExp

def eval (env : Nat → Bool) : PropExp → Bool
  | trh      => true
  | fls      => false
  | var n    => env n
  | conj p q => eval env p && eval env q
  | disj p q => eval env p || eval env q
  | impl p q => !(eval env p) || eval env q

def tenv : Nat → Bool
  | 0 => true
  | 1 => false
  | _ => false

#eval eval tenv (impl (var 0) (var 1))
#eval eval tenv (impl (var 1) fls)
#eval eval tenv (disj (var 0) (var 1))

-- TODO: complexity and replacement
end MyProp
