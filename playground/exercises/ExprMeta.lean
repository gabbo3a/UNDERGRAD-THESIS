import Lean
  open Lean

-- Create expression 1 + 2 with Expr.app
  -- mkAppN and mkRawNatLit are shortcut to write the same before expr
def a :=
  (Expr.app
    (Expr.app
      (Expr.const ``Nat.add [])
      (Expr.lit (.natVal 1)))
        (Expr.lit (.natVal 2)))

def b :=
  mkAppN (Expr.const ``Nat.add []) #[mkRawNatLit 1, mkRawNatLit 2]
#eval a
#eval b

-- Create expression fun x => 1 + x.
def c :=
  let body   := (mkAppN (Expr.const ``Nat.add []) #[mkRawNatLit 1, (.bvar 0)])
  let x_type := Expr.const ``Nat []
  Expr.lam `x x_type body BinderInfo.default
#eval c

-- [De Bruijn Indexes] Create expression fun a, fun b, fun c, (b * a) + c
def d :=
  let type := Expr.const ``Nat []
  let add  := Expr.const ``Nat.add []
  let mul  := Expr.const ``Nat.mul []
  let body := mkApp2 add (mkApp2 mul (.bvar 1) (.bvar 2)) (.bvar 0)
  (Expr.lam `a type
    (Expr.lam `b type
      (Expr.lam `c type body .default)
    .default)
  .default)
#eval d

-- Create expression fun x y => x + y
def e :=
  let type := Expr.const ``Nat []
  let add  := Expr.const ``Nat.add []
  let body := mkApp2 add (.bvar 0) (.bvar 0)
  Expr.lam `x type (Expr.lam `y type body .default) .default
#eval e


-- Create expression fun x, String.append "hello, " x
def f :=
  let append := Expr.const ``String.append []
  let slit   := Expr.lit (.strVal "hello, ")
  mkApp2 append slit (.bvar 0)
#eval f

-- Create expression ∀ x : Prop, x ∧ x.
def g :=
  let usort := Expr.sort Level.zero
  let body   :=  Expr.const ``And []
  Expr.forallE `x usort body .default
#eval g

-- Create expression Nat → String.
def h :=
  let nat := Expr.const ``Nat []
  let str := Expr.const ``String []
  Expr.forallE `_ nat str .default
#eval h

-- Create expression fun (p : Prop) => (λ hP : p => hP)
def i :=
  let usort := Expr.sort Level.zero

  Expr.lam `_ usort
    (Expr.lam `hp usort (.bvar 0) .default) .default
#eval i

-- [Universe levels] Create expression Type 6.
def j : Expr :=
  Expr.sort (Level.ofNat 6)
#eval j
