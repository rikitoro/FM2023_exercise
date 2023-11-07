import Mathlib.Tactic

inductive X : Type
| a : X
| b : X
| c : X

open X

#check a

example (x : X) : x = a ∨ x = b ∨ x = c :=
  by
  cases x
  . left
    rfl
  . right
    left
    rfl
  . right
    right
    rfl

example : a ≠ b :=
  by
  intro h
  cases h


def f : X → ℕ
| a => 37
| b => 42
| c => 0

example : f a = 37 :=
  by
  rfl

example : Function.Injective f :=
  by
  intros x y h
  cases x
  . cases y
    . rfl
    . cases h
    . cases h
  . cases y
    . cases h
    . rfl
    . cases h
  . cases y
    . cases h
    . cases h
    . rfl
  done
