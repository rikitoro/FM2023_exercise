import Mathlib.Tactic

variable (P Q R : Prop)

example : ¬ True → False :=
  by
  intro h
  apply h
  triv

example : False → ¬ True :=
  by
  intro h _
  apply h

example : ¬ False → True :=
  by
  intro _
  triv

example : True → ¬ False :=
  by
  intro _
  by_contra h
  apply h

example : False → ¬ P :=
  by
  intro h
  by_contra
  apply h

example : P → ¬ P → False :=
  by
  intro hp hnp
  apply hnp hp

example : P → ¬ (¬ P) :=
  by
  intro hp hnp
  apply hnp hp

example : (P → Q) → (¬ Q → ¬ P) :=
  by
  intro h hnq hp
  apply hnq $ h hp

example : ¬ ¬ False → False :=
  by
  intro h
  by_contra h'
  apply h h'

example : ¬ ¬ P → P :=
  by
  intro hnnp
  by_contra hnp
  apply hnnp hnp


example : (¬ Q → ¬ P) → (P → Q) :=
  by
  intro h hp
  by_contra h'
  apply h h' hp
