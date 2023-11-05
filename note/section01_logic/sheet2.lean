import Mathlib.Tactic

variable (P Q R : Prop)

example : True :=
  by
  triv

example : True → True :=
  by
  intro
  triv

example : False → True :=
  by
  intro
  triv

example : False → False :=
  by
  intro h
  apply h

example : (True → False) → False :=
  by
  intro h
  apply h
  triv

example : False → P :=
  by
  intro h
  exfalso
  apply h

example : True → False → True → False → True → False :=
  by
  intro _ h2 _ _ _
  apply h2

example : P → ((P → False) → False) :=
  by
  intro hP hnP
  apply hnP hP

example : (P → False) → P → Q :=
  by
  intro hnP hP
  exfalso
  apply hnP hP

example : (True → False) → P :=
  by
  intro h
  exfalso
  apply h
  triv
