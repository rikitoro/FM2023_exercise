import Mathlib.Tactic

variable (X : Type) [PartialOrder X]

example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) :
  a ≤ c :=
  by
  apply le_trans hab hbc

variable (a b c d : X)

example : a ≤ a :=
  by
  rfl

example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
  a ≤ d :=
  by
  apply le_trans hab
  apply le_trans hbc hcd

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) :
  a = b := by
  have hba : b ≤ a :=
    by
    apply le_trans hbc hca
  apply le_antisymm hab hba
