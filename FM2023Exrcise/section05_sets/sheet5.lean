import Mathlib.Tactic

open Set

variable
  (X : Type)
  (A B C D E : Set X)
  (x y z : X)

example : A ∪ A = A :=
  by
  ext w
  rw [mem_union]
  exact or_self_iff
