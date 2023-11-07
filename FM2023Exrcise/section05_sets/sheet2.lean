import Mathlib.Tactic

variable
  (X : Type)
  (A B C D E : Set X)
  (x y z : X)

open Set

example : x ∈ (univ : Set X) :=
  by
  triv

example : x ∈ (∅ : Set X) → False :=
  by
  intro h
  cases h


example : A ⊆ univ :=
  by
  rw [subset_def]
  intro w _
  triv

example : ∅ ⊆ A :=
  by
  rw [subset_def]
  intro w h
  cases h
