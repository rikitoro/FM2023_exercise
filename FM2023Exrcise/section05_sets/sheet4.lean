import Mathlib.Tactic

lemma mem_def (X : Type) (P : X → Prop) (a : X) :
  a ∈ {x : X | P x} ↔ P a :=
  by
  rfl

-- open Set

def is_even (n : ℕ) : Prop :=
  ∃ t, n = 2 * t

example : 74 ∈ {n : ℕ | is_even n} :=
  by
  rw [mem_def]
  use 37

def real.is_even (r : ℝ) :=
  ∃ t : ℝ, r = 2 * t

example : ∀ x, x ∈ {r : ℝ | real.is_even r} :=
  by
  intro x
  rw [mem_def]
  rw [real.is_even]
  use x / 2
  ring
  done

example : ∀ x, x ∉ {r : ℝ | 0 < r ∧ r < 0} :=
  by
  intro x
  rw [mem_def]
  intro h
  linarith
  done
