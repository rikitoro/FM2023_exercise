import Mathlib.Tactic

open Set

variable
  (X : Type)
  (A B C D E : Set X)
  (x y z : X)

example : x ∉ A → (x ∈ A → False) :=
  by
  intro h1 h2
  apply h1 h2

example : x ∈ A → (x ∉ A → False) :=
  by
  intro h1 h2
  apply h2 h1

example : (A ⊆ B) → x ∉ B → x ∉ A :=
  by
  intro h1 h2 h3
  rw [subset_def] at h1
  apply h1 at h3
  apply h2 h3

example : x ∉ (∅ : Set X) :=
  by
  intro h
  apply h

example : x ∈ Aᶜ → x ∉ A :=
  by
  intro h
  apply h

example : (∀ x, x ∈ A) ↔ ¬ (∃ x, x ∈ Aᶜ) :=
  by
  constructor
  . intro h
    intro h1
    obtain ⟨w, h1'⟩ := h1
    apply h1'
    apply h
  . intro h
    intro w
    by_contra h1
    apply h
    use w
    apply h1
  done
