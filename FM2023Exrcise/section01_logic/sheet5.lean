import Mathlib.Tactic

variable (P Q R S : Prop)

example : P ↔ P :=
  by
  rfl

example : (P ↔ Q) → (Q ↔ P) :=
  by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) :=
  by
  constructor
  . intro h
    rw [h]
  . intro h
    rw [h]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  by
  intro hpq hqr
  rw [hpq, hqr]

example : P ∧ Q ↔ Q ∧ P :=
  by
  rw [and_comm]

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
  by
  rw [and_assoc]

example : P ↔ (P ∧ True) :=
  by
  rw [and_true_iff]

example : False ↔ (P ∧ False) :=
  by
  rw [and_false_iff]

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
  by
  intro hpq hrs
  rw [hpq, hrs]

example : ¬ (P ↔ ¬ P) :=
  by
  intro h
  rcases h with ⟨h', h''⟩
  by_cases h : P
  . have hnp := h' h
    apply hnp h
  . have hp := h'' h
    apply h hp
  done
