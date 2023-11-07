import Mathlib.Tactic

variable (P Q R : Prop)

example : P ∧ Q → P :=
  by
  intro h
  rcases h with ⟨hp, _⟩
  apply hp

example : P ∧ Q → Q :=
  by
  intro h
  apply h.right

example : (P → Q → R) → (P ∧ Q → R) :=
  by
  intro h hpq
  rcases hpq with ⟨hp, hq⟩
  apply h
  . assumption
  . assumption

example : P → Q → P ∧ Q :=
  by
  intro hp hq
  constructor
  . exact hp
  . exact hq

example : P ∧ Q → Q ∧ P :=
  by
  intro h
  apply And.intro
  . apply h.right
  . apply h.left
  done

example : P → P ∧ True :=
  by
  intro hp
  constructor
  . exact hp
  . triv

example : False → P ∧ False :=
  by
  intro hf
  constructor
  . apply False.elim hf
  . apply hf

example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
  by
  intro hpq hqr
  constructor
  . apply hpq.left
  . apply hqr.right

example : ((P ∧ Q) → R) → (P → Q → R) :=
  by
  intro h hp hq
  apply h
  constructor
  . exact hp
  . exact hq
