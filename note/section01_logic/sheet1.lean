import Mathlib.Tactic

variable (P Q R : Prop)

example : P → P :=
  by
  intro hP
  apply hP

example : P → Q → P :=
  by
  intro hP _
  apply hP

example : P → (P → Q) → Q :=
  by
  intro hP hPQ
  apply hPQ hP

example : (P → Q) → (Q → R) → (P → R) :=
  by
  intro hPQ hQR hP
  apply hQR ∘ hPQ $ hP

example : (P → Q → R) → (P → Q) → (P → R) :=
  by
  intro hPQR hPQ hP
  apply hPQR
  . apply hP
  . apply hPQ hP


variable (S T: Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
  by
  intro _ hSQ hRT hQR hS
  apply hRT
  apply hQR
  apply hSQ hS

example : (P → Q) → ((P → Q) → P) → Q :=
  by
  intro hPQ hPQP
  apply hPQ
  apply hPQP
  apply hPQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
  by
  intro hQPP hQR hRP
  apply hQPP
  intro hQ
  apply hRP
  apply hQR hQ

example : (((P → Q) → Q) → Q) → (P → Q) :=
  by
  intro hPQQQ hP
  apply hPQQQ
  intro hPQ
  apply hPQ hP

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
  by
  sorry
