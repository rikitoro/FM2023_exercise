import Mathlib.Tactic

variable (P Q R S : Prop)

example : P → P ∨ Q :=
  by
  intro h
  left
  exact h

example : Q → P ∨ Q :=
  by
  intro h
  right
  exact h

example : P ∨ Q → (P → R) → (Q → R) → R :=
  by
  intro hpq hpr hqr
  rcases hpq with hp | hq
  . apply hpr hp
  . apply hqr hq
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  by
  intro hpr hqs hpq
  rcases hpq with hp | hq
  . left
    apply hpr hp
  . right
    apply hqs hq
  done

example : (P → Q) → P ∨ R → Q ∨ R :=
  by
  intro hpq hpr
  rcases hpr with hp | hr
  . left
    exact hpq hp
  . right
    exact hr
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  by
  intro hpr hqs
  rw [hpr, hqs]

example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
  by
  apply Iff.intro
  . intro hnpq
    apply And.intro
    . by_contra hp
      apply hnpq
      left
      apply hp
    . by_contra hq
      apply hnpq
      right
      apply hq
  . intro hnpnq hpq
    rcases hnpnq with ⟨hnp, hnq⟩
    rcases hpq with hp | hq
    . apply hnp hp
    . apply hnq hq
  done

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
  by
  constructor
  . intro hnpq
    by_contra h
    apply hnpq
    constructor
    . by_contra hnp
      apply h
      left
      apply hnp
    . by_contra hnq
      apply h
      right
      apply hnq
  . intro hnpnq
    intro hpq
    rcases hnpnq with hnp | hnq
    . apply hnp hpq.left
    . apply hnq hpq.right
  done
