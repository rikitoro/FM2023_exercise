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

example : A ∩ A = A :=
  by
  ext w
  rw [mem_inter_iff]
  exact and_self_iff

example : A ∩ ∅ = ∅ :=
  by
  ext w
  rw [mem_inter_iff]
  apply Iff.intro
  . intro h
    rcases h with ⟨_, h2⟩
    apply h2
  . intro h
    apply False.elim
    apply not_mem_empty x $ h

example : A ∪ univ = univ :=
  by
  ext w
  rw [mem_union]
  constructor
  . intro _
    triv
  . intro _
    right
    triv

example : A ⊆ B → B ⊆ A → A = B :=
  by
  intro hAB hBA
  ext w
  sorry
  done
