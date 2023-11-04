import Mathlib.Tactic

variable
  (X : Type)
  (A B C D : Set X)
  (x y z : X)

-- Definitions of ⊆, ∪, ∩

lemma subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B :=
  by
  rfl

lemma mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  by
  rfl

lemma mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  by
  rfl

---------------------

example : A ⊆ A :=
  by
  rw [subset_def]
  intro a
  intro h
  apply h
  done


example : A ⊆ B → B ⊆ C → A ⊆ C :=
  by
  intro hAB hBC
  intro a hainA
  apply hBC
  apply hAB
  apply hainA
  done


example : A ⊆ A ∪ B :=
  by
  intro a hainA
  rw [mem_union_iff]
  left
  apply hainA
  done


example : A ∩ B ⊆ A :=
  by
  intro w hAB
  rw [mem_inter_iff] at hAB
  apply hAB.left
  done


example : A ⊆ B → A ⊆ C → A ⊆ (B ∩ C) :=
  by
  intro hAB hAC
  intro w hwinA
  constructor
  . apply hAB hwinA
  . apply hAC hwinA
  done


example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
  by
  intro hBA hCA
  intro w hBC
  rw [mem_union_iff] at hBC
  rcases hBC with hB | hC
  . apply hBA hB
  . apply hCA hC
  done


example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
  by
  intro hAB hCD
  intro w hwAC
  rw [mem_union_iff] at *
  rcases hwAC with hwA | hwC
  . left
    apply hAB hwA
  . right
    apply hCD hwC
  done


example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D :=
  by
  intro hAB hCD
  intro w hwAC
  rw [mem_inter_iff] at *
  constructor
  . apply hAB hwAC.left
  . apply hCD hwAC.right
  done
