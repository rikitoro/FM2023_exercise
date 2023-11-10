import Mathlib.Tactic

inductive X : Type
| a : X

inductive Y : Type
| b : Y
| c : Y

inductive Z : Type
| d : Z

def f : X → Y
| X.a => Y.b

def g : Y → Z
| Y.b => Z.d
| Y.c => Z.d

example (z : Z) : z = Z.d :=
  by
  cases z
  . rfl

lemma Yb_ne_Yc : Y.b ≠ Y.c :=
  by
  intro h
  cases h

lemma gYb_eq_gYc : g Y.b = g Y.c :=
  by
  rw [g]

open Function

lemma gf_injective : Injective (g ∘ f) :=
  by
  rw [Injective]
  intro x₁ x₂ hgf
  cases x₁
  . rfl


example : ¬ (∀ A B C : Type, ∀ (ϕ : A → B) (ψ : B → C), Injective (ψ ∘ ϕ) → Injective ψ) :=
  by
  intro h
  have hginj := h X Y Z f g gf_injective
  have hY :=  hginj gYb_eq_gYc
  cases hY

lemma gf_surjective : Surjective (g ∘ f) :=
  by
  intro z
  use X.a

example : ¬ (∀ A B C : Type, ∀ (ϕ : A → B) (ψ : B → C), Surjective (ψ ∘ ϕ) → Surjective ϕ) :=
  by
  intro h
  have hg_surj := h X Y Z f g gf_surjective
  rw [Surjective] at hg_surj
  specialize hg_surj Y.c
  obtain ⟨x, hf⟩ := hg_surj
  cases hf
  done
