import Mathlib.Tactic

open Function

variable (X Y Z : Type)

-- Definition of Injective f and Surjective f

theorem injective_def (f : X → Y) :
  Injective f ↔ ∀ a b : X, f a = f b → a = b :=
  by
  rfl

theorem surjective_def (f : X → Y) :
  Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b :=
  by
  rfl

-- Definition of function id

theorem id_eval (x : X) :
  id x = x :=
  by
  rfl

-- Definition of function composirion g ∘ f

theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) :
  (g ∘ f) x = g (f x) :=
  by
  rfl


-- proove theorems

example : Injective (id : X → X) :=
  by
  rw [injective_def]
  intro x₁ x₂ h
  rw [id_eval, id_eval] at h
  apply h
  done

example : Surjective (id : X → X) :=
  by
  rw [surjective_def]
  intro x
  use x
  rw [id_eval]

example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) :
  Injective (g ∘ f) :=
  by
  rw [injective_def] at *
  intro x₁ x₂ hgf
  apply hf
  apply hg
  rw [comp_eval, comp_eval] at hgf
  apply hgf
  done

example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) :
  Surjective (g ∘ f) :=
  by
  rw [surjective_def] at *
  intro z
  obtain ⟨y, hgy⟩ := hg z
  obtain ⟨x, hfx⟩ := hf y
  use x
  rw [comp_eval]
  rw [hfx, hgy]
  done

example (f : X → Y) (g : Y → Z) :
  Injective (g ∘ f) → Injective f :=
  by
  intro hgf
  rw [injective_def] at *
  intro x₁ x₂
  intro hf
  apply hgf
  rw [comp_eval, comp_eval]
  rw [hf]
  done

  example (f : X → Y) (g : Y → Z) :
    Surjective (g ∘ f) → Surjective g :=
    by
    intro hgf
    rw [surjective_def] at *
    intro z
    obtain ⟨x, hgfx⟩ := hgf z
    rw [comp_eval] at hgfx
    use f x
    done
