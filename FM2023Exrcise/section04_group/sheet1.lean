import Mathlib.Tactic

variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
  by
  exact mul_left_inv g

example (a b c : G) : (a * b) * c = a * (b * c) :=
  by
  apply mul_assoc

example (a : G) : a * a⁻¹ = 1 :=
  by
  exact mul_inv_self a


variable (a b c : G)

example : a * (a⁻¹ * b) = b :=
  by
  --exact mul_inv_cancel_left a b
  rw [← mul_assoc, mul_inv_self, one_mul]
  done

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c :=
  by
  have h : b * (a * c) = (b * a) * c :=
    by
    rw [mul_assoc]
  rw [h1, h2] at h
  rw [mul_one, one_mul] at h
  exact h
  done

example : a * b = 1 ↔ a⁻¹ = b :=
  by
  exact mul_eq_one_iff_inv_eq

example : (1 : G)⁻¹ = 1 :=
  by
  exact inv_one

example : (a⁻¹)⁻¹ = a :=
  by
  exact inv_inv a

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  by
  exact mul_inv_rev a b


example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 :=
  by
  group

example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g :=
  by
  intro g₁ g₂
  have hg1 := h g₁
  have hg2 := h g₂
  rw [mul_eq_one_iff_eq_inv] at hg1
  rw [mul_eq_one_iff_eq_inv] at hg2
  have hg1g2 := h (g₁ * g₂)
  rw [mul_eq_one_iff_eq_inv] at hg1g2
  rw [hg1g2, mul_inv_rev, ← hg1, ← hg2]
  done
