import Mathlib.Tactic
import FM2023Exrcise.section02_reals.sheet5

theorem tends_to_thirtyseven_mul
  (a : ℕ → ℝ) (t : ℝ) (h : tends_to a t) :
  tends_to (λ n => 37 * a n) (37 * t) :=
  by
  rw [tends_to_def]
  intro ε hεpos
  have hεpos' : 0 < ε / 37 :=
    by
    apply div_pos hεpos (by norm_num)
  have h' := h (ε / 37) hεpos'
  obtain ⟨N, hN⟩ := h'
  use N
  intro n hn
  have h'' := hN n hn
  rw [← mul_sub, abs_mul, abs_of_nonneg]
  linarith
  norm_num
  done
