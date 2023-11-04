import Mathlib.Tactic

def f : ℕ → ℝ := λ n => (n : ℝ) ^ 2 + 3

-- limit of a(n) as n → ∞ is t
def tends_to (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tends_to_def {a : ℕ → ℝ} {t : ℝ} :
  tends_to a t ↔
  ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
  by
  rfl

-------------------

theorem tends_to_thirtyseven : tends_to (λ _ => 37) 37 :=
  by
  rw [tends_to_def]
  intro ε hε
  use 0
  intro n _
  norm_num
  apply hε

theorem tends_to_const (c : ℝ) : tends_to (λ _ => c) c :=
  by
  rw [tends_to_def]
  intro ε hε
  use 0
  intro n _
  norm_num
  apply hε

theorem tends_to_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ)
  (h : tends_to a t) :
  tends_to (λ n => a n + c) (t + c) :=
  by
  rw [tends_to_def] at *
  intro ε hε
  have hε' := h ε $ hε
  obtain ⟨B', hε''⟩ := hε'
  use B'
  intro n hn
  have h' := hε'' n hn
  norm_num
  apply h'
  done

example {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n => - a n) (-t) :=
  by
  sorry
