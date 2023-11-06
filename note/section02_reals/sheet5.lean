import Mathlib.Tactic

-- import note.section02_reals.sheet4
-- limit of a(n) as n → ∞ is t
def tends_to (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tends_to_def {a : ℕ → ℝ} {t : ℝ} :
  tends_to a t ↔
  ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
  by
  rfl

theorem tends_to_neg {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n => - a n) (-t) :=
  by
  rw [tends_to_def] at *
  intro ε hεpos
  obtain ⟨N, h⟩ := ha ε hεpos
  use N
  intro n hn
  simp
  have h' := h n hn
  rw [← abs_neg] at h'
  simp at h'
  rw [add_comm]
  apply h'
  done


theorem tends_to_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n => a n + b n) (t + u) :=
  by
  rw [tends_to_def]
  intro ε hεpos
  rw [tends_to] at ha
  have haε : 0 < ε / 2 :=
    by
    linarith
  apply ha at haε
  obtain ⟨Na, ha'⟩ := haε

  have hbε : 0 < ε / 2 :=
    by
    linarith
  apply hb at hbε
  obtain ⟨Nb, hb'⟩ := hbε

  let Nab := max Na Nb
  use Nab
  intro n
  intro hn
  have ha'' := ha' n
  have hb'' := hb' n
  have hNan : Na ≤ n :=
    by
    exact le_of_max_le_left hn
  have hNbn : Nb ≤ n :=
    by
    exact le_of_max_le_right hn
  apply ha'' at hNan
  apply hb'' at hNbn
  have h''' : a n + b n - (t + u) = a n - t + (b n - u) :=
    by linarith
  calc
    |a n + b n - (t + u)|
      = |(a n - t) + (b n - u)| :=
      by
      rw [h''']
    _ ≤ |a n - t| + |b n - u|   :=
      by
      exact abs_add (a n - t) (b n - u)
    _ < ε / 2 + ε / 2           :=
      by
      exact add_lt_add hNan hNbn
    _ = ε                       :=
      by
      simp
  done
