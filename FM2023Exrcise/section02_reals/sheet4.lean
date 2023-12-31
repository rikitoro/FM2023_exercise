import Mathlib.Tactic

example (x : ℝ) : |-x| = |x| :=
  by
  exact abs_neg x

example (x y : ℝ) : |x - y| = |y - x| :=
  by
  exact abs_sub_comm x y
  done

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
  by
  exact Nat.max_le

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y :=
  by
  exact abs_lt

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 :=
  by
  exact half_pos hε

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y :=
  by
  exact add_lt_add h1 h2

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 :=
  by
  have h : (0 : ℝ) < 3 := by
    norm_num
  exact div_pos hε h


example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) :
  a + b + c + d < x + y :=
  by
  have h : a + b + c + d = (a + c) + (b + d) := by
    linarith
  rw [h]
  exact add_lt_add h1 h2
