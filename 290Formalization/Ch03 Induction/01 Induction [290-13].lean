import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/- Section 13 introduces mathematical induction. In Lean, induction on a natural
number is usually written with

  induction n with
  | zero => ...
  | succ n ih => ...

The base case is `n = 0`, and the inductive step may use the inductive
hypothesis `ih : P n` to prove `P (n + 1)`. For now we only use induction on
natural numbers, not structural induction on more complicated types.

The textbook usually writes sums from `1` to `n`. In Lean it is often convenient
to use `Finset.range (n + 1)`, whose elements are `0, 1, ..., n`. Since the
extra `0` term is harmless in many formulas, this matches the textbook well. -/

theorem induction_template (P : ℕ → Prop) (h0 : P 0)
    (hstep : ∀ k : ℕ, P k → P (k + 1)) : ∀ n : ℕ, P n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      exact hstep n ih

/- The next theorem is Proposition 13.5 from the text. To avoid division in the
inductive step, we first prove an equivalent formula with both sides multiplied
by `2`. -/

theorem two_mul_sum_id (n : ℕ) :
    2 * Finset.sum (Finset.range (n + 1)) (fun i => i) = n * (n + 1) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        2 * (Finset.sum (Finset.range (n + 1)) (fun i => i) + (n + 1))
            = 2 * Finset.sum (Finset.range (n + 1)) (fun i => i) + 2 * (n + 1) := by
                ring
        _ = n * (n + 1) + 2 * (n + 1) := by
              rw [ih]
        _ = (n + 1) * (n + 2) := by
              ring

theorem sum_id (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun i => i) = n * (n + 1) / 2 := by
  simpa [Nat.mul_comm] using Finset.sum_range_id (n + 1)

/- This proof mirrors Proposition 13.10 in the text. The key move in the
inductive step is to compare `n + 1` with `2 ^ n`, then multiply by `2`. -/

theorem two_pow_gt_self (n : ℕ) : 2 ^ n > n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have h1 : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt ih
      calc
        2 ^ (n + 1) = 2 ^ n * 2 := by
          rw [pow_succ]
        _ ≥ (n + 1) * 2 := by
          exact Nat.mul_le_mul_right 2 h1
        _ > n + 1 := by
          rw [show (n + 1) * 2 = (n + 1) + (n + 1) by ring]
          exact Nat.lt_add_of_pos_right (Nat.succ_pos n)

/- Exercises -/

-- Exercise 13.1
example (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => 2 * i + 1) = n ^ 2 := by
  sorry

-- Exercise 13.2
example (n : ℕ) :
    Finset.sum (Finset.range n)
      (fun i => (1 : ℚ) / ((2 * i + 1 : ℚ) * (2 * i + 3))) = (n : ℚ) / (2 * n + 1) := by
  sorry

-- Exercise 13.3
example (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun i => i ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

-- Exercise 13.4a
example (n : ℕ) : n < 3 ^ n := by
  sorry

-- Exercise 13.4b
example (n : ℤ) : (n : ℝ) < (3 : ℝ) ^ n := by
  sorry

-- Exercise 13.5
example (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun i => x ^ i) = (1 - x ^ (n + 1)) / (1 - x) := by
  sorry

-- Exercise 13.6
example (x : ℝ) (hx : x > -1) (n : ℕ) : (1 + x) ^ n ≥ 1 + n * x := by
  sorry

-- Exercise 13.7
example {S : Set ℕ} (hS : S.Nonempty) : ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  sorry

-- Exercise 13.8
example {m n : ℕ} (h : m < n) (f : Fin m → Fin n) :
    ∃ y : Fin n, ∀ x : Fin m, f x ≠ y := by
  sorry
