import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-- A real number is rational if it is not irrational. -/
def IsRational (x : ℝ) : Prop := ¬ Irrational x

/- To prove an existential statement in Lean, we usually give a witness with `use`.
If there are several witnesses or several properties to check, `constructor` splits
the goal into smaller pieces. -/

example : ∃ x : ℝ, x > 1 := by
  use 3
  norm_num

example : ∃ n : ℕ, n ^ 3 < 2 := by
  use 1
  norm_num

example : ∃ x : ℝ, x ^ 2 < x := by
  use (1 / 2 : ℝ)
  norm_num

theorem exists_cube_eq_sq : ∃ n : ℤ, n ^ 3 = n ^ 2 := by
  use 0
  norm_num

theorem exists_sq_dvd_cube_not_dvd : ∃ a b : ℕ, a ^ 2 ∣ b ^ 3 ∧ ¬ a ∣ b := by
  refine ⟨8, 4, ?_⟩
  constructor
  · norm_num
  · norm_num

theorem odd_is_sum_of_consecutive {a : ℤ} (ha : Odd a) :
    ∃ b : ℤ, a = b + (b + 1) := by
  obtain ⟨k, hk⟩ := ha
  use k
  linarith

/- Some existence proofs are nonconstructive: we prove an object exists without
explicitly knowing which one it is. The next theorem mirrors the standard
two-case proof from the text. -/

open Classical in
theorem exists_irrational_rpow_rational :
    ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ IsRational (a ^ b) := by
  by_cases h : IsRational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · refine ⟨Real.sqrt 2, Real.sqrt 2, ?_, ?_, h⟩
    · simpa using irrational_sqrt_two
    · simpa using irrational_sqrt_two
  · refine ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, ?_, ?_, ?_⟩
    · unfold IsRational at h
      exact Classical.not_not.mp h
    · simpa using irrational_sqrt_two
    · unfold IsRational
      have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := by
        positivity
      have htwo_nonneg : (0 : ℝ) ≤ 2 := by
        positivity
      have hpow : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) := by
        calc
          ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2)
              = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
                  symm
                  exact Real.rpow_mul hsqrt_nonneg (Real.sqrt 2) (Real.sqrt 2)
          _ = (Real.sqrt 2) ^ (2 : ℝ) := by
                congr 1
                nlinarith [Real.sq_sqrt htwo_nonneg]
          _ = (Real.sqrt 2) ^ 2 := by
                simp
          _ = 2 := by
                exact Real.sq_sqrt htwo_nonneg
      rw [hpow]
      simp

/- Finding a counterexample amounts to proving an existential statement. When a
false statement is universal, one witness is enough to disprove it. -/

theorem not_forall_gt_half_sq : ¬ ∀ x : ℝ, x > x ^ 2 / 2 := by
  intro h
  have h0 := h 0
  norm_num at h0

theorem no_real_sq_lt_neg_one : ¬ ∃ x : ℝ, x ^ 2 < -1 := by
  rintro ⟨x, hx⟩
  have hx0 : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

theorem exists_dvd_dvd_ne : ∃ a b : ℤ, a ∣ b ∧ b ∣ a ∧ a ≠ b := by
  refine ⟨2, -2, ?_⟩
  constructor
  · use -1
    ring
  constructor
  · use -1
    ring
  · norm_num

/- Exercises -/

-- Exercise 11.1a
example : ∃ a b : ℝ, IsRational a ∧ IsRational b ∧ IsRational (a ^ b) := by
  sorry

-- Exercise 11.1b
example : ∃ a b : ℝ, IsRational a ∧ IsRational b ∧ Irrational (a ^ b) := by
  sorry

-- Exercise 11.1c
example : ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ Irrational (a ^ b) := by
  sorry

-- Exercise 11.1d
example : ∃ a b : ℝ, IsRational a ∧ Irrational b ∧ IsRational (a ^ b) := by
  sorry

-- Exercise 11.1e
example : ∃ a b : ℝ, IsRational a ∧ Irrational b ∧ Irrational (a ^ b) := by
  sorry

-- Exercise 11.1f
example : ∃ a b : ℝ, Irrational a ∧ IsRational b ∧ IsRational (a ^ b) := by
  sorry

-- Exercise 11.1g
example : ∃ a b : ℝ, Irrational a ∧ IsRational b ∧ Irrational (a ^ b) := by
  sorry

-- Exercise 11.2 (disprove the original statement by finding a counterexample)
example : ∃ x y : ℝ, IsRational x ∧ Irrational y ∧ IsRational (x * y) := by
  sorry

-- Exercise 11.3 (disprove the original statement by finding a counterexample)
example : ∃ s : ℤ, Odd (6 * s - 3) ∧ ¬ Odd s := by
  sorry

-- Exercise 11.4 (disprove the original statement)
example : ¬ ∃ x : ℤ, Odd (x ^ 2 + x) := by
  sorry

-- Exercise 11.5
example {a : ℚ} (ha : 0 < a) : ∃ x : ℝ, Irrational x ∧ 0 < x ∧ x < a := by
  sorry

-- Exercise 11.6
example {x y : ℝ} (h : x < y) : ∃ q : ℚ, x < q ∧ (q : ℝ) < y := by
  sorry
