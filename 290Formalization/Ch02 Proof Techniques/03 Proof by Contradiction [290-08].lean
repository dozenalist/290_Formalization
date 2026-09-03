import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/- Proof by cases in Lean is often handled with `by_cases` when the cases are
described by a proposition, or with `cases` after first producing an explicit
disjunction. -/

example (P Q : Prop) (hP : P → Q) (hNotP : ¬ P → Q) : Q := by
  by_cases hp : P
  · exact hP hp
  · exact hNotP hp

/-- We'll reuse the parity facts `even ↔ ¬ odd` and `odd ↔ ¬ even`. -/
theorem even_iff_not_odd (n : ℤ) : Even n ↔ ¬Odd n := Int.not_odd_iff_even.symm
theorem odd_iff_not_even (n : ℤ) : Odd n ↔ ¬Even n := Int.not_even_iff_odd.symm

def same_parity (x y : ℤ) : Prop := (Even x ∧ Even y) ∨ (Odd x ∧ Odd y)

namespace Int.ModEq

theorem dvd' {n a b : ℤ} (h : a ≡ b [ZMOD n]) : n ∣ a - b :=
  h.symm.dvd

end Int.ModEq

/- Introductory examples with parity. The tactic `mod_cases` splits an integer
into its possible congruence classes modulo a positive numeral. -/

theorem even_sq_add_self (x : ℤ) : Even (x ^ 2 + x) := by
  mod_cases hx : x % 2
  · obtain ⟨k, hk⟩ := hx.dvd'
    have hx' : x = 2 * k := by linarith
    rw [hx']
    use 2 * k ^ 2 + k
    ring
  · obtain ⟨k, hk⟩ := hx.dvd'
    have hx' : x = 2 * k + 1 := by linarith
    rw [hx']
    use 2 * k ^ 2 + 3 * k + 1
    ring

theorem same_parity_of_even_add {x y : ℤ}
  (h : Even (x + y)) : same_parity x y := by
  mod_cases hx : x % 2
  · mod_cases hy : y % 2
    · obtain ⟨kx, hkx⟩ := hx.dvd'
      obtain ⟨ky, hky⟩ := hy.dvd'
      left
      constructor
      · use kx
        linarith
      · use ky
        linarith
    · exfalso
      obtain ⟨kx, hkx⟩ := hx.dvd'
      obtain ⟨ky, hky⟩ := hy.dvd'
      have hx_even : Even x := by
        use kx
        linarith
      have hy_odd : Odd y := by
        use ky
        linarith
      have hxy : Odd (x + y) := hx_even.add_odd hy_odd
      rw [odd_iff_not_even] at hxy
      exact hxy h
  · mod_cases hy : y % 2
    · exfalso
      obtain ⟨kx, hkx⟩ := hx.dvd'
      obtain ⟨ky, hky⟩ := hy.dvd'
      have hx_odd : Odd x := by
        use kx
        linarith
      have hy_even : Even y := by
        use ky
        linarith
      have hxy : Odd (x + y) := hx_odd.add_even hy_even
      rw [odd_iff_not_even] at hxy
      exact hxy h
    · obtain ⟨kx, hkx⟩ := hx.dvd'
      obtain ⟨ky, hky⟩ := hy.dvd'
      right
      constructor
      · use kx
        linarith
      · use ky
        linarith

/- Congruence modulo `n`. Lean writes this as `a ≡ b [ZMOD n]`. -/

example : 7 ≡ 3 [ZMOD 2] := by
  rw [Int.modEq_iff_dvd]
  norm_num

theorem modEq_mul_right {a b c n : ℤ} (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  obtain ⟨k, hk⟩ := h
  use k * c
  calc
    b * c - a * c = (b - a) * c := by ring
    _ = (n * k) * c := by rw [hk]
    _ = n * (k * c) := by ring

theorem cube_mod_three (x : ℤ) : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  · obtain ⟨k, hk⟩ := hx.dvd'
    have hx' : x = 3 * k := by linarith
    rw [hx']
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
    use 9 * k ^ 3 - k
    ring
  · obtain ⟨k, hk⟩ := hx.dvd'
    have hx' : x = 3 * k + 1 := by linarith
    rw [hx']
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
    use 9 * k ^ 3 + 9 * k ^ 2 + 2 * k
    ring
  · obtain ⟨k, hk⟩ := hx.dvd'
    have hx' : x = 3 * k + 2 := by linarith
    rw [hx']
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
    use 9 * k ^ 3 + 18 * k ^ 2 + 11 * k + 2
    ring

/- Absolute values are another natural place for proof by cases. -/

example : |(2 : ℝ)| = 2 := by norm_num
example : |(-2 : ℝ)| = 2 := by norm_num

example {x : ℝ} (hx : x < 0) : |x| = -x := by
  rw [abs_of_neg hx]

theorem abs_sub_le_bounds {a b x : ℝ} (hb : 0 ≤ b) (h : |x - a| ≤ b) :
    a - b ≤ x ∧ x ≤ a + b := by
  by_cases hxa : 0 ≤ x - a
  · rw [abs_of_nonneg hxa] at h
    constructor <;> linarith
  · have hneg : x - a < 0 := lt_of_not_ge hxa
    rw [abs_of_neg hneg] at h
    constructor <;> linarith

theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hx hy)]
    · have hy' : y < 0 := lt_of_not_ge hy
      by_cases hxy : 0 ≤ x + y
      · rw [abs_of_nonneg hx, abs_of_neg hy', abs_of_nonneg hxy]
        linarith
      · have hxy' : x + y < 0 := lt_of_not_ge hxy
        rw [abs_of_nonneg hx, abs_of_neg hy', abs_of_neg hxy']
        linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · by_cases hxy : 0 ≤ x + y
      · rw [abs_of_neg hx', abs_of_nonneg hy, abs_of_nonneg hxy]
        linarith
      · have hxy' : x + y < 0 := lt_of_not_ge hxy
        rw [abs_of_neg hx', abs_of_nonneg hy, abs_of_neg hxy']
        linarith
    · have hy' : y < 0 := lt_of_not_ge hy
      have hxy : x + y < 0 := by linarith
      rw [abs_of_neg hx', abs_of_neg hy', abs_of_neg hxy]
      linarith

/- Exercises -/

-- Exercise 8.1
example {x y : ℤ} (h : same_parity x y) : Even (x ^ 2 + x * y) := by
  sorry

-- Exercise 8.2
example {a b c : ℤ} (h : ¬ a ∣ b * c) : ¬ a ∣ b ∧ ¬ a ∣ c := by
  sorry

-- Exercise 8.3a
example (x : ℤ) : x ^ 2 ≡ 0 [ZMOD 4] ∨ x ^ 2 ≡ 1 [ZMOD 4] := by
  sorry

-- Exercise 8.3b
example (x : ℤ) : 4 ∣ (x ^ 4 - x ^ 2) := by
  sorry

-- Exercise 8.4
example {a b c n : ℤ} (hab : a ≡ b [ZMOD n]) (hbc : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  sorry

-- Exercise 8.5
example (n : ℤ) : 3 ∣ n ↔ 3 ∣ n ^ 2 := by
  sorry

-- Exercise 8.6
example (n : ℤ) : 3 ∣ (2 * n ^ 2 + 1) ↔ ¬ 3 ∣ n := by
  sorry

-- Exercise 8.7
example {a b c d n : ℤ} (hab : a ≡ b [ZMOD n]) (hcd : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  sorry

-- Exercise 8.8 (Theorem 8.22 in the text)
example {x y : ℝ} : |x * y| = |x| * |y| := by
  sorry

-- Exercise 8.9
example {a : ℝ} : a ^ 2 ≤ 1 ↔ (-1 ≤ a ∧ a ≤ 1) := by
  sorry
