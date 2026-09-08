import Mathlib.Data.Int.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option linter.style.emptyLine false
set_option linter.style.whitespace false


/- Proof by contradiction in Lean often uses either `by_contra`, which assumes
the negation of the goal, or `exfalso`, which changes the goal to `False`. -/

theorem even_iff_not_odd (n : ℤ) : Even n ↔ ¬Odd n := Int.not_odd_iff_even.symm
theorem odd_iff_not_even (n : ℤ) : Odd n ↔ ¬Even n := Int.not_even_iff_odd.symm

open Classical in
theorem contradiction_template (R S : Prop) (h : ¬ R → S) (hNotS : ¬ S) : R := by
  by_contra hNotR
  exact hNotS (h hNotR)

/- A standard contradiction proof: there is no smallest positive rational number. -/

theorem no_smallest_positive_rational :
    ¬ ∃ q : ℚ, 0 < q ∧ ∀ r : ℚ, 0 < r → q ≤ r := by
  rintro ⟨q, hqpos, hmin⟩
  have hhalfpos : 0 < q / 2 := by
    positivity
  have hle : q ≤ q / 2 := hmin (q / 2) hhalfpos
  linarith

theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  rw [Irrational]
  rintro ⟨q, hq⟩
  have hsq : ((q.num : ℝ) / q.den) ^ 2 = 2 := by
    calc
      ((q.num : ℝ) / q.den) ^ 2 = (q : ℝ) ^ 2 := by
        simp [Rat.cast_def]
      _ = (Real.sqrt 2) ^ 2 := by
        rw [hq]
      _ = 2 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcross : (q.num : ℝ) ^ 2 = (q.den : ℝ) ^ 2 * 2 := by
    field_simp [Rat.den_nz] at hsq
    exact hsq
  have hnumden : q.num ^ 2 = (q.den : ℤ) ^ 2 * 2 := by
    exact_mod_cast hcross
  have hnumSqEven : Even (q.num ^ 2) := by
    use (q.den : ℤ) ^ 2
    linarith
  have hnumEven : Even q.num := by
    by_contra hnumNotEven
    have hnumOdd : Odd q.num := by
      rwa [Int.not_even_iff_odd] at hnumNotEven
    have hnumSqOdd : Odd (q.num ^ 2) := by
      simpa [pow_two] using (Int.odd_mul.mpr ⟨hnumOdd, hnumOdd⟩)
    have hnumSqNotEven : ¬ Even (q.num ^ 2) := by
      rw [Int.not_even_iff_odd]
      exact hnumSqOdd
    exact hnumSqNotEven hnumSqEven
  obtain ⟨k, hk⟩ := hnumEven
  have hdenSqEven : Even ((q.den : ℤ) ^ 2) := by
    use k ^ 2
    rw [hk] at hnumden
    ring_nf at hnumden ⊢
    linarith
  have hdenEven : Even (q.den : ℤ) := by
    by_contra hdenNotEven
    have hdenOdd : Odd (q.den : ℤ) := by
      rwa [Int.not_even_iff_odd] at hdenNotEven
    have hdenSqOdd : Odd ((q.den : ℤ) ^ 2) := by
      simpa [pow_two] using (Int.odd_mul.mpr ⟨hdenOdd, hdenOdd⟩)
    have hdenSqNotEven : ¬ Even ((q.den : ℤ) ^ 2) := by
      rw [Int.not_even_iff_odd]
      exact hdenSqOdd
    exact hdenSqNotEven hdenSqEven
  have htwo_num_int : (2 : ℤ) ∣ q.num := by
    use k
    linarith
  have htwo_num : 2 ∣ q.num.natAbs := by
    exact (Int.natCast_dvd).mp htwo_num_int
  have htwo_den : 2 ∣ q.den := by
    exact (Int.dvd_natCast).mp (even_iff_two_dvd.mp hdenEven)
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) htwo_num htwo_den q.reduced

/- To prove a negation, we assume the positive statement and derive `False`. -/

theorem even_not_dvd_sq_add_one {x : ℤ} (hx : Even x) : ¬ (2 ∣ x ^ 2 + 1) := by
  intro hdiv
  obtain ⟨k, hk⟩ := hx
  rw [hk] at hdiv
  have hodd : Odd ((k + k) ^ 2 + 1) := by
    use 2 * k ^ 2
    ring
  have heven : Even ((k + k) ^ 2 + 1) := even_iff_two_dvd.mpr hdiv
  rw [odd_iff_not_even] at hodd
  exact hodd heven

/- Exercises -/

-- Exercise 9.1 (logical content of the truth-table exercise)
example (R S : Prop) (h : ¬ R → S) (hNotS : ¬ S) : R := by
  sorry

-- Exercise 9.2 (direct proof)
example {x : ℤ} (h : Even (3 * x + 1)) : Odd (5 * x + 2) := by
  sorry

-- Exercise 9.2 (contrapositive proof)
example {x : ℤ} (h : Even (3 * x + 1)) : Odd (5 * x + 2) := by
  sorry

-- Exercise 9.2 (proof by contradiction)
example {x : ℤ} (h : Even (3 * x + 1)) : Odd (5 * x + 2) := by
  sorry

-- Exercise 9.3
example {a b c : ℤ} (h : a ^ 2 + b ^ 2 = c ^ 2) : Even a ∨ Even b := by
  sorry

-- Exercise 9.4
example : Irrational (Real.sqrt 3) := by
  sorry

-- Exercise 9.5 (cube root of 2 is irrational)
example : ¬ ∃ q : ℚ, (q : ℝ) ^ 3 = 2 := by
  sorry

-- Exercise 9.6
example (x : ℚ) {y : ℝ} (hy : Irrational y) : Irrational ((x : ℝ) + y) := by
  sorry

-- Exercise 9.7
example {x : ℚ} (hx : x ≠ 0) {y : ℝ} (hy : Irrational y) :
    Irrational ((x : ℝ) * y) := by
  sorry

-- Exercise 9.8
example : ¬ ∃ y : ℝ, Irrational y ∧ 0 < y ∧
    ∀ z : ℝ, Irrational z → 0 < z → y ≤ z := by
  sorry

-- Exercise 9.9
example {x y : ℤ} : 33 * x + 132 * y ≠ 57 := by
  sorry
