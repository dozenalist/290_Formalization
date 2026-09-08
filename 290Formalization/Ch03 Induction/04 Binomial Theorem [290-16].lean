import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finsupp.Notation

-- assert_not_exists Finset.card_powersetCard

namespace LeMa.Nat
open scoped Classical



/--
We could define Nat.choose the way the book defines it, as

`n.choose k = if k ≤ n then n! / (k! * (n - k)!)`

But division and subtraction are hard to work with in ℕ.
The following inductive definition is much nicer, and
we will later prove that it is equivalent
-/
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)



-- Theorem 16.4
theorem choose_succ_succ (n k : ℕ) : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
  sorry

-- Theorem 16.6
theorem choose_eq_card_subset_has_card {α} {n : ℕ} (s : Finset α) (hs : s.card = n) (k : ℕ) :
    {p ∈ s.powerset | p.card = k}.card = n.choose k := by

  induction n generalizing k s with
  | zero =>
    match k with
    | 0 => sorry

    | k + 1 => sorry


  | succ n ih =>

    have sne : s.Nonempty := sorry
    obtain ⟨x, hx⟩ := Finset.nonempty_def.mp sne

    match k with
    | 0 => sorry

    | k + 1 =>
      calc
        _ = ({p ∈ s.powerset | p.card = k + 1 ∧ x ∈ p} ∪
            {p ∈ s.powerset | p.card = k + 1 ∧ x ∉ p}).card := by
          sorry

        _ = {p ∈ s.powerset | p.card = k + 1 ∧ x ∈ p}.card +
            {p ∈ s.powerset | p.card = k + 1 ∧ x ∉ p}.card := by
          sorry

        _ = {p ∈ (s.erase x).powerset | p.card = k}.card +
            {p ∈ (s.erase x).powerset | p.card = k + 1}.card := by
          sorry

        _ = (n + 1).choose (k + 1) := by
          sorry


-- Theorem 16.8 (Binomial Theorem)
theorem add_pow {R} [CommRing R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ i ∈ Finset.range (n + 1), n.choose i * x ^ i * y ^ (n - i) := by

  induction n with

  | zero => sorry

  | succ n ih => calc

    _ = x * (x + y) ^ n + (x + y) ^ n * y := by
      ring

    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i) * x ^ (i + 1) * y ^ (n - i)
      + ∑ i ∈ Finset.range (n + 1), (n.choose i) * x ^ i * y ^ (n + 1 - i) := by
      sorry

    _ = ∑ i ∈ Finset.range (n + 2), ((n.choose i) + n.choose (i + 1)) * x ^ i * y ^ (n + 1 - i) := by
      sorry
    _ = _ := by
      sorry

open Nat

scoped notation n "!" => Nat.factorial n

theorem choose_eq (n k : ℕ) :
    n.choose k = if k ≤ n then ((n)! / ((k)! * (n - k)!)) else 0 := by

  induction n generalizing k with

  | zero => sorry

  | succ n ih =>
    match k with
    | 0 => sorry
    | k + 1 => sorry



theorem choose_zero_right (n : ℕ) : n.choose 0 = 1 := by
  sorry

theorem choose_self (n : ℕ) : n.choose n = 1 := by
  sorry

theorem choose_one_right (n : ℕ) : n.choose 1 = n := by
  sorry

theorem choose_pred (n : ℕ) : n.choose (n - 1) = n := by
  sorry

theorem choose_sub_self (n k : ℕ) (hk : k ≤ n) : n.choose (n - k) = k := by
  sorry

theorem choose_mul (n k j : ℕ) :
    n.choose j * (n - j).choose k = n.choose k * (n - k).choose j := by
  sorry

theorem sum_choose (n : ℕ) : ∑ k ∈ Finset.range (n + 1), n.choose k = 2 ^ n := by
  sorry

theorem sum_neg_one_pow_choose (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℤ) = 0 := by
  sorry

open MvPolynomial in

theorem coeff_pow_eight :

  let powers : Fin 2 →₀ ℕ :=
    { support := {0, 1}
      toFun := ![5, 3]
      mem_support_toFun := by decide }

coeff powers ((2 * X 0 + 3 * X 1) ^ 8) = 48384 := by
    sorry


theorem choose_mul_right (n k : ℕ) : k * n.choose k = n * (n - 1).choose (k - 1) := by
  sorry

theorem even_two_mul_choose (n : ℕ) : Even ((2 * n).choose n) := by
  sorry

theorem choose_bound_of_nine_le (n k : ℕ) (hn : 9 ≤ n) : n.choose k < 2 ^ (n - 2) := by
  sorry

theorem choose_bound_of_eight_le (n k : ℕ) (hn : 8 ≤ n) : n.choose k < (n - 3)! := by
  sorry




end Nat

end LeMa
