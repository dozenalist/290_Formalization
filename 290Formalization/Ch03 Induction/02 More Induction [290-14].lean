import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic
-- import Mathlib.Data.Nat.Factorial.Basic

theorem two_pow_gt_cube {n : ℕ} (h : n ≥ 10) : 2^n > n^3 := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ n nge ih =>
    calc 2 ^ (n+1) = 2^n + 2^n := by ring
      _ > n^3 + n^3 := by linarith [ih]
      _ = n^3 + n*n^2 := by ring
      _ ≥ n^3 + 10*n^2 := by gcongr
      _ = n^3 + 3*n^2 + 7*n*n := by ring
      _ ≥ n^3 + 3*n^2 + 70*n := by gcongr; linarith
      _ = n^3 + 3*n^2 + 3*n + 67*n := by ring
      _ ≥ n^3 + 3*n^2 + 3*n + 1 := by gcongr; linarith
      _ = (n+1)^3 := by ring

theorem fac_gt_two_pow {n : ℕ} (h : n ≥ 4) : n.factorial > 2^n := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ n nge ih =>
    calc (n+1).factorial = (n+1)*n.factorial := by simp only [Nat.factorial, Nat.succ_eq_add_one]
      _ > (n+1)*2^n := by gcongr
      _ > 2*2^n := by gcongr; linarith
      _ = 2^(n+1) := by ring

#check Finset.card_powerset

open Classical in
theorem Finset.card_powerset' {α : Type} (s : Finset α) :
    s.powerset.card = 2 ^ s.card := by
    induction s using Finset.induction with
    | empty =>
      simp
    | insert a s' ha ih =>
      have H : (image (insert a) s'.powerset).card = (s'.powerset).card := by
        apply Finset.card_image_of_injOn
        intro x xin y yin eq
        apply congrArg (fun t => t.erase a) at eq
        repeat rw [Finset.erase_insert] at eq
        ·  exact eq
        ·  exact notMem_of_mem_powerset_of_notMem yin ha
        ·  exact notMem_of_mem_powerset_of_notMem xin ha
      have H' : s'.powerset ∩ image (insert a) s'.powerset = ∅ := by
        rw [← disjoint_iff_inter_eq_empty, Finset.disjoint_left]
        intro x xin xin'
        have : a ∉ x := notMem_of_mem_powerset_of_notMem xin ha
        have : a ∈ x := by
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp xin'
          exact Finset.mem_insert_self a y
        contradiction
      simp [powerset_insert s' a, Finset.card_union,
        H, card_insert_of_notMem ha]
      grind

-- Multiple base cases

theorem two_pow_gt_square (n : ℕ) : 2^(n+1) > n^2 := by
  by_cases h : n < 3
  · interval_cases n <;> norm_num
  · rw [not_lt] at h
    induction n, h using Nat.le_induction with
    | base => norm_num
    | succ n =>
      calc 2 ^ (n + 1 + 1) = 2*2^(n+1) := by ring
        _ > 2*n^2 := by gcongr
        _ = n^2 + n*n := by ring
        _ ≥ n^2 + 3*n := by gcongr
        _ = n^2 + 2*n + n := by ring
        _ ≥ n^2 + 2*n + 1 := by gcongr; linarith
        _ = (n + 1) ^ 2 := by ring
