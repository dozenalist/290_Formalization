
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


set_option linter.style.emptyLine false


def Nat.even (n : ℕ) : Prop :=
  ∃ k, n = 2 * k


def Nat.odd (n : ℕ) : Prop :=
  ∃ k, n = 2 * k + 1



/-
Tactic : `let`

An exists statement `p` is composed of two things.
(i) A witness (eg. `k : ℕ`)
(ii) A proof that the witness satisfies the proposition (eg `hk : n = 2 * k + 1`)
To break an exists statement into it's two parts, we can use
let `⟨k, hk⟩ := p`
-/

example (k : ℕ) (hk : Nat.even k) : Nat.even (k + 2) := by
  let ⟨j, hj⟩ := hk
  use j + 1
  rw [hj, mul_add]


/-
Tactic : `obtain` / `rfl`
If our existence proof takes the form of an equality, we can use
`obtain ⟨k, rfl⟩ := p`, and this will automatically
rewrtite the secondary hypothesis.
Otherwise, `obtain` works like `let`
-/

example (k : ℕ) (hk : Nat.even k) : Nat.even (k + 2) := by
  obtain ⟨j, rfl⟩ := hk
  exact ⟨j + 1, by rw [mul_add]⟩

/-
Tactic : `calc`
`calc` is a tactic that allows us to compose a larger proof by
chaining smaller transitive relations. Noteably, it works with
equalities and inequalities. We put each `calc` step on the left hand side
and provide the proof after a `:=` .
Lean can figure out that the previous left-hand side must be the same as
the next right-hand side if we put a `_` .
-/

example (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  calc

  (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
    rw [mul_add, add_mul, add_mul]

  _ = a * a + (b * a + a * b) + b * b := by
    rw [← add_assoc, add_assoc (a * a)]

  _ = a * a + 2 * (a * b) + b * b := by
    rw [mul_comm b a, ← two_mul]



/-
Try proving the following using these tactics.
Note : you can use `rw [sq]` to rewrite `x^2` as `x * x`
-/

-- Proposition 6.16
theorem odd_five_mul_add_three {x : ℕ} (h : Nat.even x) :
    Nat.odd (5 * x + 3) := by
  sorry

-- Proposition 6.18
theorem even_sq_sub_two_mul_add_three {n : ℕ} (h : Nat.odd n) :
    Nat.even (n ^ 2 - 2 * n + 3) := by
  sorry

-- Proposition 6.19
theorem odd_add_seven {n : ℕ} (h : Nat.even (3 * n)) :
    Nat.odd (n + 7) := by
  sorry

-- Proposition 6.20
theorem odd_four_mul_sq_sub_one {n : ℕ} (h : Nat.even n) :
    Nat.odd (4 * n^2 - 1) := by
  sorry


-- Exercise 6.3
theorem odd_sq_of_odd {x : ℕ} (h : Nat.odd x) : Nat.odd (x^2) := by
  sorry

-- Exercise 6.4
theorem odd_seven_mul_sub_five {x : ℕ} (h : Nat.even x) :
    Nat.odd (7 * x - 5) := by
  sorry

-- Exercise 6.5
theorem even_mul_add_mul {a b c : ℕ} (ha : Nat.odd a) (hc : Nat.odd c) :
    Nat.even (a * b + b * c) := by
  sorry

-- Exercise 6.7
-- Note : `∃ a b ,` is short for `∃ a, ∃ b,`
theorem exists_sq_sub_of_odd {x : ℕ} (h : Nat.odd x) :
    ∃ a b : ℕ, x = a ^ 2 - b ^ 2 := by
  sorry
