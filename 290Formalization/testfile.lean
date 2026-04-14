
/-
This is a test file for lean and leanblueprint
-/



namespace test

inductive Even : Nat → Prop where
  | two_mul (k) : Even (2 * k)


theorem Even_four : Even 4 :=
  .two_mul 2
