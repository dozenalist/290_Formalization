import LeanProjects.Logic
import Mathlib.Order.Defs.Unbundled

/-!
# Relations in Lean

This file is a follow-up to `Logic.lean`. A relation on a type `X` is simply a
predicate in two variables:

* `R : X → X → Prop`
* `R x y` means "`x` is related to `y`"

Typical examples are:

* equality: `x = y`
* order relations: `x ≤ y`, `x < y`
* divisibility on natural numbers: `m ∣ n`

The most common structural properties of a relation are:

* reflexive: every element is related to itself;
* symmetric: if `x` is related to `y`, then `y` is related to `x`;
* transitive: if `x` is related to `y` and `y` is related to `z`, then
  `x` is related to `z`.
-/

set_option autoImplicit false

universe u v

namespace RelationsCrashCourse

/-!
## 1. Relations as functions into `Prop`
-/

abbrev RelationOn (X : Type u) := X → X → Prop

#check Eq
#check ((· ≤ ·) : Nat → Nat → Prop)
#check ((· < ·) : Nat → Nat → Prop)
#check ((· ∣ ·) : Nat → Nat → Prop)

section BasicDefinitions

variable {X : Type u}
variable (R : RelationOn X)

#check Reflexive
#check Symmetric
#check Transitive
#check Equivalence

theorem reflexive_iff : Reflexive R ↔ ∀ x : X, R x x :=
  Iff.rfl

theorem symmetric_iff : Symmetric R ↔ ∀ ⦃x y : X⦄, R x y → R y x :=
  Iff.rfl

theorem transitive_iff :
    Transitive R ↔ ∀ ⦃x y z : X⦄, R x y → R y z → R x z :=
  Iff.rfl

end BasicDefinitions

/-!
## 2. Using the properties

Once we have hypotheses saying that a relation is reflexive, symmetric, or
transitive, we use them exactly as functions.
-/

section UsingProperties

variable {X : Type u} {R : RelationOn X}
variable {x y z : X}

theorem use_reflexive (hR : Reflexive R) : R x x :=
  hR x

theorem use_symmetric (hR : Symmetric R) (hxy : R x y) : R y x :=
  hR hxy

theorem use_transitive (hR : Transitive R) (hxy : R x y) (hyz : R y z) :
    R x z :=
  hR hxy hyz

end UsingProperties

/-!
## 3. Equality as a relation

Equality is the basic example of an equivalence relation.
-/

section EqualityRelation

variable {X : Type u}

theorem eq_reflexive : Reflexive (@Eq X) := by
  intro x
  rfl

theorem eq_symmetric : Symmetric (@Eq X) := by
  intro x y hxy
  exact hxy.symm

theorem eq_transitive : Transitive (@Eq X) := by
  intro x y z hxy hyz
  exact hxy.trans hyz

theorem eq_isEquivalence : Equivalence (@Eq X) := by
  constructor
  · exact eq_reflexive (X := X)
  · intro x y hxy
    exact hxy.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

end EqualityRelation

/-!
## 4. Relations coming from functions

If `f : X → Y`, then we can declare two elements of `X` to be related when
they have the same image under `f`.

This is an important source of equivalence relations.
-/

section SameValueRelation

variable {X : Type u} {Y : Type v}

def sameValue (f : X → Y) : RelationOn X :=
  fun x y => f x = f y

theorem sameValue_reflexive (f : X → Y) : Reflexive (sameValue f) := by
  intro x
  rfl

theorem sameValue_symmetric (f : X → Y) : Symmetric (sameValue f) := by
  intro x y hxy
  exact hxy.symm

theorem sameValue_transitive (f : X → Y) : Transitive (sameValue f) := by
  intro x y z hxy hyz
  exact hxy.trans hyz

theorem sameValue_isEquivalence (f : X → Y) : Equivalence (sameValue f) := by
  constructor
  · exact sameValue_reflexive f
  · intro x y hxy
    exact hxy.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

end SameValueRelation

/-!
## 5. Concrete examples on `Nat`
-/

section NatExamples

abbrev natLe : RelationOn Nat := (· ≤ ·)
abbrev natLt : RelationOn Nat := (· < ·)
abbrev divides : RelationOn Nat := (· ∣ ·)

def sameParity : RelationOn Nat :=
  sameValue (fun n : Nat => n % 2)

/-!
### The relation `≤`

On natural numbers, `≤` is reflexive and transitive, but not symmetric.
-/

theorem natLe_reflexive : Reflexive natLe := by
  intro n
  exact le_rfl

theorem natLe_transitive : Transitive natLe := by
  intro a b c hab hbc
  exact Nat.le_trans hab hbc

theorem natLe_not_symmetric : ¬ Symmetric natLe := by
  intro hSym
  have h23 : natLe 2 3 := by
    decide
  have h32 : natLe 3 2 := hSym h23
  have hNot : ¬ natLe 3 2 := by
    decide
  exact hNot h32

/-!
### The relation `<`

The strict order `<` is transitive, but not reflexive.
-/

theorem natLt_transitive : Transitive natLt := by
  intro a b c hab hbc
  exact Nat.lt_trans hab hbc

theorem natLt_not_reflexive : ¬ Reflexive natLt := by
  intro hRefl
  have h00 : natLt 0 0 := hRefl 0
  exact lt_irrefl 0 h00

/-!
### Divisibility

Divisibility is reflexive and transitive on `Nat`.
-/

theorem divides_reflexive : Reflexive divides := by
  intro n
  exact dvd_rfl

theorem divides_transitive : Transitive divides := by
  intro a b c hab hbc
  exact dvd_trans hab hbc

theorem divides_three_twelve : divides 3 12 := by
  change 3 ∣ 12
  exact ⟨4, by decide⟩

/-!
### Same parity

Two natural numbers have the same parity if they have the same remainder mod
`2`.
-/

theorem sameParity_reflexive : Reflexive sameParity := by
  simpa [sameParity] using
    (sameValue_reflexive (f := fun n : Nat => n % 2))

theorem sameParity_symmetric : Symmetric sameParity := by
  simpa [sameParity] using
    (sameValue_symmetric (f := fun n : Nat => n % 2))

theorem sameParity_transitive : Transitive sameParity := by
  simpa [sameParity] using
    (sameValue_transitive (f := fun n : Nat => n % 2))

theorem sameParity_4_10 : sameParity 4 10 := by
  simp [sameParity, sameValue]

theorem sameParity_7_13 : sameParity 7 13 := by
  simp [sameParity, sameValue]

theorem not_sameParity_3_4 : ¬ sameParity 3 4 := by
  simp [sameParity, sameValue]

end NatExamples

/-!
## 6. What to remember

For work with relations in Lean, the key points are:

* a relation on `X` is just a term of type `X → X → Prop`;
* `Reflexive R`, `Symmetric R`, and `Transitive R` are themselves propositions;
* proving these properties usually means introducing variables and hypotheses,
  then constructing the desired proof directly;
* equality is the fundamental equivalence relation;
* many useful equivalence relations come from functions.

## Suggested exercises

Try proving some of the following statements yourself.

```lean
theorem symm_of_symmetric
    {X : Type} {R : X → X → Prop}
    (hR : Symmetric R) {x y : X} (hxy : R x y) :
    R y x := by
  sorry

theorem trans_of_transitive
    {X : Type} {R : X → X → Prop}
    (hR : Transitive R) {x y z : X}
    (hxy : R x y) (hyz : R y z) :
    R x z := by
  sorry

theorem eq_equivalence_exercise (X : Type) : Equivalence (@Eq X) := by
  sorry

theorem natLt_not_reflexive_exercise :
    ¬ Reflexive ((· < ·) : Nat → Nat → Prop) := by
  sorry

theorem divides_four_twelve_exercise :
    ((· ∣ ·) : Nat → Nat → Prop) 4 12 := by
  sorry

theorem sameParity_5_11_exercise :
    sameParity 5 11 := by
  sorry

theorem not_sameParity_6_9_exercise :
    ¬ sameParity 6 9 := by
  sorry
```
-/

end RelationsCrashCourse
