import «290Formalization».«Ch01 - Type Theory».«Ch01 - Type Theory»


/-!
# Logic in Lean

This file is a follow-up to `Types.lean`. The main theme is that the logical
connectives are themselves types:

* `P → Q` is the type of functions from proofs of `P` to proofs of `Q`;
* `P ∧ Q` is the type of pairs consisting of a proof of `P` and a proof of `Q`;
* `P ∨ Q` is the type of a proof of `P` or a proof of `Q`;
* `P ↔ Q` is the type of two implications, one in each direction;
* `∀ x, P x` is a dependent function type;
* `∃ x, P x` is the type of a witness `x` together with a proof of `P x`.

For tactics, the most useful new ones in this file are:

* `constructor` for goals of shape `P ∧ Q` and `P ↔ Q`;
* `left` and `right` for goals of shape `P ∨ Q`;
* `cases h` for breaking apart hypotheses of shape `P ∧ Q`, `P ∨ Q`, or
  `∃ x, P x`;
* `intro x` for goals of shape `∀ x, ...`;
* `use a` for goals of shape `∃ x, ...`.

Lean input:

* `\and` gives `∧`
* `\or` gives `∨`
* `\iff` gives `↔`
* `\forall` gives `∀`
* `\exists` gives `∃`
-/

set_option autoImplicit false

universe u

namespace LogicCrashCourse

/-!
## 1. The basic logical connectives
-/

#check And
#check Or
#check Iff
#check Exists

section Connectives

variable {P Q R : Prop}

/-!
### Implication

This was the main point of `Types.lean`: implication is just a function type.
-/

theorem implies_trans (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun hP => hQR (hPQ hP)

theorem implies_trans_tactic (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  exact hPQ hP

/-!
### Conjunction

A proof of `P ∧ Q` consists of a proof of `P` and a proof of `Q`.

To prove a conjunction goal, `constructor` creates the two subgoals.
To use a conjunction hypothesis, `cases` breaks it into its components.
-/

theorem and_intro_term (hP : P) (hQ : Q) : P ∧ Q :=
  And.intro hP hQ

theorem and_intro_tactic (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

theorem and_left (h : P ∧ Q) : P :=
  h.left

theorem and_right (h : P ∧ Q) : Q :=
  h.right

theorem and_comm_term : P ∧ Q → Q ∧ P :=
  fun h => And.intro h.right h.left

theorem and_comm_tactic : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hP hQ =>
      constructor
      · exact hQ
      · exact hP

/-!
### Disjunction

To prove `P ∨ Q`, it suffices to prove one side. The tactics `left` and
`right` indicate which side we are proving.

To use a hypothesis `h : P ∨ Q`, the tactic `cases h` splits the argument into
the two possible cases.
-/

theorem or_intro_left (hP : P) : P ∨ Q :=
  Or.inl hP

theorem or_intro_right (hQ : Q) : P ∨ Q :=
  Or.inr hQ

theorem or_comm_tactic : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP =>
      right
      exact hP
  | inr hQ =>
      left
      exact hQ

theorem or_comm_tactic' : P ∨ Q → Q ∨ P
  | .inl hP => .inr hP
  | .inr hQ => .inl hQ


theorem or_elim_tactic (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP =>
      exact hPR hP
  | inr hQ =>
      exact hQR hQ

/-!
### Biconditional

`P ↔ Q` is just a pair of implications. To prove it, use `constructor`.
To use it, the projections are:

* `h.mp : P → Q`
* `h.mpr : Q → P`

Because `↔` is an equivalence, it also works naturally with `rw`.
-/

theorem iff_intro_term (hPQ : P → Q) (hQP : Q → P) : P ↔ Q :=
  Iff.intro hPQ hQP

theorem iff_intro_tactic (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  constructor
  · exact hPQ
  · exact hQP

theorem iff_symm_term : (P ↔ Q) → (Q ↔ P) :=
  fun h => Iff.intro h.mpr h.mp

theorem iff_symm_tactic : (P ↔ Q) → (Q ↔ P) := by
  intro h
  constructor
  · exact h.mpr
  · exact h.mp

theorem iff_rw_example (hPQ : P ↔ Q) (hP : P) : Q := by
  rw [← hPQ]
  exact hP

end Connectives

/-!
## 2. Quantifiers: `∀` and `∃`

The universal quantifier `∀` behaves like a function space.
The existential quantifier `∃` behaves like a witness paired with a proof.
-/

section Quantifiers

variable {X : Type u} {P Q : X → Prop} {a : X}

/-!
### Universal quantifiers

For a goal `∀ x, P x`, use `intro x`.
For a hypothesis `h : ∀ x, P x`, use `h x`.
-/

theorem forall_goal
    (hPQ : ∀ x : X, P x → Q x)
    (hP : ∀ x : X, P x) :
    ∀ x : X, Q x := by
  intro x
  exact hPQ x (hP x)

theorem forall_hypothesis (h : ∀ x : X, P x) : P a :=
  h a

/-!
### Existential quantifiers

For a goal `∃ x, P x`, use `use witness`.
For a hypothesis `h : ∃ x, P x`, use `cases h` to extract the witness and its
property.
-/

theorem exists_goal (ha : P a) : ∃ x : X, P x := by
  use a

theorem exists_hypothesis_to_exists_goal
    (hPQ : ∀ x : X, P x → Q x)
    (h : ∃ x : X, P x) :
    ∃ x : X, Q x := by
  cases h with
  | intro x hx =>
      use x
      exact hPQ x hx

theorem exists_hypothesis_to_forall_conclusion
    (h : ∃ x : X, P x)
    (hAll : ∀ x : X, P x → Q x) :
    ∃ x : X, Q x := by
  cases h with
  | intro x hx =>
      use x
      exact hAll x hx

end Quantifiers

/-!
## 3. The `cases` tactic

The tactic `cases` is the main way to use hypotheses that were built by
constructors. In this file, the key examples are:

* `cases h` for `h : P ∧ Q`
* `cases h` for `h : P ∨ Q`
* `cases h` for `h : ∃ x, P x`

When you use `cases`, Lean generates one goal for each constructor.
-/

section CasesExamples

variable {X : Type u} {P Q R : Prop} {S : X → Prop}

theorem cases_on_and (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro hP hQ =>
      constructor
      · exact hQ
      · exact hP

theorem cases_on_or (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP =>
      exact hPR hP
  | inr hQ =>
      exact hQR hQ

theorem cases_on_exists (h : ∃ x : X, S x) : ∃ x : X, S x := by
  cases h with
  | intro x hx =>
      use x

end CasesExamples

/-!
## 4. Common proof techniques

Three standard proof styles are:

* direct proof: assume the hypotheses and build the conclusion;
* contrapositive proof: prove `¬ Q → ¬ P` instead of `P → Q`;
* contradiction: derive `False` from incompatible assumptions.

The first one is constructive; the other two require the law of the excluded middle.
A fully classical proof by contradiction, where one assumes `¬ P` and deduces `P`,
will be discussed in the next section.
-/

section ProofTechniques

variable {P Q R : Prop}



#check Decidable
#check Classical.propDecidable P

theorem direct_proof (hPQ : P → Q) (hP : P) : Q := by
  exact hPQ hP

theorem contrapositive_proof (hPQ : P → Q) : ¬ Q → ¬ P := by
  intro hNotQ hP
  exact hNotQ (hPQ hP)

theorem contradiction_from_hypotheses (hP : P) (hNotP : ¬ P) : Q := by
  exact False.elim (hNotP hP)

end ProofTechniques

/-!
## 5. Classical reasoning: LEM, DNE, and `open Classical`

Lean is constructive by default. This means that, in general, you cannot use:

* the law of excluded middle `P ∨ ¬ P`;
* double-negation elimination `¬¬ P → P`;
* proof by contradiction in the classical sense.

If you want those principles, a common local choice is to write
`open Classical in` before a theorem, or `open Classical` for a larger block.
Then Lean can use classical decidability for propositions.

This is often convenient, but it is good to know when you are using it.
-/

section ClassicalReasoning

variable {P Q : Prop}

open Classical in
theorem law_of_excluded_middle : P ∨ ¬ P := by
  exact Classical.em P

open Classical in
theorem double_negation_elimination : ¬¬ P → P := by
  intro hNNP
  by_contra hNP
  exact hNNP hNP

open Classical in
theorem by_cases_example (hP : P → Q) (hNotP : ¬ P → Q) : Q := by
  by_cases hp : P
  · exact hP hp
  · exact hNotP hp

open Classical in
theorem by_contradiction_example (h : ¬¬ P) : P := by
  by_contra hNP
  exact h hNP

end ClassicalReasoning

/-!
## Suggested exercises

The best way to learn this material is to prove a few small theorems yourself.

```lean
theorem and_assoc (P Q R : Prop) : (P ∧ Q ∧ R) ↔ ((P ∧ Q) ∧ R) := by
  sorry

theorem or_assoc (P Q R : Prop) : (P ∨ Q ∨ R) ↔ ((P ∨ Q) ∨ R) := by
  sorry

theorem forall_exists_example
    {X : Type} {P Q : X → Prop}
    (h : ∀ x, P x → Q x) :
    (∃ x, P x) → ∃ x, Q x := by
  sorry

open Classical

theorem dne_implies_em (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  sorry
```
-/



theorem by_contra {p : Prop} (h : ¬¬ p) : p :=
  match Classical.em p with
  | .inl hp => hp
  | .inr hnp => False.elim (h hnp)

  -- (Classical.em p).casesOn id fun hnp => (h hnp).elim




theorem contrapose_mp (p q : Prop) : (p → q) → (¬ q → ¬ p) :=
  fun h hnq hp => hnq (h hp)

theorem contrapose_mpr (p q : Prop) : (¬ p → ¬ q) → (q → p) :=
  fun h hq => by_contra fun hnp => h hnp hq

theorem contrapose (p q : Prop) : (p → q) ↔ (¬ q → ¬ p) :=
  Iff.intro (contrapose_mp _ _) (contrapose_mpr _ _)



-- Axiom 5.6
theorem not_forall {α} (P : α → Prop) : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := by
  constructor <;> intro h
  { contrapose h
    intro x
    contrapose h
    exact ⟨x, h⟩ }
  { intro h'
    let ⟨x,hx⟩ := h
    exact hx (h' x) }


end LogicCrashCourse
