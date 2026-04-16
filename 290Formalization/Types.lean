/-!
# A crash course in type theory for mathematicians

Lean is built on the principle that propositions and types are handled by the
same formal language.

The basic slogan is:

* `x : X` means "`x` is a term of the type `X`".
* if `P : Prop`, then `h : P` means "`h` is a proof of `P`".
* a function `f : X → Y` sends terms of `X` to terms of `Y`.
* an implication `h : P → Q` sends proofs of `P` to proofs of `Q`.

So implication is not merely analogous to a function arrow: in Lean, it is a
function arrow.

This file is intentionally written as a compact outline. The point is not to
cover all of type theory, but to isolate the ideas that matter most when you
first read Lean as a mathematician.
-/

set_option autoImplicit false

universe u v w u'

namespace TypeTheoryCrashCourse

/-!
## 1. Types, terms, and propositions

`Type` is the universe of ordinary mathematical data.
`Prop` is the universe of propositions.

For a mathematician:

* `Nat`, `Int`, `Set X`, `X → Y` are all types.
* `x : X` means that `x` is an element of `X`.
* `P : Prop` means that `P` is a proposition.
* `h : P` means that `h` is a proof of `P`.
-/

#check Type
#check Prop
#check Nat
#check Nat → Nat
#check Nat → Prop
#check Prop → Prop

/-!
## 2. Ordinary functions

The basic object of type theory is a function. We start with functions between
types, and later specialize to functions between propositions.
-/

section Functions

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u'}

def idFn (x : X) : X := x

def compose (g : Y → Z) (f : X → Y) : X → Z :=
  fun x => g (f x)

def const (y : Y) : X → Y :=
  fun _ => y

theorem idFn_apply (x : X) : idFn x = x := rfl

theorem compose_apply (g : Y → Z) (f : X → Y) (x : X) :
    compose g f x = g (f x) := rfl

theorem const_apply (y : Y) (x : X) : const (X := X) y x = y := rfl

theorem compose_eq_comp (g : Y → Z) (f : X → Y) :
    compose g f = g ∘ f := rfl

theorem comp_apply (g : Y → Z) (f : X → Y) (x : X) :
    (g ∘ f) x = g (f x) := rfl

theorem id_comp (f : X → Y) : idFn ∘ f = f := by
  funext x
  rfl

theorem comp_id (f : X → Y) : f ∘ idFn = f := by
  funext x
  rfl

theorem comp_assoc (h : Z → W) (g : Y → Z) (f : X → Y) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  funext x
  rfl

/-!
Two functions are equal when they have the same value at every input.
This is the principle of function extensionality.
-/
theorem extensionality (f g : X → Y) (h : ∀ x : X, f x = g x) : f = g :=
  funext h

/-!
The type `X → Y → Z` means `X → (Y → Z)`.

So a function of two variables is really a function which, given `x : X`,
returns a new function `Y → Z`.
-/
def swapArgs (f : X → Y → Z) : Y → X → Z :=
  fun y x => f x y

theorem swapArgs_apply (f : X → Y → Z) (x : X) (y : Y) :
    swapArgs f y x = f x y := rfl

end Functions

/-!
## 3. Propositions as types

Now let `P`, `Q`, `R` be propositions.

Then:

* a term of `P` is a proof of `P`,
* a term of `P → Q` is a function taking proofs of `P` to proofs of `Q`.

This is the Curry-Howard viewpoint. In practice, it means:

* to prove `P → Q`, assume `hP : P` and build a term of `Q`;
* to use `hPQ : P → Q`, apply it to `hP : P`.
-/

section Implication

variable {P Q R S : Prop}

theorem imp_id : P → P :=
  fun hP => hP

theorem modusPonens (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP

theorem imp_trans (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun hP => hQR (hPQ hP)

theorem imp_trans' : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  exact hQR (hPQ hP)

/-!
Implication is literally composition of functions.
-/
theorem implication_is_composition (hPQ : P → Q) (hQR : Q → R) :
    hQR ∘ hPQ = imp_trans hPQ hQR := by
  funext hP
  rfl

/-!
The type `P → Q → R` means `P → (Q → R)`.

So a proof of `P → Q → R` is a function which takes a proof of `P` and returns
another function `Q → R`.
-/
theorem imp_intro_two : P → Q → P :=
  fun hP _hQ => hP

theorem imp_swap : (P → Q → R) → Q → P → R :=
  fun h hQ hP => h hP hQ

theorem compose_three_implications
    (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) : P → S :=
  fun hP => hRS (hQR (hPQ hP))

/-!
Negation is also a function type:

* `¬ P` is notation for `P → False`.

So proving `¬ P` means giving a function that turns any hypothetical proof of
`P` into a contradiction.
-/
#check Not
#check False
#check (¬ P)

theorem not_of_imp_false (h : P → False) : ¬ P :=
  h

theorem doubleNegIntro : P → ¬¬ P := by
  intro hP hNotP
  exact hNotP hP

theorem contrapositive (hPQ : P → Q) : ¬ Q → ¬ P := by
  intro hNotQ hP
  exact hNotQ (hPQ hP)

end Implication

/-!
## 4. Universal quantification as a dependent function type

The expression `∀ x : X, A x` is a dependent function type: the target type
`A x` is allowed to depend on the input `x`.

This is the natural generalization of an ordinary function type.

For propositions, `∀ x : X, P x` says: given any `x`, we can produce a proof of
`P x`.
-/

section Forall

variable {X : Type u} {A : X → Type v} {P Q : X → Prop}

theorem specialize (h : ∀ x : X, P x) (x : X) : P x :=
  h x

def pointwise_application (f : ∀ x : X, A x) (x : X) : A x :=
  f x

theorem pointwise_implication
    (hPQ : ∀ x : X, P x → Q x) :
    (∀ x : X, P x) → ∀ x : X, Q x := by
  intro hP x
  exact hPQ x (hP x)

end Forall

/-!
## 5. What to remember

For everyday Lean, the essential mental model is:

* proving a statement means constructing a term of a type;
* proving an implication means defining a function;
* using an implication means applying a function;
* universal quantification is a dependent version of the same idea.

In short: theorem proving in Lean is largely function building.

## Suggested exercises

These are good next statements to try filling in by hand.

-/

-- variable {X : Type} {P Q R : Prop}

-- theorem imp_self : P → P := by
--   sorry

-- theorem imp_chain : (P → Q) → (Q → R) → P → R := by
--   sorry

-- theorem imp_permute : (P → Q → R) → Q → P → R := by
--   sorry

-- theorem pointwise_comp
--     {P Q R : X → Prop}
--     (hPQ : ∀ x, P x → Q x) (hQR : ∀ x, Q x → R x) :
--     ∀ x, P x → R x := by
--   sorry



end TypeTheoryCrashCourse
