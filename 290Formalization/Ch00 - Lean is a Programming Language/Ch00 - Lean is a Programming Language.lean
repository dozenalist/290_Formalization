import Mathlib.Data.Nat.Basic

namespace LeMa

/-!
# "The person who's going to have the best ideas is the person who is knee-deep in execution."
# - Brennan Lee Mulligan
-/

section Intro

/-!
# 1. Intro to Programming in Lean
-/

/-!
# Lean as a Programming Language

Lean has a become a somewhat infamous tool in the mathematics community in recent history. As
such, there are many ideas of what Lean is that float around in conversation, most of which
capturing only part of what Lean is and what Lean can do. So, what exactly is Lean?

Lean is a dependently typed, functional programming language. This means that the fundamental
structure of Lean is functions, exactly in the same way that sets are the fundamental structure
of set theory.

Dependent typing is a very strict condition for type systems in the context of programming
languages. Essentially, it means that every datum must be an instance of a type (static typing)
and an instance cannot be cast to an instance of a different type (strong typing). In contrast,
Python is weakly typed and dynamically typed, which is largely why it is quick to write Python
code and slow to run Python code. It should be noted that, while type casting is disallowed,
type coercion is allowed; this is one of the reasons why dependent typing is more than just
static typing and strong typing together.
-/

/-!
# Constructing the Naturals

Since every datum, which we call a term, must be an instance of a type, we ought to start by
defining a type. A type in Lean is defined as the aggregate of its constructors. To see this in
action, let's consider how we should define the natural numbers (beginning with zero) as a type in
Lean.
-/

inductive CopyNat : Type
| zero : CopyNat
| succ : CopyNat → CopyNat

/-!
This registers the binder `CopyNat` as an instance of `Type` produced by the listed
constructors. The first constructor is registered with the binder `zero` as an instance of
`CopyNat` and the second constructor is registered with the binder `succ` as an instance of
`CopyNat → CopyNat`. These constructors are representative of the following two axioms defining
the naturals.

* Zero exists and is a natural number.
* Given any natural number, its successor is also a natural number.

Here we named our natural number definition `CopyNat` instead of `Nat`, because `Nat` is already
defined in Lean's built-in MathLib library. Note that our `CopyNat` definition is identical to that
of MathLib's `Nat`. As such, in order to take advantage of the many tools and structures available
in MathLib, we will use `Nat` for the remainder of the text. For example, MathLib provides the
convenient alias `ℕ` to abbreviate `Nat`. Additionally, the standard decimal numerals are aliases
for instances of `ℕ`. That is, to represent the number four, we can write `4` instead of the
unwieldy expression `succ (succ (succ (succ zero)))`.

A more detailed explanation of these modeling decisions for `ℕ` is presented in the next section.
-/

#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

/-!
# Defining the Fibonacci Function

Now, let's consider how we might define a simple function: the Fibonacci sequence function. We
aim to create a function that takes as input `(n : ℕ)` and returns the nth output of the
Fibonacci sequence.

First, let's recall how we do this informally, using the binder `fib`. Given a term of type
`ℕ`, we do the following:

* If our term matches the form `zero` (or `0`), we produce `0`.
* Otherwise, if our term matches the form `succ zero` (or equivalently, `1`) then we produce `1`.
* Otherwise, if our term matches the form `succ (succ n)` (or `n + 2`) for some `n : ℕ` then we
  produce `fib (succ n) + fib n` (or `fib (n + 1) + fib n`).
-/

def fib : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

#eval fib 0

#eval fib 1

#eval fib 3

#eval fib 6

/-!
# Defining Addition on ℕ

Notice that we used the addition operator `+` in our definition of `fib`. We can do this because it
is already defined in MathLib. In this text, we will sometimes leave only a brief note like this one
instead of rebuilding everything from scratch, but not this time. Addition can be defined as
follows:
-/

def add : ℕ → ℕ → ℕ
| n, 0 => n
| n, m + 1 => add (n + 1) m

#eval add 7 1

#eval add 4 0

#eval add 3 3

/-!
Notice that, in both pattern matching cases, `n` fits the same pattern of an arbitrary
instance of `ℕ`, not associated with a specific constructor. As such, we can also define
addition on `ℕ` with the following alternative.
-/

def add' (n : ℕ) : ℕ → ℕ
| 0 => n
| m + 1 => add' (n + 1) m

#eval add' 7 1

#eval add' 4 0

#eval add' 3 3

/-!
# Defining Multiplication on ℕ (Exercise)
-/
def mul : ℕ → ℕ → ℕ := sorry

/-!
# Constructing Lists of Naturals

Now, let's build a type for lists of naturals using `ℕ`.
-/

inductive NatList : Type
| nil : NatList
| cons : ℕ → NatList → NatList

/-!
Just like our definition of `ℕ`, this registers the binder `NatList` as an instance of `Type`
produced by the listed constructors. The first constructor is registered with the binder `nil`
as an instance of `NatList` and the second constructor is registered with the binder `cons` as
an instance of `ℕ → NatList → NatList`. These constructors are representative of the following
two axioms defining the list structure (on natural numbers).

* The empty list (of naturals) exists and is a list (of naturals).
* If you have a natural number and a list of naturals, then by prepending the aforementioned natural
  to the list, you produce a new list of naturals.
-/

/-!
# Defining the Sum Function
-/

def NatList.sum : NatList → ℕ
| NatList.nil => 0
| NatList.cons n ns => n + sum ns

/-!
# Defining the Append Function
-/

def NatList.append : NatList → NatList → NatList
| NatList.nil, bs => bs
| NatList.cons a as, bs => NatList.cons a (append as bs)

/-!
# Defining the Count Function
-/

def NatList.count : ℕ → NatList → ℕ
| _, NatList.nil => 0
| a, NatList.cons b bs => (if a = b then 1 else 0) + (count a bs)

/-!
# Defining the Product Function (Exercise)
-/

def NatList.prod : NatList → ℕ := sorry

/-!
# Defining the Length Function (Exercise)
-/

def NatList.length : NatList → ℕ := sorry

/-!
# Defining the Reverse Function (Exercise)
-/

def NatList.rev : NatList → NatList := sorry

end Intro

section UnderTheHood

/-!
# 2. Lean Under the Hood
-/

/-!
# The Lean Program Architecture

Now, how does any of this allow Lean to verify mathematical proofs? In short, it doesn't, at
least not alone. When we think of a programming language, we often think only of that
languages syntax and the accompanying semantics. In reality, a programming language, as a
tool, also includes the programs surrounding and supporting the language: the assembler, the
compiler, the interpreter, etc. For Lean, there are four notable programs that, packaged with
the language, create Lean as the useful tool that it is:

* The Elaborater
* The Type Checker
* The Kernel
* The Compiler

The Elaborater translates Lean code into Core-Lean code: a language that has much less syntax
and accompanying semantics. Core-Lean is an easier language for a computer logic system to work
with but is a harder language for humans to work with. The remaining tools all work with
Core-Lean code.

The Type Checker is a computer logic system, running on the Kernel, that checks Core-Lean code
for type correctness. This system is what gives Lean the property of logical soundness.
Specifically, passing the Type Checker is a necessary condition for logical soundness. In
essence, think of any mathematical proposition and a proposed proof of said proposition. The
proposed proof of this proposition may or not be logically sound in reality; however, the Type
Checker will NEVER pass a logically unsound proof. As a consequence of this property, it is
possible that there are logically sound proofs expressible in the Lean language that will be
failed by the Type Checker. The goal of writing a good Type Checker is to pass as many
logically sound proofs without passing any logically unsound proofs.

We mentioned that the Type Checker runs on the Kernel. Unsurprisingly, the Type Checker is
still a program and, therefore, it needs some mechanism by which it can run. The Kernel is this
mechanism. The Kernel is a very small suite of trusted executable code that the Type Checker is
built on. It is beneficial to think of the Kernel like an Axiom Schema for a mathematical
theory: it is a small collection of programs (statements) that we assert run as expected (are
true) always so that we can deduce further results from them. The official Lean Kernel is
written in C; however, there are alternative Kernels that are written in other languages
including Rust and Lean.

Finally, the Compiler compiles Core-Lean code into executable code in a different language.
This means that Lean can compute results like any other programming language. The official Lean
compiler is written in Lean and compiles Core-Lean code into executable C code.

With all this in mind, it would preclude us from a comfortable and intuitive understanding to
jump right into learning Lean as a theorem prover. Instead, we should to start by learning Lean
as a programming language because it is, in fact, a programming language.
-/

/-!
# Explaining Nat

We can split the natural numbers into two collections: the natural umbers that are the
successor of another natural number and zero. Thus, constructing the natural numbers as a type
is tantamount to expressing these two collections as two functions. Since we are defining a
type, defining these functions is done in the formal sense, much like defining the group
operator in group theory. This means all we need to do is specify the type(s) of the data
needed for each constructor and the type that is produced from said constructor.

Let's start with naming our type. Following the convention of MathLib, we will call the type
for natural numbers `Nat`. Now that we have a binder for our type, let's introduce the notation
for having an instance of `Nat`. Suppose we want to talk about an arbitrary natural number n.
In Lean, we would express this as `n : Nat`, read as "`n` is an instance of `Nat`".

Now, let's first talk through the constructor for our successor collection of natural numbers.
The defining property of this collection is that each number is the successor of some other
natural number. In other words, there is some contract that says "if you give me a natural
number then I will produce another natural number". This statement describes a constructor that
requires one instance of `Nat` as input and produces one instance of `Nat` as output. In other
words, it is a 1-ary constructor on `Nat`. Thus, the type that defines this constructor is
`Nat → Nat`. All that remains is to specify a binder for this constructor. Following MathLib
convention, we will call this constructor `succ` for successor. To recap, the constructor for
our successor naturals is `succ : Nat → Nat`.

Now, let's talk through the constructor for our zero collection of natural numbers. The
defining property of this collection is that it has exactly one instance and this instance
exists. In other words, there is some contract that says "I will produce a natural number"
without needing any conditions to be satisfied. This statement describes a constructor that
requires zero instances of anything as input and produces one instance of `Nat` as output. In
other words, it is a 0-ary constructor on `Nat`. Thus, the type that defines this constructor
is `Nat`. All that remains is to specify a binder for this constructor. Following MathLib
convention, we will call this constructor `zero` for zero. To recap, the constructor for our
zero naturals is `zero : Nat`.

Putting all of this together we can define the natural numbers in Lean as follows:

`inductive Nat : Type`
`| zero : Nat`
`| succ : Nat → Nat`

This does the following. It registers the binder `Nat` as an instance of the type `Type`, which
is the type composed of all (universe level 0) types. Thus, we have `Nat : Type` and,
similarly, we have `Type : Type 1` and so on. Then, it defines ALL the mechanisms that can
produce an instance of `Nat` i.e. the constructors.

Informally, you may be thinking that there could be different constructors for the natural
numbers. This is correct. What we have defined is one specific type that models the natural
numbers. Thus, exactly by our definition, `Nat` has exactly two constructors. Therefore, for
any `n : Nat`, there are exactly two constructors by which it could have been made to exist:
`zero : Nat` and `succ : Nat → Nat`.
-/

/-!
# A Note on Pattern Matching

To define the `fib` function in Lean, we used pattern matching. Pattern matching uses nearly
identical syntax to defining a constructor. This is because they are the same mechanism.
Constructors take binders to types and pattern matching takes instances of a given type
(exhaustively) to another instance of a (possibly different) given type. To illustrate, let's
define `fib`.
-/

/-!
# Explaining Addition on ℕ

Think back to when you first learned how to add numbers by counting on your fingers. In order
to find `n + m`, you first count up to `n` and then count up to `m` starting from there. From
this, we have two observations regarding addition.

* First, `n + 0 = n`
* Second, `n + (m + 1) = (n + 1) + m`

Thus, we can define `add` the following process on two rules, given two terms of type `ℕ`.

* If our first term matches the form `n` for some `n : ℕ` and the second term matches `0` then
  we produce `n`.
* Otherwise, if our first term matches the form `n` for some `n : ℕ` and the second term
  matches `m + 1` for some `m : ℕ` then we produce `add (n + 1) m`.

One might note that the form for the first instance of `ℕ` is the same in both cases. We define
`add'` in addition to `add` to illustrate an equivalent way to define addition according to
this process that matches on the second instance of `ℕ` only.
-/

/-!
# Check vs Reduce vs Eval

Lean provides three main commands for computation: check, reduce, eval. Here we explain the
what these commands do and the differences between.

Check simply computes the type of a given term via the Type Checker.

Reduce computes the result of an expression via the Type Checker and Kernel execution.

Eval computes the result of an expression via the Compiler and local execution.

For example, let's perform some computations with the functions we just built.
-/

#check 7

#check fib 7

#check ℕ

#check fib

#reduce fib 7

#eval fib 7

#check add 2 7

#check add' 2 7

#check add 2

#check add' 2

#check add

#check add'

#reduce add 2 7

#reduce add' 2 7

#eval add 2 7

#eval add' 2 7

/-!
# Constructing List (for arbitrary types)
-/

inductive CopyList (α : Type) : Type
| nil : CopyList α
| cons : α → CopyList α → CopyList α

#check CopyList

/-!
# Defining the Map Function
-/

def map {α β : Type} (f : α → β) : List α → List β
| [] => []
| a :: as => (f a) :: (map f as)

/-!
# Defining the Count Function using Map and Sum
-/

def sum : List ℕ → ℕ
| [] => 0
| n :: ns => n + (sum ns)

def count_map {α : Type} [DecidableEq α] (a : α) (bs : List α) : ℕ :=
  sum (map (fun b ↦ if a = b then 1 else 0) bs)

/-!
# Defining the Filter Function
-/

def filter {α : Type} (f : α → Bool) : List α → List α
| [] => []
| a :: as => if (f a) then a :: (filter f as) else (filter f as)

/-!
# Defining the Count Function using Filter and Length
-/

def count_filter {α : Type} [BEq α] (a : α) (bs : List α) : ℕ :=
  List.length (filter (fun b ↦ a == b) bs)

end UnderTheHood

end LeMa
