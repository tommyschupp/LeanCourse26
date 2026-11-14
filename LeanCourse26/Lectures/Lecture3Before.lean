import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real
noncomputable section
variable (a b c : ℝ)

/-
# Practical remarks
* Assignment 2 is posted on GitHub.
  Due date: upload by 28.10 before class on eCampus.
  WARNING: Contains material from Lecture 4
* Remember to follow the generative AI policy in the syllabus
* As last time: the lecture will be posted in advance of class,
  so you can open the file yourself during class.
* To get the latest version of this repository,
  follow the instructions in the README file.
-/

/- # Last week -/

/- Last week we saw
* everything has a type: objects (e.g. numbers, functions) and statements (Prop)
* you can prove statements using `tactics`: we saw
  - the `rfl` tactic (for trivial statements like `2 = 2`)
  - the `ring` tactic for proving identities in a (commutative) ring
  - the `rw` tactic for rewriting by an equation or equivalence
* `calc` blocks can make long calculation proofs more readable

* dealing with implications, forward and backward reasoning
  - forward reasoning: use `have` for intermediate goals; `intro` and `exact` to conclude a proof
  - `specialize` can also be used to apply a hypothesis to arguments
  - backward reasoning: use `apply` (or `exact` and `refine`)
-/

/-
# Difference between `rw` and `apply`
- `rw` can be used to rewrite a subexpression (almost) anywhere in the goal,
  `apply` has to match the outermost thing you are trying to prove.
- *generally* you use `rw` with an equality,
  and `apply` with implications and "for all" statements.
-/

/- Often we can `apply` lemmas from Mathlib. -/
variable (f g : ℝ → ℝ)
#check (Continuous.add : Continuous f → Continuous g → Continuous (fun x : ℝ ↦ f x + g x))
#check (Continuous.mul : Continuous f → Continuous g → Continuous (fun x : ℝ ↦ f x * g x))
#check (continuous_id : Continuous (fun x : ℝ ↦ x))
#check (continuous_sin : Continuous (fun x : ℝ ↦ sin x))

example : Continuous (fun x ↦ x + x * Real.sin x) := by
  apply Continuous.add
  apply continuous_id
  apply Continuous.mul
  apply continuous_id
  apply continuous_sin

/- # Today: logic (if and only if, for all, and, exists, or, not) -/

/- ## If and only if
* You can use `constructor` to prove an "if and only if" statement
* To use an "if and only if" statement `h`, you can use any of the following
  - `apply h.1`
  - `apply h.2`
  - `rw [h]`
  - `rw [← h]`
-/


#check exp_le_exp
#check (exp_le_exp.1 : exp a ≤ exp b → a ≤ b)
#check (exp_le_exp.2 : a ≤ b → exp a ≤ exp b)


example (h : a ≤ b) : exp a ≤ exp b := by
  apply exp_le_exp.2
  apply h



example (h : exp a ≤ exp b) : a ≤ b := by
  apply exp_le_exp.1
  apply h


example {p q : Prop} (h1 : p → q) (h2 : q → p) : p ↔ q := by
  constructor
  · apply h1
  · apply h2



/- ## Universal quantification
The tactics for universal quantification and implication are the same.
* We can use `intro` to prove an universal quantification (or implication).
* We can use `apply` or `specialize` to use a hypothesis
  that is a universal quantification (or implication). -/


def Injective (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, f x = f y → x = y


example (f g : ℝ → ℝ) (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by
    intro y x e
    apply hg at e
    apply hf at e
    assumption



/- ## Conjunction

In Lean the conjunction of two statements `P` and `Q` is denoted by
`P ∧ Q`, read as "P and Q".

We can use a conjunction as follows:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.
Note that this is the same as for `↔`.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `obtain ⟨hP, hQ⟩ := h`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `obtain ⟨hPQ, hQP⟩ := h`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
* Equivalences behave very similarly to equalities, if
  `h : P ↔ Q`, then `rw [h]` will replace `P` with `Q` in the goal.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro H
  obtain ⟨hp, hq⟩ := H
  specialize h hp
  specialize h' hq
  constructor
  · assumption
  · assumption

/- Exercise: prove this. Hint: you can do this in one line. -/
example (p q r s : Prop) (h : p ↔ r) (h' : q ↔ s) : p ∧ q ↔ r ∧ s := by
  rw[h, h']

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ):= ∀ x, ContinuousAtPoint f x

-- Exercise: prove this
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  constructor
  intro fc x
  apply hfg at x
  apply x.1
  apply fc
  intro fd y
  apply hfg at y
  apply y.2
  apply fd



/- ## Existential quantifiers -/


/-
In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be any expression.
You can also use `exact ⟨x₀, hPx₀⟩`, where `hPx₀ : P x₀`.

In order to use `h : ∃ x, P x`, we use can use
`obtain ⟨x₀, hx₀⟩ := h`
to fix one `x₀` that works.
-/

example {α : Type*} [PartialOrder α]
    (isDense : ∀ x y : α, x < y → ∃ z : α, x < z ∧ z < y)
    (x y : α) (hxy : x < y) :
    ∃ z₁ z₂ : α, x < z₁ ∧ z₁ < z₂ ∧ z₂ < y := by
  have Z1 : ∃z₁ : α, x < z₁ ∧ z₁ < y := by
    apply isDense
    apply hxy
  obtain ⟨z₁, hz₁⟩ := Z1
  have Z2 : ∃z₂ : α, z₁ < z₂ ∧ z₂ < y := by
    apply isDense
    apply hz₁.2
  obtain ⟨z₂, hz₂⟩ := Z2
  use z₁, z₂
  constructor
  apply hz₁.1
  constructor
  apply hz₂.1
  apply hz₂.2



/- Lean supports shorthands for quantifiers
followed by an infix predicate (`<`, `≥`, `∈`, ...) -/
example (P : ℕ → Prop) : (∃ n > 3, P n) ↔ (∃ n, n > 3 ∧ P n) := by
  rfl
example (P : ℕ → Prop) : (∀ n ≤ 10, P n) ↔ (∀ n, n ≤ 10 → P n) := by
  rfl

/- ## Disjunctions -/

/-
Lean denotes by `∨` the logical OR operator.

In order to directly prove a goal `P ∨ Q`,
we use either the `left` tactic and prove `P` or the `right`
tactic and prove `Q`.

In order to make use of an assumption
  `h : P ∨ Q`
we use the obtain tactic:
  `obtain hP | hQ := h`
which creates two proof branches: one branch assuming `hP : P`,
and one branch assuming `hQ : Q`.
-/

#check (mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0)

example : a = a * b → a = 0 ∨ b = 1 := by
  intro h
  have H : a * (b-1) = 0 := by linarith
  rw[mul_eq_zero] at H
  obtain ha | hb := H
  · left
    assumption
  · right
    linarith



#check (lt_trichotomy a b : a < b ∨ a = b ∨ b < a)

example (f : ℝ → ℝ) (hf : StrictMono f) : Injective f := by
  intro x y h
  obtain hl | he | hg := lt_trichotomy x y
  · specialize hf hl
    linarith
  · assumption
  · specialize hf hg
    linarith

/- ## Negation

The negation `¬ A` just means `A → False`,
where `False` is a statement without a proof.
We can use the same tactics as for implication:
`intro` to prove a negation, and `apply` to use one. -/

example {p : Prop} (h : p) : ¬ ¬ p := by
  intro np
  apply np
  assumption

example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by
  constructor
  · intro nx x hp
    apply nx
    exact ⟨x, hp ⟩
  · intro h hn
    obtain ⟨ x , hx ⟩ := hn
    specialize h x
    apply h
    assumption



/- We can use `exfalso` to use the fact that
everything follows from `False`: ex falso quod libet -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by
  intro hp
  exfalso
  apply h
  exact hp



/- `contradiction` proves any goal
when two hypotheses are contradictory. -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by
  intro hp
  contradiction







/-
We can use classical reasoning (with the law of the excluded middle)
using the following tactics.

* `by_contra h` start a proof by contradiction.
* `by_cases h : p` to start a proof by cases on statement `p`.
* `push Not` to push negations inside quantifiers and connectives.
-/

example (p : Prop) (h : ¬ ¬ p) : p := by
  by_contra hnp
  apply h hnp

example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  by_contra h'
  push Not at h'
  have g1 : ¬q := by apply h'.2
  have g2 : p := by apply h'.1
  specialize h g1
  contradiction



example (p r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by
  by_cases h : p
  · specialize h1 h
    assumption
  · specialize h2 h
    assumption

example {α : Type*} {p : α → α → Prop} :
    ¬ (∃ x y, p x y) ↔ ∀ x y, ¬ p x y := by
  push Not
  rfl




/-- The sequence `u` of real numbers converges to `l`.
`∀ ε > 0, ...` means `∀ ε, ε > 0 → ...` -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (u : ℕ → ℝ) (l : ℝ) : ¬ SequentialLimit u l ↔
    ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≥ ε := by
  unfold SequentialLimit
  push Not
  rfl

lemma sequentialLimit_unique (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by
  intro ucl ucl'
  sorry
