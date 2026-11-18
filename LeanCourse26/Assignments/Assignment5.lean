-- Name: <insert your name here>

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Function Set

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: **Wednesday**, 18.11.2025 at 16.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

-- Remember the definition Point from last week's assignment: let's parametrise this by a type.
@[ext]
structure Point (α : Type*) where
  x : α
  y : α
  z : α

-- Let's connect this to ℝ³ (i.e. Fin 3 → ℝ).
-- You can use pattern matching to define an element of ℝ³,
-- just like you would for an inductive type.
example {x y z : ℝ} : Fin 3 → ℝ := fun
  | 0 => x
  | 1 => y
  | 2 => z

-- Now prove that Point α and α³ are equivalent.
-- In particular, `Point` from last week and `ℝ³` are equivalent.
example {α : Type*} : (Fin 3 → α) ≃ Point α where
  toFun := fun f ↦ ⟨f 0, f 2, f 1⟩
  invFun P := fun
    | 0 => P.x
    | 1 => P.z
    | 2 => P.y
  left_inv := by
    sorry
  right_inv := by
    sorry

-- Define an equivalence from Fin 2 × Fin 3 to Fin 6.
-- Hint: the tactic `fin_cases x` is useful for variables
-- of the form `x : Fin n`
example : Fin 3 × Fin 2 ≃ Fin 6 :=
  sorry



section EquivalenceRelation

-- Prove that the following defines an equivalence relation.
def integerEquivalenceRelation : Setoid (ℤ × ℤ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = l + m
  iseqv :=
    sorry

/- This simp-lemma will simplify `x ≈ y` in the lemma below. -/
@[simp] lemma integerEquivalenceRelation'_iff (a b : ℤ × ℤ) :
  letI := integerEquivalenceRelation; a ≈ b ↔ a.1 + b.2 = a.2 + b.1 := by rfl

example : Quotient integerEquivalenceRelation ≃ ℤ :=
  sorry

end EquivalenceRelation

section choice

/-- This exercise is about a subtle detail regarding the axiom of choice: while you know there
is a global choice function, it is not given by one "computation rule".
The following exercise makes this precise: prove it.

The key to this exercise is *proof irrelevance*: in Lean, any two proofs
of the same proposition are definitionally equal.
-/
example (choiceFunction : ∀ (α : Type) (p : α → Prop) (_h : ∃ x, p x), α)
    (h : ∀ (α : Type) (p : α → Prop) (x : α) (hx : p x), choiceFunction α p ⟨x, hx⟩ = x) :
    False := by
  sorry


end choice

section


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/

lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by
  sorry
-- In the lecture, we also saw injectivity and bijectivity of functions.
-- There is another variant, "bijectivity on a set":
def BijectiveOn {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (f '' s ⊆ t) ∧ InjOn f s ∧ SurjOn f s t

-- There is a curious fact about infinite types: they are bijective to a proper subset.
-- Let us explore this theme in the following exercises.

example : ∃ f : ℕ → ℕ, BijectiveOn f univ (univ \ {0}) := by
  sorry

example {α : Type*} [Infinite α] {a : α} : ∃ f : α → α, BijectiveOn f (univ \ {a}) univ := by
  -- Hint: a useful first step is "there exists an injective map ℕ → α".
  -- Use loogle or exact? to find this.
  sorry

-- In particular, an infinite type is bijective to a proper subtype.
-- If you like a little *challenge*, prove the converse.
-- This is a bit harder; you want to write down a careful mathematical proof first
-- and use loogle to re-use existing results from mathlib.
example {α : Type*} {s : Set α} (hs : s ≠ univ) {f : α → α} (hf : BijectiveOn f s univ) :
    Infinite α := by
  sorry

end



/-! # Exercises to hand-in. -/


noncomputable section choice

variable {α β γ : Type} {f : α → γ} {g : β → γ}

/- In mathematics, we often identify two sets by realizing them as the
same subset of some larger set. Construct, using the axiom of choice,
such an equivalence.
Hint: it might be useful to define auxilliary functions and lemmas that
can be used in the main proof body
-/

lemma helper_alpha (H : range f = range g) (a : α) : ∃ b : β , g b = f a := by
  rw [← mem_range, ← H]
  apply mem_range_self

lemma helper_beta (H : range f = range g) (b : β) : ∃ a : α , f a = g b := by
  rw [← mem_range, H]
  apply mem_range_self

def inverse_f (b : β) (h : ∃ a : α , f a = g b ) : α :=
  Classical.choose h

def inverse_g  (a : α) (h : ∃ b : β , g b = f a) : β :=
  Classical.choose h

-- I used AI to help me with proving h2, as I couldn't do it

lemma left_inv_helper (hf : Injective f) (a : α) (h : ∃ b : β , g b = f a) :
  inverse_f (inverse_g a h) ⟨a, (Classical.choose_spec h).symm⟩ = a := by
  apply hf
  have h1 : g (inverse_g a h) = f a := Classical.choose_spec h
  have h2 : f (inverse_f (inverse_g a h) ⟨a, (Classical.choose_spec h).symm⟩) = g (inverse_g a h)
  := by
    exact Classical.choose_spec
      (⟨a, (Classical.choose_spec h).symm⟩ :
        ∃ x : α, f x = g (inverse_g a h))
  rw [h2]
  exact h1

lemma right_inv_helper (hg : Injective g) (b : β) (h : ∃ a : α , f a = g b) :
  inverse_g (inverse_f b h) ⟨b, (Classical.choose_spec h).symm⟩ = b := by
  apply hg
  have h1 : f (inverse_f b h) = g b := Classical.choose_spec h
  have h2 : g (inverse_g (inverse_f b h) ⟨b, (Classical.choose_spec h).symm⟩) = f (inverse_f b h)
  := by
    exact Classical.choose_spec
      (⟨b, (Classical.choose_spec h).symm⟩ :
        ∃ x : β, g x = f (inverse_f b h))
  rw [h2]
  exact h1

lemma left_inv (hf : Injective f) (H : range f = range g) :
  LeftInverse (fun b => inverse_f b (helper_beta H b)) (fun a => inverse_g a (helper_alpha H a))
  := by
  rw [leftInverse_iff_comp]
  ext a
  simp
  apply left_inv_helper hf

lemma right_inv (hg : Injective g) (H : range f = range g) :
  RightInverse (fun b => inverse_f b (helper_beta H b)) (fun a => inverse_g a (helper_alpha H a))
  := by
  rw [rightInverse_iff_comp]
  ext b
  simp
  apply right_inv_helper hg

example (hf : Injective f) (hg : Injective g) (H : range f = range g) : α ≃ β where
  toFun := fun a => inverse_g a (helper_alpha H a)
  invFun := fun b => inverse_f b (helper_beta H b)
  left_inv := left_inv hf H
  right_inv := right_inv hg H


end choice


section Subtypes

/-- Let's prove that the positive rationals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use `apply` to use the lemmas about real numbers. -/

abbrev PosRat : Type := {x : ℚ // 0 < x}

def PosRatInv (a : PosRat) : PosRat :=
  let ⟨a', h⟩ := a
  let ainv := (1/a')
  have h1 : 0 < ainv := by rw [one_div_pos]; exact h
  ⟨ainv, h1⟩

instance groupPosRat : Group PosRat where
  one := 1
  mul := fun a b => a * b
  mul_assoc := by {
    intro a b c
    apply mul_assoc
  }
  one_mul := by {
    intro a
    simp
  }
  mul_one := by {
    intro a
    simp
  }
  npow_zero := by simp
  npow_succ := by {
    intro x y
    apply Monoid.npow_succ
  }
  inv := fun a => PosRatInv a
  div_eq_mul_inv := by {
    exact fun a b ↦ Subtype.ext rfl
  }
  zpow_zero' := by {
    exact fun a ↦ Eq.symm (Subtype.ext rfl)
  }
  zpow_succ' := by {
    exact fun n a ↦ Eq.symm (Subtype.ext rfl)
  }
  zpow_neg' := by {
    exact fun n a ↦ Subtype.ext rfl
  }
  inv_mul_cancel := by {
    intro a
    unfold PosRatInv
    ext
    rw [Positive.val_mul, Subtype.coe_mk, Rat.div_mul_cancel]
    simp
    apply Subtype.prop at a
    exact Rat.ne_of_gt a
  }



end Subtypes


section cardinality

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
#check Finset.induction
open Classical

lemma disjointness (α : Type*) (s : Finset α) (x : α) (hxs : x ∉ s) :
  s.powerset ∩ Finset.image (insert x) s.powerset = ∅ := by
  ext u
  rw [Finset.mem_inter, Finset.mem_powerset, Finset.mem_image]
  simp_rw [Finset.insert_eq]
  rw [← exists_and_left]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx
    rw [Finset.mem_powerset] at hy
    have h1 : u ⊆ s := by apply hy.1
    have h2 : {x} ∪ y = u := by apply hy.2.2
    rw[←h2] at h1
    simp
    have h3 : x ∈ s := by
      apply Finset.union_subset_left at h1; rw [Finset.singleton_subset_iff] at h1; exact h1
    contradiction
  · simp


lemma injectivity (α : Type*) (s : Finset α) (x : α) (hxs : x ∉ s) :
  InjOn (insert x) (↑s.powerset : Set (Finset α)) := by
  intro t ht p hp htp
  rw [Finset.mem_coe] at ht hp
  rw [Finset.mem_powerset] at ht hp
  have h1 : x ∉ t := by exact Finset.not_mem_subset ht hxs
  have h2 : x ∉ p := by exact Finset.not_mem_subset hp hxs
  rw [← Finset.union_singleton] at htp
  rw [← Finset.union_singleton] at htp
  ext a
  constructor
  · intro ha
    have h3 : a ≠ x := by exact ne_of_mem_of_not_mem (ht ha) hxs
    have h4 : a ∈ p ∪ {x} := by rw [← htp]; exact Finset.mem_union_left {x} ha
    rw [Finset.mem_union, or_iff_not_imp_right, Finset.notMem_singleton] at h4
    specialize h4 h3
    exact h4
  · intro ha
    have h3 : a ≠ x := by exact ne_of_mem_of_not_mem (hp ha) hxs
    have h4 : a ∈ t ∪ {x} := by rw [htp]; exact Finset.mem_union_left {x} ha
    rw [Finset.mem_union, or_iff_not_imp_right, Finset.notMem_singleton] at h4
    specialize h4 h3
    exact h4










lemma finset_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (Finset.powerset s) = 2 ^ Finset.card s := by
  induction s using Finset.induction with
  | empty => rw [Finset.card_powerset]
  | @insert x s hxs ih =>
    have disjointness : s.powerset ∩ Finset.image (insert x) s.powerset = ∅ :=
      by apply disjointness; exact hxs
    rw [Finset.powerset_insert, Finset.card_union, disjointness, Finset.card_empty]
    simp
    rw [ih, Finset.card_insert_of_notMem hxs, Nat.two_pow_succ, Nat.add_right_inj,
    Finset.card_image_of_injOn]
    exact ih
    have injectivity : InjOn (insert x) (↑s.powerset : Set (Finset α)) :=
      by apply injectivity; exact hxs
    exact injectivity


end cardinality
