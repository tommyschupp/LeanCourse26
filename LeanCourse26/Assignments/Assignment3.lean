-- Name: <insert your name here>

module

public import Mathlib.Analysis.Complex.Exponential

open Real Function Set Nat

#click_suggestions

/-

* Hand in the solutions to the exercises below. Deadline: 4.11.2025 before class.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

section calculations

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  sorry

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  sorry

end calculations

section Min
open LE
variable (a b c d : ℝ)

/- Recall the following properties of the `≤` relation -/
#check (le : ℝ → ℝ → Prop)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)

/- The following theorems characterize `min`.
Let's use this characterization of it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- Note: the tactic `order` proves both of these immediately
-- For practice, prove them "by hand"
lemma exercise_min_comm : min a b = min b a := by
  sorry

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by
  sorry

-- Prove the following exercise. You can use mathlib tactics now.
lemma exercise_min : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  sorry

end Min

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by
  sorry


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example (p : Prop) : p ∨ ¬ p := by
  sorry

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (132 + 32 * 3, (x + y) ^ 2) = (228, x ^ 2 + 2 * x * y + y ^ 2) := by
  sorry

/- Prove a version of the axiom of choice Lean's `Classical.choose`.

Note: this might be a bit harder; you will probably find `Classical.choose` and
`Classical.choose_spec` useful. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by
  sorry

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
  sorry

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
  sorry

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by
  sorry

/- Prove this without using lemmas from Mathlib -/
example {f : α → β} (h : Injective f) : Injective (image f) := by
  sorry

end Set


/-! # Exercises to hand-in. -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext x
  constructor
  · intro hx
    simp
    obtain ⟨hx1, hx2 ⟩ := hx
    simp at hx1
    obtain ⟨x_1, hx_1⟩ := hx1
    use x_1
    constructor
    · constructor
      · apply hx_1.1
      · grw[← hx_1.2] at hx2
        assumption
    · apply hx_1.2
  · intro hx
    simp
    simp at hx
    obtain ⟨x_1, hx_1⟩ := hx
    have p1 : x_1 ∈ s := by apply hx_1.1.1
    have p2 : f x_1 = x := by apply hx_1.2
    constructor
    · use x_1
    · have p3 : f x_1 ∈ t := by apply hx_1.1.2
      grw[p2] at p3
      assumption


/- Prove this without using lemmas from Mathlib. -/
-- Note: we still use the `simp` tactic... which is using mathlib, but only in a mild way.
-- That's a reasonable compromise for now.
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  · intro hx
    simp
    simp at hx
    obtain ⟨x_1, hx_1, hx_2⟩ := hx
    obtain ⟨i, hi⟩ := hx_1
    use i, x_1
  · intro hx
    simp
    simp at hx
    obtain ⟨i, x_1, hx_2, hx_3⟩ := hx
    use x_1
    constructor
    · use i
    · assumption

/- Prove this without using lemmas from Mathlib. -/
example {a b c d : ℝ} (hab : a < b) : Icc a b ⊆ Ioo c d ↔ c < a ∧ b < d := by
  unfold Icc Ioo
  constructor
  · intro hI
    simp at hI
    have key1 : a ≤ a := by linarith
    have key2 : a ≤ b := by linarith
    have key3 : b ≤ b := by linarith
    have hI2 := hI
    specialize hI a key1 key2
    specialize hI2 b key2 key3
    constructor
    · exact hI.1
    · exact hI2.2
  · intro hI x hx
    simp
    simp at hx
    constructor
    · calc
      c < a := by apply hI.1
      _ ≤ x := by apply hx.1
    · calc
      x ≤ b := by apply hx.2
      _ < d := by apply hI.2








/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  ext x
  simp
  have key : √16 = 4 := by rw [sqrt_eq_iff_mul_self_eq_of_pos]
                           norm_num
                           apply zero_lt_four'
  constructor
  · intro hx
    apply Real.sqrt_le_sqrt at hx
    grw[key] at hx
    rw [sqrt_sq_eq_abs] at hx
    exact le_abs'.mp hx
  · intro hx
    rw [← le_abs'] at hx
    grw[← key] at hx
    rwa [sqrt_le_left, sq_abs] at hx
    apply abs_nonneg



section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
    unfold SurjectiveFunction
    simp
    unfold SurjectiveFunction at hf
    constructor
    · intro hgf z
      specialize hgf z
      obtain ⟨x, hx⟩ := hgf
      use f x
    · intro hg y
      specialize hg y
      obtain ⟨z, hz⟩ := hg
      specialize hf z
      obtain ⟨x, hx⟩ := hf
      use x
      rw[← hx] at hz
      exact hz




/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  unfold SurjectiveFunction at hf
  unfold SurjectiveFunction
  intro y
  let w := (y-1)/2
  specialize hf w
  obtain ⟨u, hu⟩ := hf
  let v := (u/3) - 4
  use v
  simp
  have key1 : 3 * (v + 4) = u := by rw [sub_add_cancel, mul_div_cancel₀]
                                    apply three_ne_zero'
  rw[key1]
  rw [hu, mul_div_cancel₀, sub_add_cancel]
  exact two_ne_zero




/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  unfold Surjective
  intro hb
  let R := {x | x ∉ f x}
  specialize hb R
  obtain ⟨a, ha⟩ := hb
  by_cases key1 : a ∈ R
  · have imd1 : a ∉ f a := by apply key1
    have key2 : a ∉ R := by rw[ha] at imd1
                            apply imd1
    contradiction
  · have key2 := key1
    rw[← ha] at key2
    rw [notMem_ofPred_iff] at key1
    contradiction
end Surjectivity
