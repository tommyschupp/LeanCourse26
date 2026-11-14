-- Name: <insert your name here>
import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: 28.10.2025 at 16:00.
* Solutions from the section `Exercises to hand-in` will receive feedback
  from the tutors.
* None of your solutions should be LLM-generated: doing so will only rob you
  of the practice and waste the tutors' time.
* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  intro hq
  constructor
  · apply h
    constructor
    apply hp
    apply hq
  · specialize h' hq
    assumption


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
  intro hx
  obtain ⟨x₀ , hx₀ ⟩ := hx
  specialize h x₀ hx₀
  exact ⟨x₀, h ⟩

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  intro h
  linarith

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  constructor
  · intro hxr hx hpx
    specialize hxr ⟨hx, hpx⟩
    assumption
  · intro hax hx
    obtain ⟨x₀ , hx₀ ⟩ := hx
    specialize hax x₀ hx₀
    assumption




/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  constructor
  · intro hx
    constructor
    · obtain ⟨y , hy ⟩ := hx
      exact ⟨y, hy.1⟩
    · obtain ⟨y , hy ⟩ := hx
      exact hy.2
  · intro hx
    obtain ⟨y , hr ⟩ := hx
    obtain ⟨z, hz ⟩ := y
    use z

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  constructor
  · intro hx hnx
    obtain ⟨y, hy ⟩ := hx
    specialize hnx y
    contradiction
  · contrapose
    intro nx y hz
    apply nx
    use y












def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun _ : ℕ ↦ a) a := by
  unfold SequentialLimit
  intro ε hε
  use 0
  intro n hn
  have key := calc
    |(fun x ↦ a) n - a| = |a - a| := by rfl
    _ = |0| := by rw[sub_self]
    _ = 0 := by exact abs_zero
    _ < ε := by apply hε
  assumption




/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  have h' : n ≤ m+1 := by exact le_add_right_of_le h
  exact factorial_dvd_factorial h'


example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by
  have h' : exp x ≤ exp y := by exact exp_le_exp.mpr h3
  have h'' : y ≤ y + 2 := by linarith
  have h''' : rexp y ≤ rexp (y + 2) := by exact exp_le_exp.mpr h''
  calc
  a + rexp x ≤ b + rexp x := by linarith
            _ ≤ c + rexp x := by linarith
            _ ≤ c + rexp y := by linarith
            _ ≤ c + rexp (y + 2) := by exact (add_le_add_iff_left c).mpr h'''



-- Use `rw?` or `#click_suggestions` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
#click_suggestions

example {G : Type*} [Group G] {a b c : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * a = a * b) : b = 1 := by
    rw [mul_assoc (a⁻¹ * b) c c⁻¹, mul_inv_cancel] at h
    rw [mul_assoc a⁻¹ b 1, mul_one, mul_inv_cancel_right, mul_assoc a⁻¹ b a] at h
    sorry







/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  sorry


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  sorry

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  sorry



/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from Mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  constructor
  · intro hf x
    specialize hfg x
    specialize hf x
    apply hfg.1 hf
  · intro hg x
    specialize hfg x
    specialize hg x
    apply hfg.2 hg


def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  constructor
  · intro hp x
    specialize h x
    specialize hp x
    apply h.1 hp
  · intro hq x
    specialize h x
    specialize hq x
    apply h.2 hq

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
  constructor
  · intro hx
    obtain ⟨x₀ , px₀ ⟩ := hx
    specialize h x₀
    use x₀
    exact h.1 px₀
  · intro hx
    obtain ⟨x₀ , px₀ ⟩ := hx
    specialize h x₀
    use x₀
    exact h.2 px₀



-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)

--Not sure how to provide a counter example. An example of such p and q are p is x = 1 and q is x = 0.
example (p q : ℕ → Prop) (h: (∃ x, p x) ↔ (∃ x, q x)) : ¬ (∀ x, p x ↔ q x) := by
  sorry



/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro hx
    obtain ⟨x₀, hx₀⟩ := hx
    obtain hp | hq := hx₀
    · left
      use x₀
    · right
      use x₀
  · intro ho
    obtain hp | hq := ho
    · obtain ⟨x₀ , hx₀⟩ := hp
      use x₀
      left
      assumption
    · obtain ⟨x₀, hx₀ ⟩ := hq
      use x₀
      right
      assumption



end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in Mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet:
-- this is related to implicit arguments.
-- You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `#click_suggestions` to find this theorem in Mathlib.
-- Describe what you are doing.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  exact ZMod.pow_card x

-- The above theorem has a name. What is it?
--Fermat's little theorem.
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.

-- We go to the definition of `ZMod.pow_card`: hover over the theorem,
-- right-click and select "Go to definition".
-- This opens the Mathlib file where this theorem is proven. The theorem's doc-string says
-- "/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/".
-- This is the name of the theorem: Fermat's little theorem.

-- We open leansearch.net, type "Fermat's little theorem" as a query and press search.
-- The fourth result we get is `ZMod.pow_card x`, with the description
-- "Fermat's Little Theorem in Z/pZ: x^p=x"


-- Use `exact?` to find the following theorem in Mathlib.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  exact ZMod.pow_card_sub_one_eq_one hk

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun x ↦ x ^ p + 2 * x ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun x ↦ 3 * x) := by
  ext x
  by_cases hx : x = 0
  · rw [hx, ZMod.pow_card, pow_succ, Semiring.mul_zero, Semiring.mul_zero 3]
    ring
  · rw [ZMod.pow_card, Nat.mul_sub_one, ← Nat.mul_sub_one, _root_.pow_succ', pow_mul',
      ZMod.pow_card_sub_one_eq_one hx]
    ring


-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  by_cases hx : k = 0
  · rw[hx]
    ring
  · rw [_root_.pow_succ', pow_mul', ZMod.pow_card_sub_one_eq_one hx]
    ring



example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  by_cases hx : k = 0
  · rw[hx]
    ring
  · rw [_root_.pow_succ', pow_mul', ZMod.pow_card_sub_one_eq_one hx]
    ring

end Functions


/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  unfold SequentialLimit
  intro ε hε
  have he2 : ε /2 > 0 := by linarith
  let e := ε / 2
  specialize hs e he2
  specialize ht e he2
  obtain ⟨Nₛ, hNₛ ⟩:= hs
  obtain ⟨Nₜ , hNₜ ⟩ := ht
  let N₀ := max Nₛ Nₜ
  use N₀
  intro n hn
  have nbs : n ≥ Nₛ := by exact le_of_max_le_left hn
  have nbt : n ≥ Nₜ := by exact le_of_max_le_right hn
  specialize hNₛ n nbs
  specialize hNₜ n nbt
  have key := calc
    |(fun n ↦ s n + t n) n - (a + b)| = |s n + t n - (a + b)| := by rfl
    _ = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := by exact abs_add_le (s n - a) (t n - b)
    _ < e + e := by linarith
    _ = ε := by ring
  assumption

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  by_cases hc : c = 0
  · unfold SequentialLimit
    rw[hc]
    simp_rw [Semiring.zero_mul]
    rw [sub_self, abs_zero]
    intro ε hε
    use 0
    intro nx hnx
    assumption
  · intro ε hε
    have h' : |c| > 0 := by exact abs_pos.mpr hc
    have hec : ε / |c| > 0 := by exact _root_.div_pos hε h'
    specialize hs (ε / |c|) hec
    obtain ⟨Ns, hNs⟩ := hs
    use Ns
    intro n hn
    specialize hNs n hn
    have key := calc
      |(fun n ↦ c * s n) n - c * a| = |c * s n - c * a| := by rfl
      _ = |c * (s n - a)| := by rw [← mul_sub]
      _ = |c| * |s n - a| := by rw [abs_mul]
      _ < |c| * (ε / |c|) := by grw [hNs]
      _ = ε := by rw [mul_div_cancel₀]
                  exact ne_of_gt h'
    assumption



/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  have mg0 : m ^ 2 ≥ 0 := by exact Int.sq_nonneg m
  have hn : n ≤ 2 := by linarith
  have hk : k ^ 2 ≥ 0 := by exact Int.sq_nonneg k
  calc
    n + 1 ≤ 3 := by linarith
    _ ≤ 3 + k ^ 2 := by linarith

section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  simp
  exact Nat.mul_le_mul_right (s n) hn


/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  specialize h₁ k
  specialize h₂ k
  obtain ⟨ N1, hN1 ⟩ := h₁
  obtain ⟨ N2, hN2 ⟩ := h₂
  let N := max N1 N2
  use N
  intro n hn
  have nb1 : n ≥ N1 := by exact le_of_max_le_left hn
  have nb2 : n ≥ N2 := by exact le_of_max_le_right hn
  specialize hN1 n nb1
  specialize hN2 n nb2
  calc
    k * (t₁ + t₂) n = k * (t₁ n + t₂ n) := by simp
                  _ = k * t₁ n + k * t₂ n := by linarith
                  _ ≤ s₁ n + s₂ n := by linarith


/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  let S := fun n : ℕ ↦ (n)!
  use S
  constructor
  rotate_left
  · intro x
    exact factorial_ne_zero x
  · intro k
    use k
    intro n hn
    simp
    unfold S
    have hk : k ≤ n+1 := by linarith
    calc
      k * n ! ≤ (n+1) * (n)! := by exact Nat.mul_le_mul_right n ! hk
            _ = (n + 1)! := by exact Eq.symm (factorial_succ n)




end Growth
