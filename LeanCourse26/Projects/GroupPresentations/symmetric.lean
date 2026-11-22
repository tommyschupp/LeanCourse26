import LeanCourse26.Projects.GroupPresentations.int_mod_5
import Mathlib.GroupTheory.Coxeter.Basic    -- Coxeter groups
import Mathlib.LinearAlgebra.Matrix.Notation-- Matrices, needed for defining Coxeter groups
import Mathlib.Data.Finite.Perm             -- Cardinality of S_n
import Mathlib.Algebra.Group.End            -- Symmetric group stuff
import Mathlib.Logic.Equiv.Basic            -- Transpositions represented by swap
import Mathlib.GroupTheory.OrderOfElement   -- Computing order of element
import Mathlib.GroupTheory.Perm.Support     -- Dealing with permutations
import Mathlib.GroupTheory.Perm.Cycle.Type  -- Dealing with three cycles
import Mathlib.Logic.Equiv.Basic            -- More permutation stuff
import Mathlib.Data.Set.Disjoint            -- For disjoint sets stuff
import Mathlib.GroupTheory.Perm.Cycle.Basic -- Helps with transpositions
import Mathlib.Data.Fin.Basic               -- For dealing with Fin
-- import Mathlib.Basic.Logic.Basic            -- For dealing with ¬
import Mathlib.Data.Nat.Factorial.Basic     -- Factorials

import Mathlib.Data.Fintype.Card            -- Just used this for some testing
import Mathlib.Data.Finset.Sort             -- testing

#click_suggestions

open Nat      -- Necessary to use ! insead of Nat.factorial
open Equiv    -- Allows us to use swap instead of Equiv.swap to represent transpositions

-- Fin 5 = {0, 1, 2, 3, 4}
abbrev S₅ : Type := Equiv.Perm (Fin 5)

#eval Fintype.card (Fin 5)
#eval (Finset.univ : Finset (Fin 5))
#check Nat.card_perm


-- Order of S₅ is 5!
lemma S₅_card : Nat.card S₅ = 5! := by
  rw [Nat.card_perm, card_fin]


-- Swaps satisfy first relation of Coxeter group, check below there might be easier way to do
lemma swap_order (a b : (Fin 5)) (h : a ≠ b) : orderOf (swap a b) = 2 := by
  have hs : (swap a b).IsSwap := by
    rw [Perm.swap_isSwap_iff]
    assumption
  exact Perm.IsSwap.orderOf hs
  -- Never delete code!
  -- intro h

  -- apply (orderOf_eq_iff Nat.zero_lt_two).2
  -- constructor
  -- · exact swap_mul_self a b
  -- · intro m hm₁ hm₂
  --   have hm : m = 1 := by
  --     exact Nat.eq_of_le_of_lt_succ hm₂ hm₁
  --   rw [hm, pow_one]
  --   intro hs
  --   rw[swap_eq_one_iff] at hs
  --   contradiction



-- EASIER WAY: swap_order might be more than we need, this should be sufficient for first relation
#check swap_mul_self




-- Maybe would like to remove the a ≠ b and c ≠ d assumptions
lemma disj_swap_comm {a b c d : (Fin 5)} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
  (hbc : b ≠ c) (hbd : b ≠ d) :
  (swap a b) * (swap c d) = (swap c d) * (swap a b) := by
  -- intro h
  apply Perm.Disjoint.commute
  rw [Perm.disjoint_iff_disjoint_support, Perm.support_swap, Perm.support_swap]
  · simp
    constructor
    · constructor
      · rw [← ne_eq]
        exact hac.symm
      · rw [← ne_eq]
        exact hbc.symm
    · constructor
      · rw [← ne_eq]
        exact had.symm
      · rw [← ne_eq]
        exact hbd.symm
  · exact hcd
  · exact hab
  -- unfold Disjoint
  -- intro x hx

  -- apply Perm.disjoint_iff_eq_or_eq.2
  -- intro x
  -- by_cases hx : (swap a b) x = x
  -- · left
  --   assumption
  -- · rw [← ne_eq, swap_apply_ne_self_iff] at hx



-- Swaps satisfy third relation of Coxeter group
lemma disj_swap_ord {a b c d : (Fin 5)} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
  (hbc : b ≠ c) (hbd : b ≠ d) :
  ((swap a b) * (swap c d)) ^ 2 = 1 := by
  -- intro h
  -- obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := h
  rw [sq, mul_assoc, ← mul_assoc (swap c d) (swap a b) (swap c d)]
  rw [disj_swap_comm hcd hab hac.symm hbc.symm had.symm hbd.symm, mul_swap_mul_self,
    swap_mul_self]



-- Swaps satisfy second relation of Coxeter group
lemma adj_swap_ord_neq {a b c : (Fin 5)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
  ((swap a b) * (swap b c)) ^ 3 = 1 := by
  -- have : Perm.support_swap_mul_swap
  -- obtain ⟨hab, hac, hbc⟩ := h
  have h3 : Perm.IsThreeCycle (swap a b * swap b c) := by
    rw [swap_comm]
    exact Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac
  have ho : orderOf ((swap a b) * (swap b c)) = 3 := by
    exact Perm.IsThreeCycle.orderOf h3
  rw [← ho, pow_orderOf_eq_one]



-- These are the minimal assumptions we need for later
lemma adj_swap_ord {a b c : (Fin 5)} (hab : a ≠ b) (hbc : b ≠ c) :
  ((swap a b) * (swap b c)) ^ 3 = 1 := by
  by_cases hac : a = c
  · rw[hac, swap_comm, swap_mul_self]
    simp
  · exact adj_swap_ord_neq hab hac hbc





-- Explicit definition of Coxeter matrix (not proven to be Coxeter in Lean yet)
def M : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 3, 2, 2;
     3, 1, 3, 2;
     2, 3, 1, 3;
     2, 2, 3, 1]


-- Algorithmic definition of Coxeter matrix
-- This can be expanded for arbtirary n, and proving things about it should be easier
-- Matrix.of allows you to construct an n×m matrix from a function (Fin n) × (Fin m) → ℕ.
def C : Matrix (Fin 4) (Fin 4) ℕ :=
  Matrix.of fun i j =>
    if i.val = j.val then 1
    else if i.val + 1 = j.val then 3
    else if i.val = j.val + 1 then 3
    -- else if |(i.val : ℤ) - j.val| = 1 then 3    -- Need to do some funny coercion to subtract
    else 2


-- Here you can check that C is equal to M above
#eval C


-- First requirement for Coxeter matrix
lemma C_is_symm : C.IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  -- simp only [C, Matrix.of_apply]
  -- split_ifs
  by_cases he : i.val = j.val
  · simp [C, he]
  -- · by_cases h1 : |(i.val : ℤ) - j.val| = 1
  --   · simp [C, h1]
  · by_cases h1 : i.val + 1 = j.val
    · simp [C, h1.symm]
    · by_cases h2 : i.val = j.val + 1
      · simp [C, h2]
      · simp [C, he, h1, h2]
        simp [Ne.symm he, Ne.symm h2, Ne.symm h1]
    -- Since C j i has the indices reversed, you need to reverse the direction of the equalities


-- Second requirement
lemma C_diagonal (i : Fin 4) : C i i = 1 := by
  simp[C]


-- Third requirement
lemma C_off_diagonal (i j : Fin 4) : i ≠ j → C i j ≠ 1 := by
  intro h
  have h' : i.val ≠ j.val := by
    exact Fin.val_ne_of_ne h
  simp [C]
  split_ifs
  · constructor
    · assumption
    · simp
  · constructor
    · assumption
    · simp
  · constructor
    · assumption
    · simp

  -- by_contra hc
  -- simp[C] at hc
  -- split_ifs at hc with h1 h2
  -- · have h' : 3 = 1 := by
  --     apply hc
  --     assumption
  --   contradiction
  -- · have h' : 3 = 1 := by
  --     apply hc
  --     assumption
  --   contradiction
  -- ·


-- The Coxeter matrix defining our group
abbrev C₄_matrix : CoxeterMatrix (Fin 4) where
  M := C
  isSymm := C_is_symm
  diagonal := C_diagonal
  off_diagonal := C_off_diagonal


-- The actual Coxeter group C₄ that will be isomorphic to S₅
-- Don't know if "Type" is the right thing to put here
abbrev C₄ : Type := CoxeterMatrix.Group C₄_matrix


-- Coercion from Fin 4 to Fin 5
-- Fin.CastLE converts Fin n to Fin m provided hypothesis that n ≤ m.
abbrev caster : Fin 4 → Fin 5 := fun n ↦ Fin.castLE (by decide) n


-- Used in proof below
lemma caster_helper {a b : Fin 4} (h : a.val + 1 = b.val) : (caster a) + 1 = caster b := by
  ext
  unfold caster
  rw [Fin.val_castLE, Fin.val_add, Fin.val_castLE, Fin.val_one, h]
  simp
  have h' : b.val < 4 := Fin.prop b
  linarith



lemma caster_val (a : Fin 4) : a.val = (caster a).val := rfl






-- Note (caster n) + 1 ≠ caster (n + 1) since addition in Fin n is modular
#eval (caster 3) + 1
#eval caster (3 + 1)


-- A Coxeter group is defined as a presented group generated by Fin n where n is the side length
-- of the Coxeter matrix, so a map out of a Coxeter group should hopefully start with a map out of
-- Fin n. This map sends i ↦ (i, i+1).
abbrev F : Fin 4 → S₅ := fun n ↦ swap (caster n) ((caster n) + 1)


lemma F_resp_rels : ∀ r ∈ C₄_matrix.relationsSet, (FreeGroup.lift F) r = 1 := by
  intro r hr
  rw [show C₄_matrix.relationsSet = Set.range (Function.uncurry C₄_matrix.relation) from rfl,
    Function.uncurry_def,
    show C₄_matrix.relation = fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ C₄_matrix.M i i' from
      rfl] at hr
  simp at hr
  simp [C] at hr
  obtain ⟨a, b, hab⟩ := hr
  -- have h' : FreeGroup.of a = swap (caster a) ((caster a) + 1) := by
  by_cases h1 : a.val = b.val
  · have h' : a = b := by
      exact Fin.eq_of_val_eq h1
    simp [h1] at hab
    rw [← h'] at hab
    rw [← hab, MonoidHom.map_mul, FreeGroup.lift_apply_of,
      show F a = swap (caster a) (caster a + 1) from rfl]
    exact swap_mul_self (caster a) ((caster a) + 1)
  · by_cases h2 : a.val + 1 = b.val
    · simp [h1, h2] at hab        -- Not sure why h1 is necessary here
      rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      unfold F
      rw [caster_helper h2]
      have hab2 : caster a ≠ caster b := by
        unfold caster
        simp
        exact Fin.ne_of_val_ne h1
      have hbb' : caster b ≠ (caster b) + 1 := by
        simp
      exact adj_swap_ord hab2 hbb'
    · by_cases h3 : a.val = b.val + 1
      · simp [h3] at hab        -- whereas here h1 and h2 are not necessary here
        rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
        unfold F
        rw[caster_helper h3.symm, swap_comm, swap_comm (caster b) (caster a)]
        have ha'a : (caster a) + 1 ≠ caster a := by
          simp
        have hab2 : caster a ≠ caster b := by
          simp
          exact Fin.ne_of_val_ne h1
        exact adj_swap_ord ha'a hab2
      · simp[h1, h2, h3] at hab
        rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.lift_apply_of,
          FreeGroup.lift_apply_of]
        unfold F
        have haa' : caster a ≠ (caster a) + 1 := by simp
        have hbb' : caster b ≠ (caster b) + 1 := by simp
        have hab2 : caster a ≠ caster b := by
          simp
          exact Fin.ne_of_val_ne h1
        have ha'b' : (caster a) + 1 ≠ (caster b) + 1 := by
          simp
          exact Fin.ne_of_val_ne h1
        have hab' : caster a ≠ (caster b) + 1 := by
          rw [caster_val a, caster_val b, ← Fin.val_add_one_of_lt] at h3
          exact Fin.ne_of_val_ne h3
          have hb : (caster b).val < 4 := by simp
          exact Fin.castSucc_lt_castSucc_iff.mp hb
        have ha'b : (caster a) + 1 ≠ caster b := by
          rw [caster_val a, caster_val b, ← Fin.val_add_one_of_lt] at h2
          exact Fin.ne_of_val_ne h2
          have ha : (caster a).val < 4 := by simp
          exact Fin.castSucc_lt_castSucc_iff.mp ha
        exact disj_swap_ord haa' hbb' hab2 hab' ha'b ha'b'

      -- have hab' : caster a ≠ (caster b) + 1 := by
      --   rw [caster_val a, caster_val b] at h2

      -- have hc : (caster a) + 1 = caster b := by

      --   apply Nat.eq_sub_of_add_eq at h2

        -- rw[Fin.val_eq_val] at h2



-- The map C₄ → S₅ that will be our isomorphism
abbrev Phi : C₄ →* S₅ := PresentedGroup.toGroup F_resp_rels
