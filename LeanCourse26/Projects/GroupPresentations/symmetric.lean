import LeanCourse26.Projects.GroupPresentations.int_mod_5
import Mathlib.GroupTheory.Coxeter.Basic    -- Coxeter groups
import Mathlib.Data.Finite.Perm             -- Cardinality of S_n
import Mathlib.Algebra.Group.End            -- Symmetric group stuff
import Mathlib.Logic.Equiv.Basic            -- Transpositions represented by swap
import Mathlib.GroupTheory.OrderOfElement   -- Computing order of element
import Mathlib.GroupTheory.Perm.Support     -- Dealing with permutations
import Mathlib.GroupTheory.Perm.Cycle.Type  -- Dealing with three cycles
import Mathlib.Logic.Equiv.Basic            -- More permutation stuff
import Mathlib.Data.Set.Disjoint            -- For disjoint sets stuff
import Mathlib.GroupTheory.Perm.Cycle.Basic -- Helps with transpositions
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




-- The statement and proof are garbo but it's a start
lemma disj_swap_comm (a b c d : (Fin 5)) (h : a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
  (swap a b) * (swap c d) = (swap c d) * (swap a b) := by
  -- intro h
  apply Perm.Disjoint.commute
  rw [Perm.disjoint_iff_disjoint_support, Perm.support_swap, Perm.support_swap]
  · simp
    constructor
    · constructor
      · rw [← ne_eq]
        exact h.2.2.1.symm
      · rw [← ne_eq]
        exact h.2.2.2.2.1.symm
    · constructor
      · rw [← ne_eq]
        exact h.2.2.2.1.symm
      · rw [← ne_eq]
        exact h.2.2.2.2.2.symm
  · exact h.2.1
  · exact h.1
  -- Never delete code!
  -- unfold Disjoint
  -- intro x hx

  -- apply Perm.disjoint_iff_eq_or_eq.2
  -- intro x
  -- by_cases hx : (swap a b) x = x
  -- · left
  --   assumption
  -- · rw [← ne_eq, swap_apply_ne_self_iff] at hx



-- Swaps satisfy third relation of Coxeter group
lemma disj_swap_ord (a b c d : (Fin 5)) (h : a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
  ((swap a b) * (swap c d)) ^ 2 = 1 := by
  -- intro h
  obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := h
  rw [sq, mul_assoc, ← mul_assoc (swap c d) (swap a b) (swap c d)]
  rw [disj_swap_comm c d a b ⟨hcd, hab, hac.symm, hbc.symm, had.symm, hbd.symm⟩, mul_swap_mul_self,
    swap_mul_self]



-- Swaps satisfy second relation of Coxeter group
lemma adj_swap_ord (a b c : (Fin 5)) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c): ((swap a b) * (swap b c)) ^ 3 = 1
  := by
  -- have : Perm.support_swap_mul_swap
  obtain ⟨hab, hac, hbc⟩ := h
  have h3 : Perm.IsThreeCycle (swap a b * swap b c) := by
    rw [swap_comm]
    exact Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac
  have ho : orderOf ((swap a b) * (swap b c)) = 3 := by
    exact Perm.IsThreeCycle.orderOf h3
  rw [← ho, pow_orderOf_eq_one]
