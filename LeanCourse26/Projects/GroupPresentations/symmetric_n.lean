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


-- I didn't realize, not all of these imports are necessary, should go through and see which ones
-- break it and which ones can be removed.


#click_suggestions

open Nat      -- Necessary to use ! insead of Nat.factorial
open Equiv    -- Allows us to use swap instead of Equiv.swap to represent transpositions


abbrev Sₙ (n : ℕ) : Type := Equiv.Perm (Fin n)

-- Order of S₅ is 5!
lemma Sₙ_card (n : ℕ) : Nat.card (Sₙ n) = n ! := by
  rw [Nat.card_perm, card_fin]


-- Swaps satisfy first relation of Coxeter group, check below there might be easier way to do
lemma swap_order (n : ℕ) (a b : (Fin n)) (h : a ≠ b) : orderOf (swap a b) = 2 := by
  have hs : (swap a b).IsSwap := by
    rwa [Perm.swap_isSwap_iff]
  exact Perm.IsSwap.orderOf hs

-- Maybe would like to remove the a ≠ b and c ≠ d assumptions
lemma disj_swap_comm (n : ℕ) {a b c d : (Fin n)}
  (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
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


-- Swaps satisfy third relation of Coxeter group
lemma disj_swap_ord (n : ℕ) {a b c d : (Fin n)}
  (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
  (hbc : b ≠ c) (hbd : b ≠ d) :
  ((swap a b) * (swap c d)) ^ 2 = 1 := by
  -- intro h
  -- obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := h
  rw [sq, mul_assoc, ← mul_assoc (swap c d) (swap a b) (swap c d)]
  rw [(disj_swap_comm n) hcd hab hac.symm hbc.symm had.symm hbd.symm, mul_swap_mul_self,
    swap_mul_self]



-- Swaps satisfy second relation of Coxeter group
lemma adj_swap_ord_neq (n : ℕ) {a b c : (Fin n)}
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
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
lemma adj_swap_ord (n : ℕ) {a b c : (Fin n)}
  (hab : a ≠ b) (hbc : b ≠ c) :
  ((swap a b) * (swap b c)) ^ 3 = 1 := by
  by_cases hac : a = c
  · rw[hac, swap_comm, swap_mul_self]
    simp
  · exact adj_swap_ord_neq n hab hac hbc



-- Algorithmic definition of Coxeter matrix
-- This can be expanded for arbtirary n, and proving things about it should be easier
-- Matrix.of allows you to construct an n×m matrix from a function (Fin n) × (Fin m) → ℕ.
def C (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j =>
    if i.val = j.val then 1
    else if i.val + 1 = j.val then 3
    else if i.val = j.val + 1 then 3
    else 2

-- First requirement for Coxeter matrix
lemma C_is_symm (n : ℕ) : (C n).IsSymm := by
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
lemma C_diagonal (n : ℕ) (i : Fin n) : C n i i = 1 := by
  simp[C]


-- Third requirement
lemma C_off_diagonal (n : ℕ) (i j : Fin n) : i ≠ j → C n i j ≠ 1 := by
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



-- The Coxeter matrix defining our group
abbrev Cₙ_matrix (n : ℕ) : CoxeterMatrix (Fin n) where
  M := C n
  isSymm := C_is_symm n
  diagonal := C_diagonal n
  off_diagonal := C_off_diagonal n


abbrev Cₙ (n : ℕ): Type := CoxeterMatrix.Group (Cₙ_matrix n)

-- Fin.CastLE converts Fin n to Fin m provided hypothesis that n ≤ m.
abbrev caster (n : ℕ) : Fin n → Fin (n + 1) := fun m ↦ Fin.castLE (by simp) m


lemma caster_val (n : ℕ) (a : Fin n) : a.val = (caster n a).val := rfl


-- Used in proof below
lemma caster_helper (n : ℕ) {a b : Fin n}
  (ha : a.val + 1 = b.val) :
    Fin.succ (a) = caster n b := by
  ext
  -- unfold caster
  rw [← caster_val n]
  simp
  rw[ha]


-- A Coxeter group is defined as a presented group generated by Fin n where n is the side length
-- of the Coxeter matrix, so a map out of a Coxeter group should hopefully start with a map out of
-- Fin n. This map sends i ↦ (i, i+1).

--It's so unfortunate that we have to define this using n - 1, because
--it demands we pass in n > 0, but we would need to do that
--eventually anyway.

lemma hn_helper (n : ℕ) (hn : n > 0) : n - 1 + 1 = n := by omega

abbrev F (n : ℕ) (hn : n > 0) : Fin (n - 1) → Sₙ n :=
  fun m ↦
    swap
      (Fin.cast (hn_helper n hn) (caster (n - 1) m))
      (Fin.cast (hn_helper n hn) (Fin.succ m))


lemma F_resp_rels (n : ℕ) (hn : n > 0) :
  ∀ r ∈ (Cₙ_matrix (n - 1)).relationsSet, (FreeGroup.lift (F n hn)) r = 1 := by
  intro r hr
  rw [show (Cₙ_matrix (n - 1)).relationsSet =
    Set.range (Function.uncurry (Cₙ_matrix (n - 1)).relation) from rfl,
    Function.uncurry_def,
    show (Cₙ_matrix (n - 1)).relation =
     fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (Cₙ_matrix (n - 1)).M i i' from rfl]
    at hr
  simp at hr
  simp [C] at hr
  obtain ⟨a, b, hab⟩ := hr
  let casted_a := Fin.cast (hn_helper n hn) (caster (n - 1) a)
  let casted_b := Fin.cast (hn_helper n hn) (caster (n - 1) b)
  let casted_a_plus_1 := Fin.cast (hn_helper n hn) (Fin.succ a)
  let casted_b_plus_1 := Fin.cast (hn_helper n hn) (Fin.succ b)
  by_cases h1 : a.val = b.val
  · have h' : a = b := by
      exact Fin.eq_of_val_eq h1
    simp [h1] at hab
    rw [← h'] at hab
    rw [← hab, MonoidHom.map_mul, FreeGroup.lift_apply_of,
      show F n hn a = swap
        casted_a
        casted_a_plus_1
        from rfl]
    exact swap_mul_self casted_a casted_a_plus_1
  · by_cases h2 : a.val + 1 = b.val
    · simp [h1, h2] at hab        -- Not sure why h1 is necessary here
      rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      unfold F
      rw [caster_helper (n - 1) h2]
      have hab2 : casted_a ≠ casted_b := by
        unfold casted_a casted_b
        simp
        exact Fin.ne_of_val_ne h1
      have hbb' : casted_b ≠  casted_b_plus_1 := by
        apply caster_helper at h2
        unfold casted_b casted_b_plus_1
        rw[←h2]
        simp
        apply Fin.ne_of_val_ne at h1
        exact h1
      exact adj_swap_ord n hab2 hbb'
    · by_cases h3 : a.val = b.val + 1
      · simp [h3] at hab        -- whereas here h1 and h2 are not necessary here
        rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
        unfold F
        rw[caster_helper (n - 1) h3.symm, swap_comm, swap_comm casted_b casted_a]
        have ha'a : casted_a_plus_1 ≠ casted_a := by
          unfold casted_a_plus_1 casted_a
          rw [Fin.ne_iff_vne]
          simp
        have hab2 : casted_a ≠ casted_b := by
          simp
          exact Fin.ne_of_val_ne h1
        exact adj_swap_ord n ha'a hab2
      · simp[h1, h2, h3] at hab
        rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.lift_apply_of,
          FreeGroup.lift_apply_of]
        unfold F
        have haa' : casted_a ≠ casted_a_plus_1 :=
          by unfold casted_a casted_a_plus_1; rw [Fin.ne_iff_vne]; simp
        have hbb' : casted_b ≠ casted_b_plus_1 :=
          by unfold casted_b casted_b_plus_1; rw[Fin.ne_iff_vne]; simp
        have hab2 : casted_a ≠ casted_b := by
          simp
          exact Fin.ne_of_val_ne h1
        have ha'b' : casted_a_plus_1 ≠ casted_b_plus_1:= by
          unfold casted_a_plus_1 casted_b_plus_1
          simp
          exact Fin.ne_of_val_ne h1
        have hab' : casted_a ≠ casted_b_plus_1 := by
          unfold casted_a casted_b_plus_1
          rw [caster_val (n-1) a, caster_val (n-1) b] at h3
          rw [Fin.ne_iff_vne]
          simp at h3
          simp
          exact h3
        have ha'b : casted_a_plus_1 ≠ casted_b := by
          unfold casted_a_plus_1 casted_b
          rw [caster_val (n-1) a, caster_val (n-1) b] at h2
          rw [Fin.ne_iff_vne]
          simp at h2
          simp
          exact h2
        exact disj_swap_ord n haa' hbb' hab2 hab' ha'b ha'b'

abbrev Phi (n : ℕ) (hn : n > 0) : Cₙ (n-1) →* Sₙ n := PresentedGroup.toGroup (F_resp_rels n hn )


-- Adjacent transpositions are in the image of Phi
lemma ajd_swap_Phi_img (n : ℕ) (hn : n > 0) :
  ∀ (i : Fin (n - 1)), ∃ (x : Cₙ (n-1)),
  Phi n hn x = swap
    (Fin.cast (hn_helper n hn) (caster (n-1) i))
    (Fin.cast (hn_helper n hn) (Fin.succ i))
  := by
  intro i
  use PresentedGroup.of i
  apply PresentedGroup.toGroup.of



-- The group homomorphism Phi: C₄ → S₅ is surjective
lemma Phi_surj (n : ℕ) (hn : n > 0) : Function.Surjective (Phi n hn) := by
  have hm : Submonoid.closure (Set.range (F n hn)) ≤ ((Phi n hn).range).toSubmonoid := by
    rw [Submonoid.closure_le]
    simp
    intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    simp
    use PresentedGroup.of y
    unfold Phi
    rw [← hy, ← PresentedGroup.toGroup.of (F_resp_rels n hn)]
    rfl
  have hs : (Set.range fun (i : Fin (n-1)) ↦ swap (Fin.cast (hn_helper n hn) i.castSucc) (Fin.cast (hn_helper n hn) i.succ)) = Set.range (F n hn) := by
    rfl
  sorry





#check Subgroup.card_dvd_of_surjective
#check Nat.bijective_iff_surjective_and_card



-- If f: G → H is a surjective homomorphism between finite groups and |G| ≤ |H| then f is bijective
-- Feel like this proof can be cleaned up
abbrev fin_grp_surj {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (f : G →* H)
  (hs : Function.Surjective f) (hgle : Nat.card G ≤ Nat.card H) :
  Function.Bijective f := by
  -- have hd : Nat.card H ∣ Nat.card G := Subgroup.card_dvd_of_surjective hs
  have hhle : Nat.card H ≤ Nat.card G := card_le_card_of_surjective (⇑f) hs
  have he : Nat.card G = Nat.card H := Nat.le_antisymm hgle hhle
  rw [Nat.bijective_iff_surjective_and_card]
  constructor
  · assumption
  · assumption


-- Under same assumptions as above we can conclude G ≅ H.
noncomputable def fin_grp_surj_equiv {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
  (f : G →* H) (hs : Function.Surjective f) (hgle : Nat.card G ≤ Nat.card H) :
  G ≃* H := by
  have hb : Function.Bijective f := fin_grp_surj f hs hgle
  apply MulEquiv.ofBijective f hb



-- Attempting to prove size of C₄ in a way that scales
-- Maybe this will be harder than just doing it
abbrev cast_3 : Fin 3 → Fin 4 := fun n ↦ Fin.castLE (by decide) n

abbrev C₃_incl : Fin 3 → S₅ := F ∘ cast_3

abbrev C₃_image : Subgroup S₅ := Subgroup.closure (Set.range C₃_incl)


--Assuming we want to use induction, it might be easiest to
--actually jump right up to the n case
