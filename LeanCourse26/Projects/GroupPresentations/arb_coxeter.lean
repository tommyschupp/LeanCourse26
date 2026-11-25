import LeanCourse26.Projects.GroupPresentations.symmetric_5

#click_suggestions

-- Candidate Coxeter matrix for arbitrary n
abbrev cox_mat_temp (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j =>
    if i.val = j.val then 1
    else if i.val + 1 = j.val then 3
    else if i.val = j.val + 1 then 3
    else 2


-- First requirement for creating Coxeter group
lemma cox_mat_temp_is_symm (n : ℕ): (cox_mat_temp n).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  by_cases he : i.val = j.val
  · simp [he]
  · by_cases h1 : i.val + 1 = j.val
    · simp [h1.symm]
    · by_cases h2 : i.val = j.val + 1
      · simp [h2]
      · simp [he, h1, h2]
        simp [Ne.symm he, Ne.symm h2, Ne.symm h1]


-- Second requirement
lemma cox_mat_temp_diagonal {n : ℕ} (i : Fin n) : (cox_mat_temp n) i i = 1 := by
  simp


-- Third requirement
lemma cox_mat_temp_off_diagonal {n : ℕ} (i j : Fin n) : i ≠ j → (cox_mat_temp n) i j ≠ 1 := by
  intro h
  have h' : i.val ≠ j.val := by
    exact Fin.val_ne_of_ne h
  simp
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


-- Coxeter matrix for arbitrary n
abbrev cox_mat (n : ℕ) : CoxeterMatrix (Fin n) where
  M := cox_mat_temp n
  isSymm := cox_mat_temp_is_symm n
  diagonal := cox_mat_temp_diagonal
  off_diagonal := cox_mat_temp_off_diagonal


-- Coxeter group for arbitrary n
abbrev cox_grp (n : ℕ) : Type := CoxeterMatrix.Group (cox_mat n)

#eval cox_mat_temp 0

-- Want to define function cox_grp n → cox_grp n+1, do this using PresentedGroup.map
-- The definition using "fun n ↦ Fin.castLE (by decide) n" as in symmetric.lean didn't work
abbrev succ_cast (n : ℕ) : Fin n → Fin (n+1) := Fin.castSucc

abbrev free_cast (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Fin (n+1)) := FreeGroup.map (succ_cast n)


lemma free_cast_helper_pow {n : ℕ} (i j : Fin n) : (cox_mat_temp n) i j =
  (cox_mat_temp (n+1)) (succ_cast n i) (succ_cast n j) := by
  simp    -- simp might be the goat



-- note the exponent is split by a line break
-- This says the image under free_cast n of the of the relations given by cox_mat n is a relation
-- given by cox_mat (n + 1).
-- lemma free_cast_helper_2 {n : ℕ} (y : (Fin n) × (Fin n)) :
--   (free_cast n) (FreeGroup.of y.1 * FreeGroup.of y.2) ^ (cox_mat n).M y.1 y.2 =
--   (FreeGroup.of (succ_cast n y.1) * FreeGroup.of (succ_cast n y.2)) ^
--   (cox_mat (n+1)).M (succ_cast n y.1) (succ_cast n y.2) := by
--   sorry


-- lemma free_cast_helper_mem {n : ℕ} (y : (Fin n) × (Fin n)) :
--   ((free_cast n) (FreeGroup.of y.1) * (free_cast n) (FreeGroup.of y.2)) ^
--     (cox_mat (n + 1)).M (succ_cast n y.1) (succ_cast n y.2) ∈
--   (cox_mat (n + 1)).relationsSet := by
--  rw[show (cox_mat (n + 1)).relationsSet = Set.range (Function.uncurry (cox_mat (n + 1)).relation)
--       from rfl,
--     Function.uncurry_def,
--     show
--       (cox_mat (n + 1)).relation = fun i i' ↦
--         (FreeGroup.of i * FreeGroup.of i') ^ (cox_mat (n + 1)).M i i'
--       from rfl]


-- Map between Coxeter groups, used for inducting on the size
lemma free_cast_resp_rels (n : ℕ) :
  Set.MapsTo (free_cast n) (CoxeterMatrix.relationsSet (cox_mat n))
  (CoxeterMatrix.relationsSet (cox_mat (n + 1))) := by
  -- unfold Set.MapsTo
  intro x hx
  rw [show (cox_mat n).relationsSet =
    Set.range (Function.uncurry (cox_mat n).relation) from rfl,
    Function.uncurry_def,
    show (cox_mat n).relation =
     fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (cox_mat n).M i i' from rfl]
    at hx
  simp only [Set.mem_range, Prod.exists] at hx
  obtain ⟨a, b, hab⟩ := hx
  rw [← hab, MonoidHom.map_pow, MonoidHom.map_mul, FreeGroup.map.of, FreeGroup.map.of]
  rw [show (cox_mat (n+1)).relationsSet =
    Set.range (Function.uncurry (cox_mat (n+1)).relation) from rfl,
    Function.uncurry_def,
    show (cox_mat (n+1)).relation =
     fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (cox_mat (n+1)).M i i' from rfl]
  simp only [Set.mem_range, Prod.exists]
  use succ_cast n a, succ_cast n b
  rw [free_cast_helper_pow a b]

  -- have hex : ∃ (y : (Fin n) × (Fin n)),
  -- rw [show (cox_mat n).relationsSet = Set.range (Function.uncurry (cox_mat n).relation) from rfl,
  --  show (cox_mat n).relation = fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (cox_mat n).M i i'
  --     from rfl] at hx
  -- rw [show (cox_mat n).relationsSet = Set.range (Function.uncurry (cox_mat n).relation) from rfl,
  --  show (cox_mat n).relation = fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (cox_mat n).M i i'
  --     from rfl,
  --   Function.uncurry_def] at hx
  -- unfold Set.range at hx
  -- obtain ⟨y, hy⟩ := hx
  -- rw [show
  --     (fun p ↦ (FreeGroup.of p.1 * FreeGroup.of p.2) ^ (cox_mat n).M p.1 p.2) y =
  --       (FreeGroup.of y.1 * FreeGroup.of y.2) ^ (cox_mat n).M y.1 y.2
  --     from rfl] at hy
  -- rw [← hy, MonoidHom.map_pow, MonoidHom.map_mul]
  -- nth_rw 1 [show free_cast n = FreeGroup.map (succ_cast n) from rfl]
  -- rw[FreeGroup.map.of, show free_cast n = FreeGroup.map (succ_cast n) from rfl, FreeGroup.map.of]
  -- rw [free_cast_helper_pow]


-- Inclusion map C_n → C_{n+1} which allows us to use induction to prove size of C_n
abbrev cox_incl (n : ℕ) : cox_grp n →* cox_grp (n+1) :=
  PresentedGroup.map (free_cast n) (free_cast_resp_rels n)


-- This instance says that the free group with no generators has only one element
#check FreeGroup.instUniqueOfIsEmpty

-- Can apply this to show that it is isomorphic to the trivial group
abbrev empty_free_grp_triv : FreeGroup (Fin 0) ≃* Unit := MulEquiv.ofUnique

lemma empty_free_card : Nat.card (FreeGroup (Fin 0)) = 1 := Nat.card_unique

abbrev triv_cox : CoxeterMatrix (Fin 0) := cox_mat 0

example : cox_grp 0 = PresentedGroup triv_cox.relationsSet := rfl

abbrev triv_quot : FreeGroup (Fin 0) →* cox_grp 0 := PresentedGroup.mk triv_cox.relationsSet

#check Subgroup.card_bot (G := (cox_grp 0))
#check (Subgroup.card_le_card_group (G := (cox_grp 0)))



-- This is the base case for the induction that will put a bound on the size of cox_grp n
lemma triv_cox_card [Group (cox_grp 0)] [Fintype (cox_grp 0)] : Fintype.card (cox_grp 0) = 1 := by
  -- rw [← empty_free_card]
  have h : Fintype.card (cox_grp 0) ≤ Fintype.card (FreeGroup (Fin 0)) := by
    exact Fintype.card_le_of_surjective triv_quot
      (PresentedGroup.mk_surjective triv_cox.relationsSet)
  simp at h
  have h' : Fintype.card (cox_grp 0) ≥ 1 := NeZero.one_le
  exact Eq.symm (Nat.le_antisymm h' h)



-- Want to prove that the image of cox_incl (n-1) has at most n left cosets in C_n
/-
The quotient of a group `G` by a normal subgroup `H` is denoted `G ⧸ H`.
If `H` is not normal, this stands for the left cosets of `H`.
-/


#check leftCoset_eq_iff         -- left coset equality condition
#check Commute.inv_right        -- ab = ba implies ab⁻¹ = b⁻¹a



-- The image of C_n under the map C_n → C_{n+1}
abbrev cox_incl_img (n : ℕ) : Subgroup (cox_grp (n + 1)) := MonoidHom.range (cox_incl n)


-- gen i represents the generator s_{i+1} in cox_grp n.
-- This is because index for generators starts at 1 while cox_grp n is technically generated by
-- Fin n which starts a 0.
-- Fin.mk i h sends i to i ∈ Fin n.
-- abbrev gen {i n : ℕ} (h : i < n) : cox_grp n := PresentedGroup.of (Fin.mk i h)
abbrev gen {n : ℕ} (i : Fin n) : cox_grp n := PresentedGroup.of i

-- This is the function we use to take the product over the generators, see gen_prod
abbrev gen_prod_fun {n : ℕ} (i : Fin n) : Fin n → cox_grp n :=
  fun j => if j.val < i.val then 1 else gen j

abbrev prod_fun_test (n i : ℕ) : Fin n → ℕ :=
  fun j => if j.val < i-1 then 1 else j.val

#eval prod_fun_test 5 3


-- This is product s_{i} ... s_n.
-- Can't use ∏ in non-commutative groups so you need to use List.ofFn which takes a function
-- f: Fin n → G as input and outputs f(0) * f(1) * ... * f(n).
abbrev gen_prod {n : ℕ} (i : Fin n) : cox_grp n := (List.ofFn (gen_prod_fun i)).prod
-- abbrev prod {j n : ℕ} (h : j < n) : cox_grp n := (List.ofFn (prod_fun j n)).prod
  -- ∏ i ∈ Finset.Ico j n, if h : i < n then gen h else 1

open scoped Pointwise   -- Interprets a • (H : Set G) as the coset aH in a group G.


-- Let H denote the image of C_n in C_{n+1}. Let P_i denote the product s_i ... s_{n+1} in C_{n+1}.
-- This function sends i to the left coset P_i H.
-- These are n out of the n+1 cosets we will use to show the size of C_{n+1}.
abbrev coset_fun (n : ℕ) : Fin n → Set (cox_grp (n+1)) :=
  fun i => (gen_prod (succ_cast n i)) • ((cox_incl_img n) : Set (cox_grp (n+1)))

-- abbrev cosets (n : ℕ) : Set (Set (cox_grp (n+1))) :=
--   {(gen_prod i.val n) • (cox_incl_img n) | i ∈ Fin n}


-- This is the set {P_i H | 0 ≤ i < n+1} of left cosets of H in C_{n+1}.
abbrev coset_set (n : ℕ) : Set (Set (cox_grp (n+1))) := Set.range (coset_fun n)


-- Cleans up notation in theorem below
-- lemma succ_helper {n : ℕ} (i : Fin n) : i < n + 1 := Nat.lt_add_right 1 i.isLt


#check FreeGroup.map

-- The map C_n → C_{n+1} sends s_i ↦ s_i
lemma cox_incl_gen_to_gen {n : ℕ} (i : Fin n) : cox_incl n (gen i) = gen ((succ_cast n) i)
  := by
  -- cox_incl is defined using free_cast which is defined using succ_cast so maybe this will help
  -- have h : gen (succ_helper i.isLt) = gen (succ_cast n i).isLt := by
  --   simp
  -- rw [h]
  -- exact ((fun a ↦ h) ∘ fun a ↦ n) n
  exact ((fun a ↦ a) ∘ fun a ↦ a) rfl   -- exact? is goated




-- Proving generators of C_n satisfy the relations.
-- The following 4 lemmas just spell out that the relevant equations involving the generators
-- appear in the relation set itself. This directly proves that they appear in its normal closure
-- which is what we ultimately need.

lemma gen_cox_rel_helper_1 {n : ℕ} (i : Fin n) : FreeGroup.of i * FreeGroup.of i
  ∈ (cox_mat n).relationsSet := by
    rw [show (cox_mat n).relationsSet = Set.range (Function.uncurry (cox_mat n).relation) from rfl]
    simp
    use i
    use i
    rw [show (cox_mat n).relation i i = (FreeGroup.of i * FreeGroup.of i) ^ (cox_mat n).M i i from
        rfl,
      CoxeterMatrix.diagonal]
    simp

lemma gen_cox_rel_helper_2 {n : ℕ} {i j : Fin n} (h : i.val + 1 = j.val) :
  (FreeGroup.of i * FreeGroup.of j) ^ 3 ∈ (cox_mat n).relationsSet := by
  have h' : i.val ≠ j.val := by
    linarith
  rw [show (cox_mat n).relationsSet = Set.range (Function.uncurry (cox_mat n).relation) from rfl]
  simp
  use i
  use j
  rw [show (cox_mat n).relation i j = (FreeGroup.of i * FreeGroup.of j) ^ (cox_mat n).M i j from
      rfl]
  simp [h', h]    -- For some reason h' is necessary here

lemma gen_cox_rel_helper_3 {n : ℕ} {i j : Fin n} (h : i.val = j.val + 1) :
  (FreeGroup.of i * FreeGroup.of j) ^ 3 ∈ (cox_mat n).relationsSet := by
  -- have h' : i.val ≠ j.val := by
  --   linarith
  rw [show (cox_mat n).relationsSet = Set.range (Function.uncurry (cox_mat n).relation) from rfl]
  simp
  use i
  use j
  rw [show (cox_mat n).relation i j = (FreeGroup.of i * FreeGroup.of j) ^ (cox_mat n).M i j from
      rfl]
  simp [h]      -- but it's not necessary here

lemma gen_cox_rel_helper_4 {n : ℕ} {i j : Fin n} (h1 : i.val ≠ j.val) (h2 : i.val + 1 ≠ j.val)
  (h3 : i.val ≠ j.val + 1) : (FreeGroup.of i * FreeGroup.of j) ^ 2 ∈ (cox_mat n).relationsSet := by
  rw [show (cox_mat n).relationsSet = Set.range (Function.uncurry (cox_mat n).relation) from rfl]
  simp
  use i
  use j
  rw [show (cox_mat n).relation i j = (FreeGroup.of i * FreeGroup.of j) ^ (cox_mat n).M i j from
      rfl]
  simp [h1, h2, h3]


-- Reworks lt_abs to use natAbs
theorem lt_natAbs {b : ℤ} {c : ℕ} :
    c < b.natAbs ↔ (c : ℤ) < b ∨ (c : ℤ) < -b := by
  rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, lt_abs]

-- Unifying helper_4 into just |i - j| > 1.
lemma gen_cox_rel_helper_4_natAbs {n : ℕ} {i j : Fin n} (h : 1 < ((i : ℤ) - j).natAbs) :
  (FreeGroup.of i * FreeGroup.of j) ^ 2 ∈ (cox_mat n).relationsSet := by
  have h1' : (i : ℤ) ≠ j := by
    rw[← Int.natAbs_sub_pos_iff]
    linarith
  have h2' : (i : ℤ) + 1 ≠ j := by
    rw[lt_natAbs (b:= (i : ℤ) - j)] at h
    by_cases hc : 1 < (i : ℤ) - j
    · linarith
    · have hc' := h.resolve_left hc
      simp at hc'
      linarith
  have h3' : (i : ℤ) ≠ j + 1 := by
    rw[lt_natAbs (b:= (i : ℤ) - j)] at h
    by_cases hc : 1 < (i : ℤ) - j
    · linarith
    · have hc' := h.resolve_left hc
      simp at hc'
      linarith

  have h1 : i.val ≠ j.val := by
    exact Fin.val_ne_of_ne fun a ↦ h1' (congrArg Nat.cast (congrArg Fin.val a))
  have h2 : i.val + 1 ≠ j.val := by
    exact Ne.symm (Ne.intro fun a ↦ id (Ne.symm h2') (congrArg Nat.cast a))
  have h3 : i.val ≠ j.val + 1 := by
    exact Ne.intro fun a ↦ h3' (congrArg Nat.cast a)

  exact gen_cox_rel_helper_4 h1 h2 h3




-- Relation 1: s_i ^ 2 = 1
lemma gen_cox_rel_1 {n : ℕ} (i : Fin n) : (gen i) * (gen i) = 1 := by
  unfold gen
  unfold PresentedGroup.of
  erw [← MonoidHom.map_mul]
  erw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.subset_normalClosure
  exact gen_cox_rel_helper_1 i

-- Relation 1 implies that s_i = s_i^{-1}
lemma rel_1_self_inv {n : ℕ} (i : Fin n) : (gen i) = (gen i)⁻¹ := by
  rw[← mul_eq_one_iff_eq_inv]
  exact gen_cox_rel_1 i


-- Relation 2 part 1: (s_i s_{i+1}) ^ 3 = 1
lemma gen_cox_rel_2 {n : ℕ} {i j : Fin n} (h : i.val + 1 = j.val) : ((gen i) * (gen j)) ^ 3 = 1
  := by
  unfold gen
  unfold PresentedGroup.of
  erw [← MonoidHom.map_mul]
  erw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.subset_normalClosure
  exact gen_cox_rel_helper_2 h


-- Relation 2 part 2
lemma gen_cox_rel_3 {n : ℕ} {i j : Fin n} (h : i.val = j.val + 1) : ((gen i) * (gen j)) ^ 3 = 1
  := by
  unfold gen
  unfold PresentedGroup.of
  erw [← MonoidHom.map_mul]
  erw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.subset_normalClosure
  exact gen_cox_rel_helper_3 h


-- Relation 4: (s_i s_j) ^ 2 = 1 if |i - j| > 1
-- lemma gen_cox_rel_4 {n : ℕ} {i j : Fin n} (h1 : i.val ≠ j.val) (h2 : i.val + 1 ≠ j.val)
--   (h3 : i.val ≠ j.val + 1) : ((gen i) * (gen j)) ^ 2 = 1 := by
lemma gen_cox_rel_4 {n : ℕ} {i j : Fin n} (h : 1 < ((i : ℤ) - j).natAbs) :
  ((gen i) * (gen j)) ^ 2 = 1 := by
  unfold gen
  unfold PresentedGroup.of
  erw [← MonoidHom.map_mul]
  erw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.subset_normalClosure
  exact gen_cox_rel_helper_4_natAbs h


-- The generators commute if |i - j| > 1
lemma rel_4_comm {n : ℕ} {i j : Fin n} (h : 1 < ((i : ℤ) - j).natAbs) :
  Commute (gen i) (gen j) := by
  -- have h : orderOf ((gen i) * (gen j)) ∣ 2 :=
  --   orderOf_dvd_of_pow_eq_one (gen_cox_rel_4 h1 h2 h3)
  have h : ((gen i) * (gen j)) ^ 2 = 1 :=
    gen_cox_rel_4 h
  rw [sq, ← inv_eq_iff_mul_eq_one, mul_inv_rev, ← rel_1_self_inv, ← rel_1_self_inv] at h
  exact (commute_iff_eq (gen i) (gen j)).mpr (id (Eq.symm h))




-- This is one of the cases used in the classification of left cosets of the image of C_n in C_{n+1}
-- This shows that if j < i then s_j commutes with s_i s_{i+1} ... s_{n-1} within C_{n+1}
-- Note these are indexed starting at 0 so C_{n+1} is generated by s_0, ..., s_n.
-- MAYBE WANT TO CHANGE this to (j : ℤ) instead of j.val etc
lemma coset_case_1 {n : ℕ} {i j : Fin n} (h : j.val < i.val - 1) :
  (gen j) * (gen_prod i) = (gen_prod i) * (gen j) := by
  -- have ho : i.val ≥ 2 := by omega
  apply Commute.list_prod_right
  intro k hk
  rw [List.mem_ofFn] at hk
  obtain ⟨l, hl⟩ := hk
  by_cases hc : l.val < i.val
  · rw [show gen_prod_fun i l = if l.val < i.val then 1 else gen l from rfl] at hl
    simp [hc] at hl
    rw [← hl]
    exact Commute.one_right (gen j)
  · have hc' : l.val ≥ i.val := Nat.le_of_not_lt hc
    -- rw [Nat.not_lt] at hc
    have hjl := calc
      j.val < i.val - 1 := by assumption
      _ ≤ l.val - 1 := by exact Nat.sub_le_sub_right hc' 1
    rw [show gen_prod_fun i l = if l.val < i.val then 1 else gen l from rfl] at hl
    simp [hc] at hl
    rw [← hl]
    have hz : 1 < l - (j : ℤ) := by
      omega
      -- rw [← Int.ofNat_sub]
      -- apply Int.ofNat_lt_ofNat_of_lt
      -- exact lt_tsub_comm.mp hjl
      -- apply LT.lt.le
      -- omega
      -- rw [← Order.le_sub_one_iff_of_not_isMin]
      -- linarith
      -- rw [← Int.natCast_pred_of_pos]
      -- exact Int.ofNat_lt_ofNat_of_lt hjl
      -- linarith
    have habs : 1 < ((l : ℤ) - j).natAbs := by
      rw [lt_natAbs]
      left
      assumption
    rw [Commute.symm_iff]
    exact rel_4_comm habs



lemma coset_case_2 {n : ℕ} {i j : Fin n} (h : (j : ℤ) = i - 1) :
  (gen j) * (gen_prod i) = gen_prod j := by
  -- have h' : j = i + 1
  unfold gen_prod
  have hf : List.ofFn (gen_prod_fun j) = (List.ofFn (gen_prod_fun i)).set j ((gen_prod_fun j) j)
    := by
    apply List.ext_getElem
