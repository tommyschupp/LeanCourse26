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


-- Need this to create map between Coxeter groups, there has to be an easier way to prove it
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
abbrev cox_incl (n : ℕ) : cox_grp n → cox_grp (n+1) :=
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
