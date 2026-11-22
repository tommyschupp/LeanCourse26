import LeanCourse26.Projects.GroupPresentations.symmetric

#click_suggestions

-- Candidate Coxeter matrix for arbitrary n
abbrev Cox_mat_temp (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j =>
    if i.val = j.val then 1
    else if i.val + 1 = j.val then 3
    else if i.val = j.val + 1 then 3
    else 2


-- First requirement for creating Coxeter group
lemma Cox_mat_temp_is_symm (n : ℕ): (Cox_mat_temp n).IsSymm := by
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
lemma Cox_mat_temp_diagonal {n : ℕ} (i : Fin n) : (Cox_mat_temp n) i i = 1 := by
  simp


-- Third requirement
lemma Cox_mat_temp_off_diagonal {n : ℕ} (i j : Fin n) : i ≠ j → (Cox_mat_temp n) i j ≠ 1 := by
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
abbrev Cox_mat (n : ℕ) : CoxeterMatrix (Fin n) where
  M := Cox_mat_temp n
  isSymm := Cox_mat_temp_is_symm n
  diagonal := Cox_mat_temp_diagonal
  off_diagonal := Cox_mat_temp_off_diagonal


-- Coxeter group for arbitrary n
abbrev Cox_grp (n : ℕ) : Type := CoxeterMatrix.Group (Cox_mat n)


-- Want to define function Cox_grp n → Cox_grp n+1, do this using PresentedGroup.map
-- The definition using "fun n ↦ Fin.castLE (by decide) n" as in symmetric.lean didn't work
abbrev succ_cast (n : ℕ) : Fin n → Fin (n+1) := Fin.castSucc

abbrev free_cast (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Fin (n+1)) := FreeGroup.map (succ_cast n)


lemma free_cast_helper_pow {n : ℕ} (i j : Fin n) : (Cox_mat n) i j =
  (Cox_mat (n+1)) (succ_cast n i) (succ_cast n j) := by
  simp    -- simp might be the goat


lemma free_cast_helper_mem {n : ℕ} (y : (Fin n) × (Fin n)) :
  ((free_cast n) (FreeGroup.of y.1) * (free_cast n) (FreeGroup.of y.2)) ^
    (Cox_mat (n + 1)).M (succ_cast n y.1) (succ_cast n y.2) ∈
  (Cox_mat (n + 1)).relationsSet := by
  rw [show (Cox_mat (n + 1)).relationsSet = Set.range (Function.uncurry (Cox_mat (n + 1)).relation)
      from rfl,
    Function.uncurry_def,
    show
      (Cox_mat (n + 1)).relation = fun i i' ↦
        (FreeGroup.of i * FreeGroup.of i') ^ (Cox_mat (n + 1)).M i i'
      from rfl]


-- Need this to create map between Coxeter groups, there has to be an easier way to prove it
lemma free_cast_resp_rels (n : ℕ) :
  Set.MapsTo (free_cast n) (CoxeterMatrix.relationsSet (Cox_mat n))
  (CoxeterMatrix.relationsSet (Cox_mat (n + 1))) := by
  unfold Set.MapsTo
  intro x hx
  -- have hex : ∃ (y : (Fin n) × (Fin n)),
  -- rw [show (Cox_mat n).relationsSet = Set.range (Function.uncurry (Cox_mat n).relation) from rfl,
  --   show (Cox_mat n).relation = fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (Cox_mat n).M i i'
  --     from rfl] at hx
  rw [show (Cox_mat n).relationsSet = Set.range (Function.uncurry (Cox_mat n).relation) from rfl,
    show (Cox_mat n).relation = fun i i' ↦ (FreeGroup.of i * FreeGroup.of i') ^ (Cox_mat n).M i i'
      from rfl,
    Function.uncurry_def] at hx
  unfold Set.range at hx
  obtain ⟨y, hy⟩ := hx
  rw [show
      (fun p ↦ (FreeGroup.of p.1 * FreeGroup.of p.2) ^ (Cox_mat n).M p.1 p.2) y =
        (FreeGroup.of y.1 * FreeGroup.of y.2) ^ (Cox_mat n).M y.1 y.2
      from rfl] at hy
  rw [← hy, MonoidHom.map_pow, MonoidHom.map_mul]
  -- nth_rw 1 [show free_cast n = FreeGroup.map (succ_cast n) from rfl]
  -- rw [FreeGroup.map.of, show free_cast n = FreeGroup.map (succ_cast n) from rfl, FreeGroup.map.of]
  rw [free_cast_helper_pow]
