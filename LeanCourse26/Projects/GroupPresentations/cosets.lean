import LeanCourse26.Projects.GroupPresentations.arb_coxeter

#click_suggestions

-- This file is to work on different strategies for proving the coset cases in the proof.

-- How we denote the generators s_0, ..., s_{n-1} of C_n. gen i = s_i.
#check gen

-- abbrev coset_rep {n : ℕ} (i : Fin n) : cox_grp n :=
--   | 0 => 1
--   | n + 1 => (gen)

-- lemma coset_rep_helper {n i : ℕ} (h : i < n) (h' : 0 < i) : (0 ≤ n - 1 - i) ∧ (n - 1 - i < n)
  -- := by
--   omega

-- Lemma that ensures that n - 1 - i is an element of Fin n if i is a non-zero element of Fin n.
lemma coset_rep_helper {n i : ℕ} (h : i < n) (h' : 0 < i) : (n - 1 - i < n) := by
  omega

/-
Given n > 0 we get a function defining a product P_i of the generators s_0, ..., s_{n-1} of C_n
inductively. P_0 = s_{n-1} and P_{i+1} = s_{n-i-2} * P_i. This means we have
P_0 = s_{n-1}
P_1 = s_{n-2} * s_{n-1}
...
P_{n-1} = s_0 * ... * s_{n-1}
-/
abbrev coset_rep {n : ℕ} (h : 0 < n) : Fin n → cox_grp n
  | ⟨0, _⟩ => gen ⟨n - 1 , by omega⟩
  | ⟨i + 1, H⟩ => gen ⟨n - 1 - (i + 1), (coset_rep_helper H (Nat.succ_pos'))⟩
    * (coset_rep h ⟨i, Nat.lt_of_succ_lt H⟩)


-- The original attempt atthis is in arb_coxeter.lean
lemma coset_case_2 {n : ℕ} {i j : Fin n} (h : 0 < n) (h' : j.val = i.val + 1) :
  coset_rep h j = gen ⟨n - 1 - j.val, (coset_rep_helper j.isLt (by omega))⟩ * (coset_rep h i) := by
  have H : 1 < n := by
    omega
  -- have H' : (i + (Fin.mk 1 H)).val = i.val + 1 := by
  --   apply Fin.val_add_eq_of_add_lt
  --   rw [← h']
  --   omega
  -- have H'' : (i + (Fin.mk 1 H)).val < n := by
  --   omega
  -- rw [← H'] at h'
  -- have H''' : j = i + (Fin.mk 1 H) := Fin.eq_of_val_eq h'
  -- subst H'''
  -- unfold coset_rep
  have H' : i.val + 1 < n := by
    omega
  have H'' : j = ⟨(i.val + 1), H'⟩ := Fin.eq_mk_iff_val_eq.mpr h'
  subst H''
  simp
  nth_rw 1 [coset_rep]


-- The original successful attempt at this is in arb_coxeter.lean
lemma coset_case_1 {n : ℕ} {i j : Fin n} (h : 0 < n) (h' : j.val < n - i.val - 2) :
  Commute (gen j) (coset_rep h i) := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    simp at h'
    unfold coset_rep
    let index := (Fin.mk (n-1) (by omega) : Fin n)
    have hi : index.val = n-1 := by
      rw [Fin.val_mk]
    have habs : 1 < ((j : ℤ) - index).natAbs := by
      rw [hi]
      omega
    exact rel_4_comm habs
  | succ k ih =>
    unfold coset_rep
    have hf : n - 1 - (k + 1) < n := by
      omega
    let index := (Fin.mk (n - 1 - (k + 1)) hf : Fin n)
    have hi : index.val = n - 1 - (k + 1) := by
      rw [Fin.val_mk]
    rw [Fin.val_mk hk] at h'
    have habs : 1 < ((j : ℤ) - index).natAbs := by
      omega
    have hcom : Commute (gen j) (gen index) := by
      exact rel_4_comm habs
    -- simp_rw [Fin.val_mk] at ih
    rw [Nat.sub_add_eq, Nat.sub_right_comm] at h'
    have hk' : k < n := by
      omega
    have h'' : j < n - k - 2 := by
      omega
    specialize ih hk'
    rw [Fin.val_mk hk'] at ih
    specialize ih h''
    apply Commute.mul_right
    · assumption
    · assumption
