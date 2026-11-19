import Mathlib.GroupTheory.PresentedGroup
noncomputable section

#click_suggestions

#check Fin 2

abbrev one_gen_no_relns : Type :=
  PresentedGroup ({} : Set (FreeGroup (Fin 1)))

#check one_gen_no_relns
#synth Group one_gen_no_relns
#synth Mul one_gen_no_relns
#check Group ℤ

-- This is the quotient map from the free group on one generator to the presented group that has one
-- generator and no relations.
abbrev Q : FreeGroup (Fin 1) →* one_gen_no_relns :=
  PresentedGroup.mk ∅

abbrev g : one_gen_no_relns := PresentedGroup.of 0

-- is_power is the property we want to prove for all elements of one_gen_no_relns
-- We do this using PresentedGroup.induction_on which relies on FreeGroup.induction_on
-- The lemmas below with "ind" in the name are helper lemmas for the FreeGroup induction
def is_power (y : one_gen_no_relns) : Prop := ∃ m : ℤ, y = g ^ m

lemma ind_one : is_power (Q 1) := by
  use 0
  rw [zpow_zero, MonoidHom.map_one]

lemma ind_of : ∀ (x : (Fin 1)), is_power (Q (FreeGroup.of x)) := by
  intro x
  have h : x = 0 := by
    exact Fin.fin_one_eq_zero x
  use 1
  rw [h, zpow_one]
  unfold g
  unfold Q
  exact (congrArg ⇑(QuotientGroup.mk' (Subgroup.normalClosure ∅)) ∘ congrArg FreeGroup.of) rfl

lemma ind_inv_of : ∀ (x : (Fin 1)), is_power (Q (FreeGroup.of x)) →
  is_power (Q (FreeGroup.of x)⁻¹) := by
  intro x hx
  obtain⟨m, hm⟩ := hx
  use -m
  have hQ : Q (FreeGroup.of x)⁻¹ = (Q (FreeGroup.of x))⁻¹ := by
    exact MonoidHom.map_inv Q (FreeGroup.of x)
  rw[hQ, hm]
  exact Eq.symm (zpow_neg g m)

lemma ind_mul : ∀ (x y : FreeGroup (Fin 1)), is_power (Q x) →
  is_power (Q y) → is_power (Q (x * y)) := by
  intro x y hl hm
  obtain⟨l, hx⟩ := hl
  obtain⟨m, hy⟩ := hm
  use (l + m)
  rw [MonoidHom.map_mul, hx, hy]
  exact Eq.symm (zpow_add g l m)

-- Here we apply FreeGroup induction to show that is_power holds for Q z for all elements z of the
-- free group.
lemma fg_power (z : FreeGroup (Fin 1)) : is_power (Q z) := by
  exact FreeGroup.induction_on z ind_one ind_of ind_inv_of ind_mul

-- We can now use PresentedGroup induction to show that is_power holds for all elements of the
-- presented group
lemma pg_power (x : one_gen_no_relns) : is_power x := by
  exact PresentedGroup.induction_on x fg_power






-- [DecidableEq (Fin 1)]
example : (one_gen_no_relns ≃* Multiplicative ℤ) := by
  let f : Fin 1 → Multiplicative ℤ
  | 0 => Multiplicative.ofAdd 1
  have f_respects_relns :
    ∀ r ∈ ({} : Set (FreeGroup (Fin 1))) , (FreeGroup.lift f) r = 1 := by tauto
  let phi : one_gen_no_relns →* Multiplicative ℤ :=
    PresentedGroup.toGroup f_respects_relns
  -- let g : one_gen_no_relns := PresentedGroup.of 0
  have hg : phi g = Multiplicative.ofAdd 1 := by
    rw[PresentedGroup.toGroup.of f_respects_relns]

  -- have hg : phi g = 1 := by
  --   rw[PresentedGroup.toGroup.of f_respects_relns]

  have h_inj : Function.Injective phi := by {
    intro x y hxy
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, hb⟩ := Quot.mk_surjective a
    have hx : ∃ m : ℤ, x = g ^ m := by sorry
    have hy : ∃ n : ℤ , y = g ^ n := by sorry
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    rw[hm, hn] at hxy
    have hphin : phi (g ^ n) = phi (g) ^ n := by sorry
    have hphim : phi (g ^ m) = phi (g) ^ m := by sorry
    rw[hphin, hphim] at hxy
    have hxy_move : (phi (g)) ^ (m - n) = 1 := by sorry
    have hmn : m - n = 0 := by sorry
    have xy_move : g ^ (m - n) = 1 := by sorry
    have xy : g ^ m = g ^ n := by sorry
    rw[hm, hn]
    exact xy
    }
  have h_surj : Function.Surjective phi := by {
    intro n
    sorry
  }
  have h_bij : Function.Bijective phi := by {
    constructor
    · exact h_inj
    · exact h_surj
  }
  apply MulEquiv.ofBijective phi h_bij
