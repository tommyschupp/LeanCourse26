import LeanCourse26.Projects.GroupPresentations.integers
import Mathlib.Data.ZMod.Basic

-- FreeGroup.of 0 is the image of 0 under the map Fin 1 → FreeGroup (Fin 1), so is the generator
abbrev one_gen_mod_5 : Type :=
  PresentedGroup ({(FreeGroup.of 0) ^ 5} : Set (FreeGroup (Fin 1)))

abbrev Q₅ : FreeGroup (Fin 1) →* one_gen_mod_5 :=
  PresentedGroup.mk {(FreeGroup.of 0) ^ 5}

abbrev g₅ : one_gen_mod_5 := PresentedGroup.of 0

abbrev f' : Fin 1 → one_gen_mod_5
  | 0 => g₅

lemma f'_respects_relns :
    ∀ r ∈ ({} : Set (FreeGroup (Fin 1))) , (FreeGroup.lift f') r = 1 := by tauto

abbrev p : one_gen_no_relns →* one_gen_mod_5 := PresentedGroup.toGroup f'_respects_relns

-- I thought this would help with the proofs below but it ended up being unnecessary.
-- Still was a good exercise though.
lemma Q₅_factor : Q₅ = p.comp Q := by
  apply FreeGroup.ext_hom Q₅ (p.comp Q)
  intro a
  have ha : a = 0 := by
    exact Fin.fin_one_eq_zero a
  have hp : p g = g₅ := by
    exact PresentedGroup.toGroup.of f'_respects_relns
  have hQ₅ : Q₅ (FreeGroup.of 0) = g₅ := rfl
  have hQ : Q (FreeGroup.of 0) = g := rfl
  simp
  rw [ha, hQ, hp, hQ₅]


def is_power_5 (y : one_gen_mod_5) : Prop := ∃ m : ℤ, y = g₅ ^ m

lemma ind_one_5 : is_power_5 (Q₅ 1) := by
  use 0
  rw [zpow_zero, MonoidHom.map_one]

lemma ind_of_5 : ∀ (x : (Fin 1)), is_power_5 (Q₅ (FreeGroup.of x)) := by
  intro x
  have h : x = 0 := by
    exact Fin.fin_one_eq_zero x
  use 1
  rw [h, zpow_one]
  rfl

lemma ind_inv_of_5 : ∀ (x : (Fin 1)), is_power_5 (Q₅ (FreeGroup.of x)) →
  is_power_5 (Q₅ (FreeGroup.of x)⁻¹) := by
  intro x hx
  obtain⟨m, hm⟩ := hx
  use -m
  have hQ₅ : Q₅ (FreeGroup.of x)⁻¹ = (Q₅ (FreeGroup.of x))⁻¹ := by
    exact MonoidHom.map_inv Q₅ (FreeGroup.of x)
  rw[hQ₅, hm]
  exact Eq.symm (zpow_neg g₅ m)

lemma ind_mul_5 : ∀ (x y : FreeGroup (Fin 1)), is_power_5 (Q₅ x) →
  is_power_5 (Q₅ y) → is_power_5 (Q₅ (x * y)) := by
  intro x y hl hm
  obtain⟨l, hx⟩ := hl
  obtain⟨m, hy⟩ := hm
  use (l + m)
  rw [MonoidHom.map_mul, hx, hy]
  exact Eq.symm (zpow_add g₅ l m)

lemma fg_power_5 (z : FreeGroup (Fin 1)) : is_power_5 (Q₅ z) := by
  exact FreeGroup.induction_on z ind_one_5 ind_of_5 ind_inv_of_5 ind_mul_5

lemma pg_power_5 (x : one_gen_mod_5) : is_power_5 x := by
  exact PresentedGroup.induction_on x fg_power_5

-- Want an actual realization of Z/5Z here
-- abbrev Z₅ : ZMod
