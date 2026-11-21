import LeanCourse26.Projects.GroupPresentations.integers
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
noncomputable section

#click_suggestions

-- FreeGroup.of 0 is the image of 0 under the map Fin 1 → FreeGroup (Fin 1), so is the generator
abbrev one_gen_mod_5 : Type :=
  PresentedGroup ({(FreeGroup.of 0) ^ 5} : Set (FreeGroup (Fin 1)))

abbrev Q₅ : FreeGroup (Fin 1) →* one_gen_mod_5 :=
  PresentedGroup.mk {(FreeGroup.of 0) ^ 5}

abbrev g₅ : one_gen_mod_5 := PresentedGroup.of 0

lemma g₅_one : g₅ ^ 5 = 1 := by
  rw [show g₅ = Q₅ (FreeGroup.of 0) from rfl,
    show Q₅ = PresentedGroup.mk {FreeGroup.of 0 ^ 5} from rfl, ← MonoidHom.map_pow]
  apply PresentedGroup.mk_eq_one_iff.2
  apply Subgroup.subset_normalClosure
  simp

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
abbrev Z₅ : Type := Multiplicative (ZMod 5)


#check (Int.cast 1 : (ZMod 5))

#check (orderOf (1 : (ZMod 5)))


def mod_5 (x : ℤ) : (ZMod 5) := x


-- Since 1 : (ZMod 5) and not Multiplicative (ZMod 5), it is actually 1 and not 0.
def f₅ : Fin 1 → Z₅
  | 0 =>  (1 : (ZMod 5))




lemma f₅_order : orderOf (f₅ 0) = 5 := by
  rw [← addOrderOf_ofMul_eq_orderOf, show f₅ 0 = (1 : ZMod 5) from rfl]
  exact ZMod.addOrderOf_one 5



lemma f₅_respects_relns :
  ∀ r ∈ ({(FreeGroup.of 0) ^ 5} : Set (FreeGroup (Fin 1))) , (FreeGroup.lift f₅) r = 1 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  rw [hr, MonoidHom.map_pow, FreeGroup.lift_apply_of]
  rfl

def phi₅ : one_gen_mod_5 →* Z₅ := PresentedGroup.toGroup f₅_respects_relns


lemma Z₅_cyclic : IsCyclic Z₅ := by
  apply isCyclic_multiplicative_iff.2
  exact ZMod.instIsAddCyclic 5



def one_gen_mod_5_equiv_ZMod_5 : (one_gen_mod_5 ≃* Z₅) := by
  have hg₅ : phi₅ g₅ = f₅ 0 := by
    exact Eq.symm (Multiplicative.ext rfl)

  have hg₅' : phi₅ g₅ = Multiplicative.ofAdd 1 := by
    exact Eq.symm (Multiplicative.ext rfl)

  have h_inj : Function.Injective phi₅ := by
    intro x y hxy
    have hx : ∃ m : ℤ, x = g₅ ^ m := pg_power_5 x
    have hy : ∃ n : ℤ , y = g₅ ^ n := pg_power_5 y
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    rw [hm, hn, MonoidHom.map_zpow, MonoidHom.map_zpow, zpow_eq_zpow_iff_modEq, hg₅, f₅_order,
      Int.cast_ofNat_Int, Int.modEq_iff_dvd] at hxy
    obtain ⟨k, hk⟩ := hxy
    rw [Int.sub_eq_iff_eq_add] at hk
    rw [hk, zpow_add] at hn
    rw [hm, hn, right_eq_mul, zpow_mul, zpow_ofNat, g₅_one]
    exact one_zpow k

  have h_surj : Function.Surjective phi₅ := by
    intro n
    have hn : n = (Multiplicative.ofAdd 1) ^ (ZMod.val n) := by
      rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val n]
      rfl
    use (g₅ ^ ZMod.val n)
    rw [MonoidHom.map_pow, hg₅']
    rw[← hn]

  have h_bij : Function.Bijective phi₅ := by {
    constructor
    · exact h_inj
    · exact h_surj
  }

  apply MulEquiv.ofBijective phi₅ h_bij
