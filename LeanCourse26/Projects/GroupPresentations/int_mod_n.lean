import LeanCourse26.Projects.GroupPresentations.integers
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
noncomputable section

#click_suggestions
-- FreeGroup.of 0 is the image of 0 under the map Fin 1 → FreeGroup (Fin 1), so is the generator
abbrev one_gen_mod_n (n : ℕ) : Type :=
  PresentedGroup ({(FreeGroup.of 0) ^ n} : Set (FreeGroup (Fin 1)))

abbrev Qₙ (n : ℕ) : FreeGroup (Fin 1) →* one_gen_mod_n n:=
  PresentedGroup.mk {(FreeGroup.of 0) ^ n}

abbrev gₙ (n : ℕ) : one_gen_mod_n n := PresentedGroup.of 0

lemma gₙ_one (n : ℕ) : (gₙ n)^ (↑n) = 1 := by
  rw [show gₙ n = Qₙ n (FreeGroup.of 0) from rfl,
    show Qₙ n = PresentedGroup.mk {FreeGroup.of 0 ^ n} from rfl, ← MonoidHom.map_pow]
  apply PresentedGroup.mk_eq_one_iff.2
  apply Subgroup.subset_normalClosure
  simp

abbrev f' (n : ℕ) : Fin 1 → one_gen_mod_n n
  | 0 => gₙ n

lemma f'_respects_relns (n : ℕ):
    ∀ r ∈ ({} : Set (FreeGroup (Fin 1))) , (FreeGroup.lift (f' n)) r = 1 := by tauto

abbrev p (n : ℕ) : one_gen_no_relns →* one_gen_mod_n n
  := PresentedGroup.toGroup (f'_respects_relns n)

-- I thought this would help with the proofs below but it ended up being unnecessary.
-- Still was a good exercise though.
lemma Qₙ_factor (n : ℕ) : (Qₙ n) = (p n).comp Q := by
  apply FreeGroup.ext_hom (Qₙ n) ((p n).comp Q)
  intro a
  have ha : a = 0 := by
    exact Fin.fin_one_eq_zero a
  have hp : (p n) g = gₙ n := by
    exact PresentedGroup.toGroup.of (f'_respects_relns n)
  have hQₙ : Qₙ n (FreeGroup.of 0) = gₙ n := rfl
  have hQ : Q (FreeGroup.of 0) = g := rfl
  simp
  rw [ha, hQ, hp, hQₙ]


def is_power_n (n : ℕ) (y : one_gen_mod_n n) : Prop := ∃ m : ℤ, y = (gₙ n) ^ m

lemma ind_one_n (n : ℕ) : is_power_n n (Qₙ n 1) := by
  use 0
  rw [zpow_zero, MonoidHom.map_one]

lemma ind_of_n (n : ℕ) : ∀ (x : (Fin 1)), is_power_n n (Qₙ n (FreeGroup.of x)) := by
  intro x
  have h : x = 0 := by
    exact Fin.fin_one_eq_zero x
  use 1
  rw [h, zpow_one]
  rfl

lemma ind_inv_of_n (n : ℕ) : ∀ (x : (Fin 1)), is_power_n n (Qₙ n (FreeGroup.of x)) →
  is_power_n n (Qₙ n (FreeGroup.of x)⁻¹) := by
  intro x hx
  obtain⟨m, hm⟩ := hx
  use -m
  have hQₙ : Qₙ n (FreeGroup.of x)⁻¹ = (Qₙ n (FreeGroup.of x))⁻¹ := by
    exact MonoidHom.map_inv (Qₙ n) (FreeGroup.of x)
  rw[hQₙ, hm]
  exact Eq.symm (zpow_neg (gₙ n) m)

lemma ind_mul_n (n : ℕ) : ∀ (x y : FreeGroup (Fin 1)), (is_power_n n) (Qₙ n x) →
  is_power_n n (Qₙ n y) → is_power_n n (Qₙ n (x * y)) := by
  intro x y hl hm
  obtain⟨l, hx⟩ := hl
  obtain⟨m, hy⟩ := hm
  use (l + m)
  rw [MonoidHom.map_mul, hx, hy]
  exact Eq.symm (zpow_add (gₙ n) l m)

lemma fg_power_n (n : ℕ) (z : FreeGroup (Fin 1)) : is_power_n n (Qₙ n z) := by
  exact FreeGroup.induction_on z (ind_one_n n) (ind_of_n n) (ind_inv_of_n n) (ind_mul_n n)

lemma pg_power_n (n : ℕ) (x : one_gen_mod_n n) : is_power_n n x := by
  exact PresentedGroup.induction_on x (fg_power_n n)

abbrev Zₙ (n : ℕ) : Type := Multiplicative (ZMod n)


def mod_n (n : ℕ) (x : ℤ) : (ZMod n) := x


def fₙ (n : ℕ) : Fin 1 → Zₙ n
  | 0 =>  (1 : (ZMod n))




lemma fₙ_order (n : ℕ) : orderOf (fₙ n 0) = n := by
  rw [← addOrderOf_ofMul_eq_orderOf, show fₙ n 0 = (1 : ZMod n) from rfl]
  exact ZMod.addOrderOf_one n



lemma fₙ_respects_relns (n : ℕ) :
  ∀ r ∈ ({(FreeGroup.of 0) ^ n} : Set (FreeGroup (Fin 1))) , (FreeGroup.lift (fₙ n)) r = 1 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  rw [hr, MonoidHom.map_pow, FreeGroup.lift_apply_of, pow_eq_one_iff_modEq, fₙ_order]
  exact Nat.modulus_modEq_zero


def phiₙ (n : ℕ) : one_gen_mod_n n →* Zₙ n := PresentedGroup.toGroup (fₙ_respects_relns n)


lemma Zₙ_cyclic (n : ℕ) : IsCyclic (Zₙ n) := by
  apply isCyclic_multiplicative_iff.2
  exact ZMod.instIsAddCyclic n



def one_gen_mod_n_equiv_ZMod_n (n : ℕ) (hn : NeZero n): (one_gen_mod_n n ≃* Zₙ n) := by
  have hgₙ : (phiₙ n) (gₙ n) = (fₙ n) 0 := by
    simp [phiₙ]


  have hgₙ' : phiₙ n (gₙ n) = Multiplicative.ofAdd 1 := by
    simp [phiₙ]
    rfl

  have h_inj : Function.Injective (phiₙ n) := by
    intro x y hxy
    have hx : ∃ m : ℤ, x = (gₙ n) ^ m := pg_power_n n x
    have hy : ∃ l : ℤ , y = (gₙ n) ^ l := pg_power_n n y
    obtain ⟨m, hm⟩ := hx
    obtain ⟨l, hl⟩ := hy
    rw [hm, hl, MonoidHom.map_zpow, MonoidHom.map_zpow, zpow_eq_zpow_iff_modEq, hgₙ, (fₙ_order n),
      Int.modEq_iff_dvd] at hxy
    obtain ⟨k, hk⟩ := hxy
    rw [Int.sub_eq_iff_eq_add] at hk
    rw [hk, zpow_add] at hl
    rw [hm, hl, right_eq_mul, zpow_mul, zpow_natCast, (gₙ_one n)]
    exact one_zpow k

  have h_surj : Function.Surjective (phiₙ n) := by
    intro m
    have hm : m = (Multiplicative.ofAdd 1) ^ (ZMod.val m) := by
      rw [← ofAdd_nsmul,
      nsmul_one,
      ZMod.natCast_zmod_val m]
      rfl
    use ((gₙ n) ^ ZMod.val m)
    rw [MonoidHom.map_pow, hgₙ']
    rw[← hm]

  have h_bij : Function.Bijective (phiₙ n) := by {
    constructor
    · exact h_inj
    · exact h_surj
  }

  apply MulEquiv.ofBijective (phiₙ n) h_bij
