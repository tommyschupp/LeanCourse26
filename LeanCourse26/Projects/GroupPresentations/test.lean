import Mathlib.GroupTheory.PresentedGroup
noncomputable section

#check Fin 2

abbrev one_gen_no_relns : Type :=
  PresentedGroup ({} : Set (FreeGroup (Fin 1)))

#check one_gen_no_relns
#synth Group one_gen_no_relns
#synth Mul one_gen_no_relns
#check Group ℤ


example : (one_gen_no_relns ≃* Multiplicative ℤ) := by
  let f : Fin 1 → Multiplicative ℤ
  | 0 => 1
  have f_respects_relns :
    ∀ r ∈ ({} : Set (FreeGroup (Fin 1))) , (FreeGroup.lift f) r = 1 := by tauto
  let phi : one_gen_no_relns →* Multiplicative ℤ :=
    PresentedGroup.toGroup f_respects_relns
  let g : one_gen_no_relns := PresentedGroup.of 0

  have hg : phi g = Multiplicative.ofAdd 1 := by sorry

  have h_inj : Function.Injective phi := by {
    intro x y hxy
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
