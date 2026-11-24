import TSGA.CoulombModel
import TSGA.SmallBallPhase

/-! # Simultaneous comparison of two SSW gas energies on a ball -/

noncomputable section

namespace TSGA.ManyBody

open SSW TSGA.Localization
open scoped ComplexOrder

/-- The comparison of SSW gas energies in `lem:compare_SSW`. The trace bound
`r` may be chosen once for the ball. The constant works for every pair of
matrices, both wavevectors, and every localization parameter in (0,1]. -/
theorem CoulombGasInputs.compare_ssw {η : Mollifier} {K : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (S : SobolevDifferenceQuotients) {p : ℝ} (hp : 3 ≤ p) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ},
      0 < r → A.trace.re ≤ r → B.trace.re ≤ r → ∀ (q k : Position) {ε : ℝ}, 0 < ε → ε ≤ 1 →
      |sswEnergy energy η A q - sswEnergy energy η B k| ≤ C *
        (holderGrowth r q *
          (hilbertSchmidt (hA.1.cfc (fun t => t^(1/p:ℝ)) - hB.1.cfc (fun t => t^(1/p:ℝ))) /
            r^(1/p:ℝ)) +
          (r + r^(4/3:ℝ))*‖q-k‖ + r*‖q-k‖^2/ε + ε*r*‖q‖^2) := by
  obtain ⟨J, hJ, modulus⟩ := coulomb_root_tile_modulus L.localization (L.kinematics H S)
    L.rate (L.removal H S) H.lo_nonneg H.indirect_lower hp
  let W := 2*K+1
  let C := max J (2*W)
  have hW : 0 ≤ W := by dsimp [W]; linarith [L.rate.one_le]
  refine ⟨C, hJ.trans_le (le_max_left ..), ?_⟩
  intro A B hA hB r hr hAr hBr q k ε hε hε'
  let s := max A.trace.re B.trace.re
  let a := 1/p
  let D := hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hB₀ := (RCLike.nonneg_iff.mp hB.trace_nonneg).1
  have hs : 0 ≤ s := hB₀.trans (le_max_right ..)
  have ha : 0 < a := one_div_pos.mpr (by linarith)
  have ha' : a ≤ 1 := (div_le_one (by linarith : 0 < p)).2 (by linarith)
  have hgr : 0 ≤ holderGrowth r q / r^a := by unfold holderGrowth; positivity
  have compare : holderGrowth s q / s^a ≤ holderGrowth r q / r^a := by
    rcases hs.eq_or_lt with h | h
    · simpa only [← h, Real.zero_rpow ha.ne', div_zero] using hgr
    exact holderGrowth_div_rpow_mono h (max_le hAr hBr) ha' q
  have matrixCost : J * holderGrowth s q * (D/s^a) ≤ C * (holderGrowth r q * (D/r^a)) := calc
    _ = J * (holderGrowth s q / s^a) * D := by ring
    _ ≤ C * (holderGrowth r q / r^a) * D := mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left compare hJ.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) hgr)) hD
    _ = _ := by ring
  let v := ‖q-k‖
  let P := (r+r^(4/3:ℝ))*v + r*v^2/ε + ε*r*‖q‖^2
  have hP : 0 ≤ P := by dsimp [P, v]; positivity
  have phase := wavevectorModulus_le_smallBallPhaseCost (q := q) (k := k)
    hB₀ hBr (le_refl (0:ℝ)) hε hε' (show ‖k-q‖ ≤ v by rw [norm_sub_rev])
  have phaseCost : smallBallPhaseCost r 0 ε v q = P := by
    simp only [smallBallPhaseCost, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, P]
    ring
  rw [phaseCost] at phase
  have waveCost := (mul_le_mul_of_nonneg_left phase hW).trans
    (show W*(2*P) ≤ C*P by
      rw [← mul_assoc, mul_comm W 2]
      exact mul_le_mul_of_nonneg_right (le_max_right ..) hP)
  have bound := modulus hA hB q k
  rw [mul_assoc W] at bound
  exact bound.trans ((add_le_add matrixCost waveCost).trans_eq (by dsimp [P, v, D, a]; ring))

end TSGA.ManyBody
