import TSGA.PowerOscillation
import TSGA.PhaseLocalization
import TSGA.BulkLocalization
import TSGA.LocalizationAssembly

/-! # The root-gradient estimate on a ball of large density oscillation

The spectral power comparison turns the oscillation threshold for the bulk
power into a lower bound on the oscillation of the matrix root. Morrey's
inequality then controls the maximum charge times the volume of the ball.
-/

noncomputable section

namespace TSGA

open MeasureTheory Metric Set TSGA.Localization PhaseLocalization

theorem BulkRegime.root_le_densityPower (mode : BulkRegime) {p θ : ℝ}
    (hp : 0 < p) (hpθ : 2 ≤ p * θ) : 1 / p ≤ mode.densityPower p θ := by
  have hθ : 1 / p ≤ θ := (div_le_iff₀ hp).2 (by linarith [mul_comm p θ])
  cases mode <;> first | exact hθ | exact le_rfl

namespace ManyBody

/-- The local Sobolev hypothesis provides an integrable root-gradient power
on every compact subset of its domain, including the closed comparison ball. -/
theorem rootPower_integrableOn_compact {D : Density} {p : ℝ} {G : MatrixGradient}
    {U K : Set Position} (hp : 0 < p) (reg : RootRegularOn U D p G)
    (hK : IsCompact K) (sub : K ⊆ U) : IntegrableOn (rootPower G p) K := by
  have loc : LocallyIntegrableOn (rootPower G p) U := by
    intro x hx
    obtain ⟨r, hr, _, _, _, hLp⟩ := reg x hx
    refine ⟨ball x r, nhdsWithin_le_nhds (ball_mem_nhds x hr), ?_⟩
    change Integrable (fun y => matrixGradNorm G y ^ p) (volume.restrict (ball x r))
    have hn (y : Position) : ‖matrixGradNorm G y‖ = matrixGradNorm G y :=
      Real.norm_of_nonneg (Real.sqrt_nonneg _)
    simpa only [hn, ENNReal.toReal_ofReal hp.le] using
      hLp.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  exact loc.integrableOn_compact_subset sub hK

/-- The volume normalization of Morrey's inequality at the comparison
radius `3/ε`. Its coefficient is independent of the center and of ε. -/
theorem tile_ball_morrey_scale {p ε C d J : ℝ} (he : 0 < ε) (c : Position)
    (h : d ≤ C * (3 * ε⁻¹)^(p-3) * J) :
    volume.real (closedBall c (3 * ε⁻¹)) * d ≤
      (volume.real (ball (0 : Position) 1) * (3 : ℝ)^p * C) * ε^(-p) * J := by
  let R := 3 * ε⁻¹
  have hR : 0 < R := mul_pos (by norm_num) (inv_pos.mpr he)
  have hs : R^(3 : ℕ) * R^(p-3) = (3 : ℝ)^p * ε^(-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    rw [show ((3 : ℕ) : ℝ) + (p-3) = p by norm_num]
    dsimp only [R]
    rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr he.le), Real.inv_rpow he.le, Real.rpow_neg he.le]
  calc
    _ ≤ volume.real (closedBall c R) * (C * R^(p-3) * J) :=
      mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg
    _ = (volume.real (ball (0 : Position) 1) * C * J) * (R^(3 : ℕ) * R^(p-3)) := by
      rw [Measure.addHaar_real_closedBall volume c hR.le]
      simp only [finrank_euclideanSpace, Fintype.card_fin]
      ring
    _ = _ := by rw [hs]; ring

/-- Divide the volume-normalized estimate by the ball volume and express the
result using the project's open-ball average. Spheres have zero volume. -/
theorem tile_ball_morrey_average {p ε A d : ℝ} {f : Position → ℝ}
    (he : 0 < ε) (c : Position)
    (h : volume.real (closedBall c (3*ε⁻¹)) * d ≤
      A * ε^(-p) * ∫ z in closedBall c (3*ε⁻¹), f z) :
    d ≤ ε^(-p) * (A * ballAverage (3*ε⁻¹) f c) := by
  let R := 3 * ε⁻¹
  have hR : 0 < R := mul_pos (by norm_num) (inv_pos.mpr he)
  have hv : volume.real (closedBall c R) = ballVolume R :=
    (Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume c R).trans
      (Measure.addHaar_real_ball_center volume c R)
  have hi : (∫ z in closedBall c R, f z) = ballIntegral R f c :=
    setIntegral_congr_set (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume c R).le measurableSet_ball.nullMeasurableSet
      (isCompact_closedBall c R).measure_lt_top.ne).symm
  change volume.real (closedBall c R)*d ≤ A*ε^(-p)*(∫ z in closedBall c R, f z) at h
  rw [hv, hi] at h
  change d ≤ ε^(-p) * (A * (ballIntegral R f c / ballVolume R))
  rw [← mul_div_assoc, ← mul_div_assoc, le_div_iff₀ (ballVolume_pos hR)]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- A pair witnessing large oscillation of the `u`-power forces a comparable
oscillation of the `1/p`-power. This also covers the case of zero charge. -/
private theorem charge_le_root_oscillation {D : Density} {p u r κ : ℝ} {x y : Position}
    (hp : 0 < p) (hu : 1 / p ≤ u) (hκ : 0 < κ)
    (hx : D.charge x ≤ r) (hy : D.charge y ≤ r)
    (large : κ*r^u ≤ hilbertSchmidt (D.power u x - D.power u y)) :
    r ≤ (u*p/κ)^p * hilbertSchmidt (D.power (1/p) x - D.power (1/p) y)^p := by
  let δ := hilbertSchmidt (D.power (1/p) x - D.power (1/p) y)
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have ha : 0 < 1 / p := one_div_pos.mpr hp
  have hu' := ha.trans_le hu
  have hq := div_nonneg (mul_nonneg hu'.le hp.le) hκ.le
  have hr := (D.charge_nonneg x).trans hx
  rcases hr.eq_or_lt with hz | hr'
  · rw [← hz]
    exact mul_nonneg (Real.rpow_nonneg hq _) (Real.rpow_nonneg hδ _)
  have hmat := matrix_power_oscillation (D.positive x) (D.positive y) ha hu hr hx hy
  have h := large.trans hmat
  have hsplit : r^u = r^(1/p) * r^(u - 1/p) := by
    rw [← Real.rpow_add hr']
    congr 1
    ring
  have hcancel : (κ*r^(1/p))*r^(u - 1/p) ≤ (u*p*δ)*r^(u - 1/p) := by
    change κ*r^u ≤ (u/(1/p)*r^(u - 1/p))*δ at h
    rw [hsplit, div_div_eq_mul_div, div_one] at h
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hδlarge : r^(1/p) ≤ (u*p/κ)*δ := by
    have h' := le_of_mul_le_mul_right hcancel (Real.rpow_pos_of_pos hr' _)
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    exact (mul_comm _ κ).le.trans h'
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hδlarge hp.le
  rwa [← Real.rpow_mul hr, div_mul_cancel₀ _ hp.ne', Real.rpow_one,
    Real.mul_rpow hq hδ] at hpow

/-- On a compact subset of the active region, the local root Morrey
inequality controls the full charge scale on the large-oscillation branch. -/
theorem large_oscillation_active_morrey {D : Density} {φ : Phase} {G : MatrixGradient}
    {p u r κ ε C : ℝ} {K : Set Position}
    (hp : 0 < p) (hu : 1 / p ≤ u) (hκ : 0 < κ)
    (hφ : PhaseAdmissible D p φ G) (compact : IsCompact K) (active : K ⊆ φ.active)
    (charge : ∀ x ∈ K, D.charge x ≤ r)
    (large : ∃ x ∈ K, ∃ y ∈ K, κ*r^u ≤ hilbertSchmidt (D.power u x - D.power u y))
    (morrey : ∀ x ∈ K, ∀ y ∈ K,
      volume.real K * hilbertSchmidt (D.power (1/p) x - D.power (1/p) y)^p ≤
        C * ε^(-p) * ∫ z in K, rootPower G p z) :
    IntegrableOn (rootPower G p) K ∧ volume.real K * r ≤
      ((u*p/κ)^p * C) * ε^(-p) * ∫ z in K, rootPower G p z := by
  obtain ⟨x, hx, y, hy, hxy⟩ := large
  refine ⟨rootPower_integrableOn_compact hp hφ.root_regular compact active, ?_⟩
  have h := charge_le_root_oscillation hp hu hκ (charge x hx) (charge y hy) hxy
  have hq : 0 ≤ u*p/κ := by
    exact div_nonneg (mul_nonneg ((one_div_pos.mpr hp).le.trans hu) hp.le) hκ.le
  calc
    _ ≤ volume.real K * ((u*p/κ)^p * hilbertSchmidt (D.power (1/p) x - D.power (1/p) y)^p) :=
      mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg
    _ = (u*p/κ)^p * (volume.real K * hilbertSchmidt (D.power (1/p) x - D.power (1/p) y)^p) :=
      mul_left_comm _ _ _
    _ ≤ (u*p/κ)^p * (C * ε^(-p) * ∫ z in K, rootPower G p z) :=
      mul_le_mul_of_nonneg_left (morrey x hx y hy) (Real.rpow_nonneg hq _)
    _ = _ := by ring

end ManyBody
end TSGA
