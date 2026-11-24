import TSGA.CoordinateDilation
import TSGA.TetrahedronCoulomb

/-! # Coordinate scaling of the Coulomb SSW gas

A coordinate dilation by `b` multiplies the density by `b³`, the kinetic
energy by `b²`, and the indirect Coulomb energy by `b`. The scaled test
domain has volume `V/b³`.
-/

noncomputable section
namespace TSGA.ManyBody

open SSW Filter MeasureTheory Metric
open scoped Topology ComplexOrder InnerProductSpace

/-- Finite-system inequalities before dividing by the dilated volume.
`J` bounds the magnitude of the negative indirect energy of a single state. -/
theorem finite_coordinate_scaling {b J : ℝ} (hb : 0 < b) (hb' : b ≤ 1) {M : Position → SpinMatrix}
    (d : StateDilation b M) (hr : ∃ Γ, feasible M Γ)
    (hlo : ∀ Γ, feasible M Γ → -J ≤ indirectAt M Γ) :
    b^2 * energy M - (b-b^2)*J ≤ energy (coordinateDensity b M) ∧
      energy (coordinateDensity b M) ≤ b * energy M := by
  let N := coordinateDensity b M
  obtain ⟨Γ, hΓ⟩ := hr
  have g := energy_isGLB (M := M) ⟨Γ,hΓ⟩
  have g' := energy_isGLB (M := N) ⟨(d.states ⟨Γ,hΓ⟩).val, (d.states ⟨Γ,hΓ⟩).property⟩
  have hg (s : {Γ // feasible M Γ}) : energy M ≤ s.val.kinetic + indirectAt M s.val := by
    simpa only [indirectAt, add_sub_assoc] using g.1 (Set.mem_range_self s)
  have hd (s : {Γ // feasible M Γ}) : (d.states s).val.kinetic + (d.states s).val.interaction -
      hartree (fun x => (N x).trace.re) = b^2*s.val.kinetic + b*indirectAt M s.val := by
    rw [add_sub_assoc, ← d.indirect s, ← d.kinetic s]
    rfl
  have hgap : 0 ≤ b-b^2 := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb')]
  constructor
  · apply g'.2
    rintro _ ⟨t, rfl⟩
    obtain ⟨s,rfl⟩ := d.states.surjective t
    dsimp only
    rw [hd]
    nlinarith only [mul_le_mul_of_nonneg_left (hg s) (sq_nonneg b),
      mul_le_mul_of_nonneg_left (hlo s.val s.property) hgap]
  · have h : energy N / b ≤ energy M := by
      apply g.2
      rintro _ ⟨s,rfl⟩
      apply (div_le_iff₀ hb).mpr
      have hs := g'.1 (Set.mem_range_self (d.states s))
      dsimp only at hs ⊢
      rw [hd] at hs
      unfold indirectAt at hs
      nlinarith only [hs, mul_nonneg hgap s.val.kinetic_nonneg]
    simpa only [mul_comm b] using (div_le_iff₀ hb).mp h

private theorem dilated_balls (η : Mollifier) {b : ℝ} (hb : 0 < b) :
    ∃ D : DomainSequence, (∀ n, D.region n = ball 0 (((n : ℝ)+1)/b)) ∧
      (∀ n, D.delta n = b⁻¹) ∧ D.mollifier = η ∧
      ∀ n, D.vol n = (DomainSequence.balls η).vol n / b^3 := by
  let R (n : ℕ) : ℝ := ((n : ℝ)+1)/b
  have hR (n) : 0 < R n := by dsimp [R]; positivity
  have hv (n) : regionVolume (ball (0 : Position) (R n)) = (DomainSequence.balls η).vol n / b^3 := by
    rw [DomainSequence.vol, DomainSequence.balls_region, DomainSequence.ball_volume (hR n).le,
      DomainSequence.ball_volume (show (0:ℝ) ≤ n+1 by positivity)]
    simp only [R, div_pow]
    ring
  have ht : Tendsto (fun n => regionVolume (ball (0 : Position) (R n))) atTop atTop := by
    simp_rw [hv]
    exact (DomainSequence.balls η).vol_tendsto.atTop_div_const (pow_pos hb 3)
  have hl := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp ht
  let D : DomainSequence := {
    region := fun n => ball 0 (R n)
    region_open := fun _ => isOpen_ball
    region_connected := fun n => isConnected_ball (hR n)
    region_bounded := fun _ => isBounded_ball
    vol_tendsto := ht
    boundary := by
      obtain ⟨C,hC,h⟩ := DomainSequence.ball_boundary
      exact ⟨C,hC,fun n r => h (R n) r (hR n)⟩
    delta := fun _ => b⁻¹
    delta_pos := fun _ => inv_pos.mpr hb
    delta_ratio := hl.const_div_atTop _
    delta_product := hl.const_mul_atTop (inv_pos.mpr hb)
    mollifier := η }
  exact ⟨D, fun _ => rfl, fun _ => rfl, rfl, hv⟩

private theorem cutoff_dilate (η : Mollifier) {b : ℝ} (hb : 0 < b) (r : ℝ) (x : Position) :
    smoothedIndicator (ball 0 (r/b)) η b⁻¹ x = smoothedIndicator (ball 0 r) η 1 (b • x) := by
  classical
  let K (y : Position) := (ball (0:Position) r).indicator (fun _ => (1:ℝ)) y *
    η.scaled 1 (b • x - y)
  have hInd (y : Position) : (ball 0 (r/b)).indicator (fun _ => (1:ℝ)) y =
      (ball (0:Position) r).indicator (fun _ => (1:ℝ)) (b • y) := by
    simp only [Set.indicator, mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hb.le,
      lt_div_iff₀ hb, mul_comm b]
  have hs (y) : η.scaled b⁻¹ (x-y) = b^3 * η.scaled 1 (b • x - b • y) := by
    simp [Mollifier.scaled, smul_sub]
  change (∫ y, (ball 0 (r/b)).indicator (fun _ => (1:ℝ)) y * η.scaled b⁻¹ (x-y)) = ∫ y, K y
  have hcon (y : Position) : (ball 0 (r/b)).indicator (fun _ => (1:ℝ)) y * η.scaled b⁻¹ (x-y) =
      b^3 * K (b • y) := by rw [hInd, hs]; dsimp [K]; ring
  simp_rw [hcon]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume K b (hR := hb.le)]
  simp [finrank_euclideanSpace, smul_eq_mul, hb.ne']

private theorem cutoff_bounds (D : DomainSequence) (n : ℕ) (x : Position) :
    0 ≤ D.cutoff n x ∧ D.cutoff n x ≤ 1 :=
  smoothedIndicator_bounds (D.region n) D.mollifier (D.delta_pos n) x

private theorem moment_bound (D : DomainSequence) (n : ℕ) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    (∫ x, ((D.spiralField M n q x).trace.re)^(4/3 : ℝ)) ≤ M.trace.re^(4/3 : ℝ) * D.vol n := by
  let r := M.trace.re
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have he (x) : (D.spiralField M n q x).trace.re = D.cutoff n x*r := by
    simp [DomainSequence.spiralField, cutoffSpiral, Matrix.trace_smul, r]
  have hi : Integrable (D.cutoff n) := Integrable.of_integral_ne_zero ((D.cutoff_mass n).trans_ne (D.vol_pos n).ne')
  have h := integral_mono_of_nonneg (μ := volume)
    (ae_of_all _ fun x => Real.rpow_nonneg (mul_nonneg (cutoff_bounds D n x).1 hr) (4/3 : ℝ))
    (hi.mul_const (r^(4/3 : ℝ))) (ae_of_all _ fun x => by
      dsimp only
      rw [Real.mul_rpow (cutoff_bounds D n x).1 hr]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_le_one
        (cutoff_bounds D n x).1 (cutoff_bounds D n x).2 (by norm_num)) (Real.rpow_nonneg hr _))
  simp_rw [he]
  rw [integral_mul_const, D.cutoff_mass] at h
  exact h.trans_eq (mul_comm ..)

/-- The two gas inequalities in `eq:scaling_SSW`. Only the original
finite spirals need representing states. Dilation gives the states for the
scaled density and wavevector. The endpoint α=0 uses the vacuum energy. -/
theorem ssw_scaling {η χ : Mollifier} (gas : SSWGasTheorem (referenceEnergies energy η))
    {cLO : ℝ} (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3 : ℝ)) ≤ indirectAt D.matrix Γ)
    (M : SpinMatrix) (hM : M.PosSemidef) (q : Position)
    (represented : ∀ n, ∃ Γ, feasible ((DomainSequence.balls χ).spiralField M n q) Γ)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    α^(5/3 : ℝ) * (sswEnergy energy η M q + cLO * M.trace.re^(4/3 : ℝ)) -
      α^(4/3 : ℝ) * cLO * M.trace.re^(4/3 : ℝ) ≤ sswEnergy energy η (α • M) (α^(1/3 : ℝ) • q) ∧
    sswEnergy energy η (α • M) (α^(1/3 : ℝ) • q) ≤ α^(4/3 : ℝ) * sswEnergy energy η M q := by
  have hvac (k : Position) : sswEnergy energy η 0 k = 0 := gas.vacuum_ssw k
  rcases hα.eq_or_lt with h0 | hα
  · subst α
    simp [Real.zero_rpow (by norm_num : (5/3 : ℝ) ≠ 0), Real.zero_rpow (by norm_num : (4/3 : ℝ) ≠ 0), hvac]
  have htrace := RCLike.nonneg_iff.mp hM.trace_nonneg
  by_cases hr : 0 < M.trace.re
  · let b := α^(1/3 : ℝ)
    have hb : 0 < b := Real.rpow_pos_of_pos hα _
    have hb' : b ≤ 1 := Real.rpow_le_one hα.le hα' (by norm_num)
    have pow_b (n : ℕ) : b^n = α^((1/3:ℝ)*n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]
    have h3 : b^3 = α := by simpa using pow_b 3
    have h4 : b^4 = α^(4/3 : ℝ) := by rw [pow_b]; norm_num
    have h5 : b^5 = α^(5/3 : ℝ) := by rw [pow_b]; norm_num
    let D := DomainSequence.balls χ
    obtain ⟨D',hreg,hδ,hη,hvol⟩ := dilated_balls χ hb
    have hcut (n x) : D'.cutoff n x = D.cutoff n (b • x) := by
      simpa only [DomainSequence.cutoff, hreg, hδ, hη, D, DomainSequence.balls_region,
        DomainSequence.balls_mollifier, DomainSequence.balls_delta] using cutoff_dilate χ hb ((n:ℝ)+1) x
    have hfield (n) : D'.spiralField (α • M) n (b • q) = coordinateDensity b (D.spiralField M n q) := by
      funext x
      simp only [DomainSequence.spiralField, coordinateDensity, cutoffSpiral, h3, hcut, rotate,
        real_inner_smul_left, real_inner_smul_right, Matrix.mul_smul, Matrix.smul_mul, smul_comm α]
    let e := fun n => D.energyDensity energy M n q
    let e' := fun n => D'.energyDensity energy (α • M) n (b • q)
    let J := cLO * M.trace.re^(4/3 : ℝ)
    have he : Tendsto e atTop (𝓝 (sswEnergy energy η M q)) := gas.limit M hM hr q D
    have hr' : 0 < (α • M).trace.re := by
      simpa [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul] using mul_pos hα hr
    have he' : Tendsto e' atTop (𝓝 (sswEnergy energy η (α • M) (b • q))) :=
      gas.limit _ (hM.smul hα.le) hr' _ _
    have hfinite (n) : b^5 * (e n + J) - b^4 * J ≤ e' n ∧ e' n ≤ b^4 * e n := by
      let P : Density := ⟨D.spiralField M n q, fun x =>
        (rotate_posSemidef _ hM).smul (RCLike.nonneg_iff.mpr
          ⟨(cutoff_bounds D n x).1, by simp⟩ : (0:ℂ) ≤ (D.cutoff n x : ℂ))⟩
      let d := coulombStateDilation P.matrix b hb
      have hL (Γ) (hΓ : feasible P.matrix Γ) : -(J*D.vol n) ≤ indirectAt P.matrix Γ := by
        apply le_trans _ (lo P Γ hΓ)
        have hm := mul_le_mul_of_nonneg_left (moment_bound D n hM q) hc
        dsimp [J, P, Density.charge]
        linarith
      obtain ⟨h1,h2⟩ := finite_coordinate_scaling hb hb' d (represented n) hL
      change b^2 * D.totalEnergy energy M n q - (b-b^2)*(J*D.vol n) ≤ energy _ at h1
      change energy _ ≤ b * D.totalEnergy energy M n q at h2
      rw [← hfield n] at h1 h2
      change _ ≤ D'.totalEnergy energy (α • M) n (b • q) at h1
      change D'.totalEnergy energy (α • M) n (b • q) ≤ _ at h2
      have hv := D.vol_pos n
      change b^5 * (D.totalEnergy energy M n q / D.vol n + J) - b^4*J ≤
        D'.totalEnergy energy (α • M) n (b • q) / D'.vol n ∧
        D'.totalEnergy energy (α • M) n (b • q) / D'.vol n ≤ b^4*(D.totalEnergy energy M n q / D.vol n)
      rw [hvol]
      change _ ≤ D'.totalEnergy energy (α • M) n (b • q) / (D.vol n / b^3) ∧
        D'.totalEnergy energy (α • M) n (b • q) / (D.vol n / b^3) ≤ _
      constructor
      · field_simp [hv.ne', hb.ne']
        nlinarith only [h1]
      · field_simp [hv.ne', hb.ne']
        exact h2
    have hl := le_of_tendsto_of_tendsto' ((((he.add_const J).const_mul (b^5)).sub_const (b^4*J)))
      he' (fun n => (hfinite n).1)
    have hu := le_of_tendsto_of_tendsto' he' (he.const_mul (b^4)) (fun n => (hfinite n).2)
    rw [← h4, ← h5]
    exact ⟨by simpa only [J, mul_assoc] using hl, hu⟩
  · have hz := hM.trace_eq_zero_iff.mp (Complex.ext (le_antisymm (le_of_not_gt hr) htrace.1) htrace.2)
    subst M
    simp [hvac, Real.zero_rpow (by norm_num : (4/3 : ℝ) ≠ 0)]

end TSGA.ManyBody
