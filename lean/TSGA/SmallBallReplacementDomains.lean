import TSGA.SmallBallReplacementFisher
import TSGA.LargeTileTrials

/-! # Root regularity and form domains for a frozen spin frame -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Set Metric Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

theorem referenceDensity_charge (N : Density) (c x : Position) :
    (referenceDensity N c).charge x = N.charge x := by
  simp only [Density.charge, referenceDensity, SpectralExtrema.referenceFrame, inSpinFrame_trace]
  rw [(N.positive x).1.trace_eq_sum_eigenvalues]
  simp [Fin.sum_univ_two]

private theorem referenceDensity_power (N : Density) (c x : Position) (a : ℝ) :
    (referenceDensity N c).power a x = inSpinFrame (N.positive c).1.eigenvectorUnitary
      (fun i => (N.positive x).1.eigenvalues i ^ a) := by
  unfold Density.power
  exact inSpinFrame_cfc _ _ _ _

theorem referenceDensity_sqrt_regular (sob : SobolevLipschitzComposition) {N : Density} {S : MatrixGradient}
    (reg : SqrtRegular N S) (c : Position) :
    ∃ Z : MatrixGradient, SqrtRegular (referenceDensity N c) Z ∧
      ∀ᵐ x, kineticDensity Z x ≤ kineticDensity S x := by
  let D := referenceDensity N c
  have lip (x y : Position) :
      hilbertSchmidt (D.power (1/2) x - D.power (1/2) y) ≤ 1*hilbertSchmidt (N.power (1/2) x-N.power (1/2) y) := by
    have h := eigenvalue_distances_le_hs (N.positive x) (N.positive y) (f := fun t => t^(1/2:ℝ))
      (fun a ha _ _ h => Real.rpow_le_rpow ha h (by norm_num))
    rw [one_mul]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    change hilbertSchmidt ((referenceDensity N c).power (1/2) x-(referenceDensity N c).power (1/2) y)^2 ≤ hilbertSchmidt (N.power (1/2) x-N.power (1/2) y)^2
    rw [referenceDensity_power, referenceDensity_power, inSpinFrame_sub, inSpinFrame_hs]
    simpa only [Fin.sum_univ_two, Pi.sub_apply, Density.power] using h
  obtain ⟨Z, weak, meas, bound⟩ := sob _ _ _ 1 zero_le_one lip reg.weak
  have hz : ∀ᵐ x, matrixGradNorm Z x ≤ matrixGradNorm S x := by simpa only [one_mul] using bound
  have hz₂ : ∀ᵐ x, kineticDensity Z x ≤ kineticDensity S x :=
    hz.mono fun _ hx => pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
  refine ⟨Z, ⟨?_, weak, reg.grad.mono meas ?_⟩,hz₂⟩
  · change Integrable (fun x => (referenceDensity N c).charge x)
    simpa only [referenceDensity_charge] using reg.charge
  · exact hz.mono fun x hx => by simpa only [Real.norm_of_nonneg (show 0 ≤ matrixGradNorm Z x from Real.sqrt_nonneg _), Real.norm_of_nonneg (show 0 ≤ matrixGradNorm S x from Real.sqrt_nonneg _)] using hx

theorem continuous_referenceDensity {N : Density} (c : Position) (hc : Continuous (N.power 1)) :
    Continuous (referenceDensity N c).matrix := by
  have he (i) : Continuous (fun x => ((N.positive x).1.eigenvalues i : ℂ)) := by
    have h := spinEigenvalue_power_continuousOn (K := univ) N zero_le_one hc.continuousOn i
    have hc' : Continuous (fun x => (N.positive x).1.eigenvalues i ^ (1:ℝ)) := continuousOn_univ.mp h
    simpa only [Real.rpow_one,Function.comp_def] using Complex.continuous_ofReal.comp hc'
  change Continuous fun x => inSpinFrame _ ((N.positive x).1.eigenvalues)
  unfold inSpinFrame
  simp only [Unitary.conjStarAlgAut_apply]
  apply Continuous.mul _ continuous_const
  apply Continuous.mul continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases e : i=j
  · subst j
    simpa [Matrix.diagonal_apply] using he i
  · simpa [Matrix.diagonal_apply,e] using (continuous_const (X := Position) (y := (0:ℂ)))

/-- A spatial window of finite support and a continuous spin field have all
the deterministic L¹ and L² domain properties needed by the island trial. -/
theorem taper_domain {K : Set Position} (hK : IsCompact K) (t : SpiralTaper K)
    (hc : Continuous t.shape) (A B : Density) (ha : Continuous A.matrix) (hb : Continuous B.matrix)
    (order : ∀ x ∈ K, A.matrix x ≤ B.matrix x) : IslandDensityDomain (t.field A) (t.residual A B order) := by
  let D := t.field A
  let E := t.residual A B order
  have smooth (M : Position → SpinMatrix) (hm : Continuous M) (i j : Fin 2) :
      Continuous (fun x => SSW.cutoffSpiral t.shape (M x) t.wavevector x i j) := by
    simp only [SSW.cutoffSpiral, Matrix.smul_apply, smul_eq_mul, rotate_by_entry]
    unfold phaseFactor
    fun_prop
  have d (i j : Fin 2) : Continuous (fun x => D.matrix x i j) := smooth _ ha i j
  have e (i j : Fin 2) : Continuous (fun x => E.matrix x i j) := smooth _ (hb.sub ha) i j
  have dc : Continuous D.charge := by
    unfold Density.charge Matrix.trace
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => d i i)
  have ec : Continuous E.charge := by
    unfold Density.charge Matrix.trace
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => e i i)
  have supp (f : Position → ℝ) (h : ∀ x ∉ K, f x = 0) : HasCompactSupport f :=
    hK.of_isClosed_subset (isClosed_tsupport f) (closure_minimal (fun x hx => by by_contra hn; exact hx (h x hn)) hK.isClosed)
  have ds := supp D.charge (fun x hx => by simp [D,t.field_charge,t.outside x hx])
  have es := supp E.charge (fun x hx => by simp [E, Density.charge, SpiralTaper.residual, SSW.cutoffSpiral,t.outside x hx])
  exact IslandDensityDomain.of_L1_L2 dc.measurable ec.measurable (fun i j => (d i j).aestronglyMeasurable)
    (fun i j => (e i j).aestronglyMeasurable) (dc.integrable_of_hasCompactSupport ds) (ec.integrable_of_hasCompactSupport es)
    (dc.memLp_of_hasCompactSupport ds) (ec.memLp_of_hasCompactSupport es)

/-- Cost after weighting the unrotated Fisher estimate by the taper and
conjugating by the plane wave. The charge cap occurs only in the Fisher
boundary cost and the mass rotated into the spiral. -/
def affineSpiralKinetic {K : Set Position} (t : SpiralTaper K) (S : MatrixGradient)
    (g : Position → Position) (a cap : ℝ) : ℝ :=
  8*(a*(∫ x, t.shape x*kineticDensity S x) + cap*(∫ x in K, ‖g x‖^2)) +
    2*‖t.wavevector‖^2*cap*(∫ x, t.shape x)

theorem SpiralTaper.affine_spiral_regular {K : Set Position} (t : SpiralTaper K) (hK : IsCompact K)
    (F : FisherSobolevCalculus) (chain : WeakPhaseProduct)
    {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S) (cont : Continuous D.matrix)
    {b a δ cap : ℝ} {A : SpinMatrix} (pos : ∀ x ∈ K, (b • D.matrix x + A).PosSemidef)
    (order : ∀ x ∈ K, δ • D.matrix x ≤ b • D.matrix x + A) (hd : 0 ≤ δ) (hb : b^2 ≤ a*δ) (ha : 0 ≤ a)
    (charge : ∀ x ∈ K, (b • D.matrix x + A).trace.re ≤ cap)
    (lip : LocallyLipschitz fun x => √(t.shape x)) (g : Position → Position)
    (weak : ∀ i, WeakPartialOn univ i (fun x => √(t.shape x)) (fun x => g x i))
    (shape : Continuous t.shape) (ishape : Integrable t.shape)
    (fish : Integrable (K.indicator (fun x => ‖g x‖^2))) :
    let N := t.affineDensity D b A pos
    ∃ Z, SqrtRegular (rotatedDensity N (frozenLinearPhase t.wavevector)) Z ∧
      sqrtKinetic Z ≤ affineSpiralKinetic t S g a cap := by
  intro N
  have m (x) : N.charge x = t.shape x * (b • D.matrix x + A).trace.re := by
    simp [N, SpiralTaper.affineDensity, Density.charge, Matrix.trace_smul, Complex.real_smul, mul_add]
  have hc : Continuous N.charge := by
    simp_rw [show N.charge = _ from funext m]
    fun_prop
  have cap' (x) : N.charge x ≤ cap*t.shape x := by
    rw [m,mul_comm cap]
    by_cases hx : x ∈ K
    · exact mul_le_mul_of_nonneg_left (charge x hx) (t.range x).1
    · simp [t.outside x hx]
  have mass : Integrable N.charge := (ishape.const_mul cap).mono' hc.aestronglyMeasurable
    (ae_of_all _ fun x => (Real.norm_of_nonneg (N.charge_nonneg x)).le.trans (cap' x))
  obtain ⟨r, cost⟩ := t.affine_sqrt_regular hK.isClosed.measurableSet F reg pos order hd hb ha charge lip g weak mass
    shape.aemeasurable fish
  let q := t.wavevector
  let φ := frozenLinearPhase q
  have kin : Integrable (fun x => N.charge x * ‖φ.grad x‖^2) := by
    change Integrable (fun x => N.charge x*‖q‖^2)
    exact mass.mul_const _
  obtain ⟨Z, w, lp, h⟩ := rotated_sqrt_kinetic_of_weak chain r.weak r.grad (frozenLinearPhase_regular q) kin
  have er : (rotatedDensity N φ).charge = N.charge := funext (rotated_charge N φ)
  refine ⟨Z, ⟨er.symm ▸ r.charge, w, lp⟩, ?_⟩
  have hm := integral_mono mass (ishape.const_mul cap) cap'
  rw [integral_const_mul] at hm
  change sqrtKinetic Z ≤ 2*sqrtKinetic (F.gradient N)+2*(∫ x, N.charge x*‖q‖^2) at h
  rw [integral_mul_const] at h
  apply h.trans
  unfold affineSpiralKinetic
  nlinarith only [cost,mul_le_mul_of_nonneg_right hm (sq_nonneg ‖q‖)]
end TSGA.ManyBody
