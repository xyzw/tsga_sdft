import TSGA.CoulombCenterIntegrability
import TSGA.CoulombVarianceIntegrability
import TSGA.CoulombShiftIntegrability

/-! # Finite translation integrals for the physical upper trial -/

noncomputable section
namespace TSGA.ManyBody
open SSW MeasureTheory Metric Set TSGA.Localization
open scoped ComplexOrder

/-- In a fixed translation cube only finitely many bulk energies survive.
The uniform local kinetic bound controls these terms, and the mean Fisher
bound gives an integrable majorant for the skeleton. -/
theorem coulomb_lattice_shift_integrals (borel : LevyLiebBorel) (H : FiniteEnergyInputs)
    (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients) {η : Mollifier}
    (S : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {Ω : Set Position} (hop : IsOpen Ω) (hb : Bornology.IsBounded Ω) (χ : Mollifier)
    {e : ℝ} (he : 0 < e) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {b d : ℝ} (hd : 0 < d) (hsc : d ≤ b/2) (R : Position ≃ₗᵢ[ℝ] Position) :
    let D := cutoffSpiral (smoothedIndicator Ω χ e) M q
    Integrable (latticeBlockEnergySum b d η R D) (latticeShiftMeasure b) ∧
      Integrable (fun τ => energy (latticeBlockDensity b d η R D τ none)) (latticeShiftMeasure b) := by
  classical
  let f := smoothedIndicator Ω χ e
  intro D
  have hbpos : 0 < b := by linarith
  let : IsProbabilityMeasure (latticeShiftMeasure b) := latticeShiftMeasure_probability hbpos
  obtain ⟨hmD,hiD,⟨B,hB⟩,hr⟩ := cutoffSpiral_source_data hop.measurableSet hb χ he M q
  have hχ : Integrable (Ω.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hop.measurableSet).2 (integrableOn_const hb.measure_lt_top.ne)
  have fi : Integrable f := hχ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (χ.scaled_integrable he)
  have hf := smoothedIndicator_bounds Ω χ he
  obtain ⟨g,df,gf⟩ := smoothedIndicator_sqrt_sobolev sob hop.measurableSet hb.measure_lt_top.ne χ he
  obtain ⟨G,hG,hup⟩ := (skeleton_shift_bounds H W S hs hf fi g gf df hM q hd hsc R).2.1
  have sk := latticeBlock_integrable_of_upper borel hd hsc hs R hmD hiD none hr hG hup
  obtain ⟨C,hC⟩ := H.centered_window_bounded_above W sob η (show 0 < b-d by linarith) hd hf fi g gf df hM q
  let E := fun p τ => energy (latticeBlockDensity b d η R D τ (some p))
  have hbulk (p : LatticeTile) : Integrable (E p) (latticeShiftMeasure b) := by
    apply latticeBlock_integrable_of_upper borel hd hsc hs R hmD hiD _ hr (integrable_const C)
    apply ae_of_all
    intro τ
    let z := R.symm (latticeShift b p.1+τ+cubeLabelCenter b p.2)
    have heq : latticeBlockDensity b d η R D τ (some p) =
        cutoffSpiral (fun x => f x * centeredWindow η (b-d) d (R.trans (cubeFrame b p.2)) z x) M q := by
      funext x
      simp only [D,latticeBlockDensity,latticeBlock,cutoffSpiral,smul_smul,Complex.ofReal_mul,
        latticeWindow_centered,z,f]
      rw [mul_comm]
    rw [heq]
    exact hC _ z
  obtain ⟨T,hT⟩ := latticeWindow_finite_range hbpos hd hs B
  refine ⟨(sk.add (integrable_finsetSum T (fun p _ => hbulk p))).congr ?_,sk⟩
  filter_upwards [ae_latticeShift_mem b] with τ hτ
  apply congrArg (energy (latticeBlockDensity b d η R D τ none)+·)
  refine (tsum_eq_sum (s := T) (fun p hp => ?_)).symm
  change energy (latticeBlockDensity b d η R D τ (some p)) = 0
  suffices h : latticeBlockDensity b d η R D τ (some p) = 0 by rw [h,energy_vacuum]
  funext x
  by_cases hx : D x = 0
  · simp [latticeBlockDensity,hx]
  · simp [latticeBlockDensity,latticeBlock,hT R τ hτ x (hB x hx) p hp]

/-- All finite-tiling integrability requirements for a smoothed physical
spiral on a bounded open set follow from the ordinary Sobolev and Fock
inputs, the measurable Haar action, and the scalar skeleton Fisher bound. -/
theorem coulomb_lattice_integrals (O : TileOrientationLaw) (action : MeasurableFrameAction O)
    (haar : CubeFrameInvariant O) (borel : LevyLiebBorel) (H : FiniteEnergyInputs)
    (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients) {η : Mollifier}
    (S : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {Ω : Set Position} (hop : IsOpen Ω) (hb : Bornology.IsBounded Ω) (χ : Mollifier)
    {e : ℝ} (he : 0 < e) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2) :
    CoulombLatticeIntegrals O η (smoothedIndicator Ω χ e) M q ℓ δ := by
  let D := cutoffSpiral (smoothedIndicator Ω χ e) M q
  obtain ⟨hm,hi,hB,hr⟩ := cutoffSpiral_source_data hop.measurableSet hb χ he M q
  have hmρ : Measurable (fun x => (D x).trace.re) :=
    Complex.measurable_re.comp (Finset.measurable_fun_sum _ (fun i _ => hm i i))
  have variance := lattice_variance_integrable O action hs hδ hsc hmρ hr
  have tpos {t : ℝ} (ht : t ∈ scaleInterval) : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) ht.1
  have hd {t : ℝ} (ht : t ∈ scaleInterval) : 0 < t*δ := mul_pos (tpos ht) hδ
  have sc {t : ℝ} (ht : t ∈ scaleInterval) : t*δ ≤ t*ℓ/2 := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hsc (tpos ht).le
  have center (t : ℝ) (ht : t ∈ scaleInterval) :=
    coulomb_center_integrals H W sob borel O action haar hop hb χ he η (hd ht)
      (show t*δ<t*ℓ by linarith [sc ht, hd ht]) hM q
  exact ⟨hm, hi, hB, hr, fun t ht R =>
    coulomb_lattice_shift_integrals borel H W sob S hs hop hb χ he hM q (hd ht) (sc ht) R,
    fun t ht => (center t ht).1, fun t ht => (center t ht).2.1, fun t ht => (center t ht).2.2,
    variance.1, variance.2⟩

end TSGA.ManyBody
