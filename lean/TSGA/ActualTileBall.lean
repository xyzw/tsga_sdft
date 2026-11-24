import TSGA.ActualTileCutoffs

/-! # Comparing centered cutoff averages with integrals on the comparison ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Metric Set

theorem actual_cutoff_average_ball (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (side : CutoffSide)
    {ε : ℝ} (he : 0 < ε) (he' : ε < 1) {u : Position → ℝ} (hu : Integrable u)
    (hpos : ∀ᵐ x, 0 ≤ u x) (c : Position) :
    let T := actualTiles O frames η side he he'
    Integrable (fun x => u x * T.cutoffProfile (c-x)) ∧
    cutoffAverage T.cutoffProfile u c ≤ 192*ε^3*(∫ x in closedBall c (3*ε⁻¹), u x) := by
  intro T
  let B := 192/(ε⁻¹)^3
  let μ := tileDilationLaw.prod O.law
  let : IsProbabilityMeasure μ := (inferInstance : IsProbabilityMeasure (tileDilationLaw.prod O.law))
  let k : (ℝ × O.Frames) → Position → ℝ := fun (i : ℝ × O.Frames) z => actualTileWeight ε⁻¹ i.1 * actualTileShape O η side ε⁻¹ i z
  have hm : Measurable (Function.uncurry k) :=
    (((measurable_actualTileWeight _).comp measurable_fst).comp measurable_fst).mul
      (measurable_actualTileShape O frames η side ε⁻¹)
  have km : Measurable T.cutoffProfile := by
    change Measurable (fun z => ∫ i, k i z ∂μ)
    exact hm.stronglyMeasurable.integral_prod_left.measurable
  have bound (z : Position) : T.cutoffProfile z ∈ Icc 0 B := by
    change (∫ i, k i z ∂μ) ∈ Icc 0 B
    have hs' (i : ℝ × O.Frames) : actualTileShape O η side ε⁻¹ i z ∈ Icc 0 1 := smoothedIndicator_bounds _ _ (tileDilation_pos i.1) _
    have hw (i : ℝ × O.Frames) := actualTileWeight_nonneg (inv_pos.mpr he).le i.1
    have ik : Integrable (fun i => k i z) μ := T.profile_integrable z
    refine ⟨integral_nonneg (fun i => mul_nonneg (hw i) (hs' i).1),?_⟩
    have h := integral_mono ik (integrable_const (μ := μ) B)
      (fun i => (mul_le_of_le_one_right (hw i) (hs' i).2).trans (actualTileWeight_bound (inv_pos.mpr he) _))
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hz (x : Position) (hx : x ∉ closedBall c (3*ε⁻¹)) : T.cutoffProfile (c-x) = 0 := by
    change (∫ i : ℝ × O.Frames, T.weight i * T.shape i (c-x) ∂μ) = 0
    simp only [show ∀ i : ℝ × O.Frames, T.shape i (c-x) = 0 from fun i => actualTiles_supported O frames η hs side he he' c i x hx,
      mul_zero,integral_zero]
  have hM : AEStronglyMeasurable (fun x => u x * T.cutoffProfile (c-x)) volume :=
    hu.1.mul (km.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hi : Integrable (fun x => u x * T.cutoffProfile (c-x)) := (hu.norm.mul_const B).mono' hM
    (ae_of_all _ fun x => by
      rw [norm_mul,Real.norm_of_nonneg (bound _).1]
      exact mul_le_mul_of_nonneg_left (bound _).2 (norm_nonneg _))
  refine ⟨hi,?_⟩
  change (∫ x, u x*T.cutoffProfile (c-x)) ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall c (3*ε⁻¹))
    (fun x hx => by rw [hz x hx,mul_zero])]
  calc
    _ ≤ ∫ x in closedBall c (3*ε⁻¹), u x * B := integral_mono_ae hi.integrableOn
      (hu.mul_const B).integrableOn (ae_restrict_of_ae (hpos.mono fun x hx => mul_le_mul_of_nonneg_left (bound _).2 hx))
    _ = _ := by rw [integral_mul_const]; simp only [B,div_eq_mul_inv,← inv_pow,inv_inv]; ring

end TSGA.ManyBody
