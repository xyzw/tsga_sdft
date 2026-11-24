import TSGA.ActualTileAssembly
import TSGA.IntegratedScaleCost

/-! # Integration of the two signed physical Coulomb comparisons -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Set Metric

/-- Integrate the signed reference over the centers. The cutoff mass deficit
is included together with the exterior energy, and the error may depend on
the side of the tiling. -/
private theorem integrated_profile (P : TileProfile) {σ E : ℝ}
    {f err overhead : Position → ℝ} (hf : Integrable f) (hi : Integrable err)
    (ho : Integrable overhead)
    (gl : σ*E ≤ (∫ c, P.tileEnergy c) + ∫ x, P.exterior x)
    (loc : ∀ᵐ c, P.tileEnergy c ≤ σ*cutoffAverage P.cutoff f c + err c)
    (outside : ∀ᵐ x, P.exterior x + ((∫ z, P.cutoff z)-1)*(σ*f x) ≤ overhead x) :
    σ*(E - ∫ x, f x) ≤ (∫ x, overhead x) + ∫ c, err c := by
  let m := ∫ z, P.cutoff z
  have cInt := (cutoffAverage_integrable P.cutoff_integrable hf).const_mul σ
  have htile := integral_mono_ae P.tile_integrable (cInt.add hi) loc
  change (∫ c, P.tileEnergy c) ≤ ∫ c, σ*cutoffAverage P.cutoff f c + err c at htile
  rw [integral_add cInt hi,integral_const_mul,integral_cutoffAverage P.cutoff_integrable hf] at htile
  have dInt := (hf.const_mul σ).const_mul (m-1)
  have hcost := integral_mono_ae (P.exterior_integrable.add dInt) ho outside
  change (∫ x, P.exterior x + (m-1)*(σ*f x)) ≤ ∫ x, overhead x at hcost
  rw [integral_add P.exterior_integrable dInt,integral_const_mul,integral_const_mul] at hcost
  dsimp only [m] at hcost
  linarith only [gl,htile,hcost]

/-- The physical upper and lower bounds give a common small-scale constant
once their centerwise errors are integrable. The upper taper mass and the
exterior skeleton are paid through the cutoff control for its own family. -/
theorem actual_signed_global_bound_at_cost (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (tensor : DisjointFockTensorization)
    (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (haar : CubeFrameInvariant O)
    {η : Mollifier} (hs : tsupport η.kernel ⊆ closedBall 0 (1/100)) (sk : SkeletonFisherAverages η)
    {A B C A₀ : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (hc : 0 ≤ C) (graf : SmearedGrafSchenker η O C)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    (rough : APriori (referenceEnergies energy η) A₀) (hA₀ : 0 ≤ A₀) :
    ∃ M ≥ 1, ∀ {D : Density} {φ : Phase} {S T G : MatrixGradient} {p θ : ℝ} (mode : BulkRegime),
      3 < p → 0 < θ → DensityRegular D p θ S T → PhaseAdmissible D p φ G →
      ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), C*ε ≤ 1/2 → ∀ L total : ℝ,
        integratedScaleCost mode D φ S T G p θ ε ≤ total →
        let F := referenceEnergies energy η
        let tiles := fun side => actualTiles O frames η side he (by linarith)
        (∀ (side : CutoffSide) (P : TileProfile), P.cutoff = (tiles side).cutoffProfile →
          ∃ err : Position → ℝ, Integrable err ∧
            (∀ᵐ c, tileSign side*((tiles side).energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c) ≤ err c) ∧
            (∫ c, err c) ≤ L*total) →
        |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤
          (M+L)*total := by
  obtain ⟨J,hJ,profiles⟩ := coulomb_actual_signed_profiles H product chain W sob quant tensor lsc O frames haar
    hs sk ha hb hc graf transport fourier 0 0 (by norm_num)
  let M := 3*J+J*A₀
  have j₀ : 0 ≤ J := by linarith
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hJ,mul_nonneg j₀ hA₀]
  refine ⟨M,hM,?_⟩
  intro D φ S T G p θ mode hp hθ reg phase ε he hle cg L total cover F tiles localBound
  let ref := localEnergy F D φ
  have href : Integrable ref := rough.integrable_local hp hθ reg phase.regular phase.kinetic
  have hm := massDensity_integrable reg phase
  have hk := kineticDensity_integrable reg
  let over := fun x => M*(ε*massDensity D φ x + kineticDensity S x/ε)
  have oi : Integrable over := ((hm.const_mul ε).add (hk.div_const ε)).const_mul M
  have sum : (∫ x, over x) ≤ M*total := by
    dsimp only [over]
    rw [integral_const_mul,integral_add (hm.const_mul ε) (hk.div_const ε),integral_const_mul,integral_div]
    exact mul_le_mul_of_nonneg_left ((mass_kinetic_le_integratedScaleCost mode D φ S T G p θ he).trans cover)
      (zero_le_one.trans hM)
  have sideBound (side : CutoffSide) : tileSign side*(rotatedEnergy F D φ - ∫ x, ref x) ≤ (M+L)*total := by
    obtain ⟨P,_,cut,tile,kernel,volumeCost,_,control,global⟩ :=
      profiles J le_rfl reg phase.regular phase.kinetic he hle cg side
    obtain ⟨err,ei,point,integral⟩ := localBound side P cut
    have hsign : tileSign side = 1 ∨ tileSign side = -1 := by
      cases side <;> first | exact Or.inl rfl | exact Or.inr rfl
    have outside : ∀ᵐ x, P.exterior x + ((∫ z, P.cutoff z)-1)*(tileSign side*ref x) ≤ over x := by
      filter_upwards [control.bound rough he j₀ hA₀ hsign] with x hx
      simpa only [kernel,volumeCost,zero_mul,integral_zero,mul_zero,add_zero] using hx
    have loc : ∀ᵐ c, P.tileEnergy c ≤ tileSign side*cutoffAverage P.cutoff ref c + err c := by
      rw [tile]
      filter_upwards [point] with c h
      change tileSign side*((tiles side).energy F D φ c) ≤ tileSign side*cutoffAverage P.cutoff ref c + err c
      exact (sub_le_iff_le_add'.mp (by simpa only [mul_sub] using h))
    have h := integrated_profile P href ei oi global loc outside
    exact h.trans ((add_le_add sum integral).trans_eq (add_mul M L total).symm)
  refine abs_le.mpr ⟨?_,?_⟩
  · have hlo := sideBound .lower
    simp only [tileSign,neg_one_mul] at hlo
    linarith only [hlo]
  · simpa only [tileSign,one_mul] using sideBound .upper

/-- Use the integrated scale cost for the general, global-root and positive-minority bounds. -/
theorem actual_signed_global_bound (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (tensor : DisjointFockTensorization)
    (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (haar : CubeFrameInvariant O)
    {η : Mollifier} (hs : tsupport η.kernel ⊆ closedBall 0 (1/100)) (sk : SkeletonFisherAverages η)
    {A B C A₀ : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (hc : 0 ≤ C) (graf : SmearedGrafSchenker η O C)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    (rough : APriori (referenceEnergies energy η) A₀) (hA₀ : 0 ≤ A₀) :
    ∃ M ≥ 1, ∀ {D : Density} {φ : Phase} {S T G : MatrixGradient} {p θ : ℝ} (mode : BulkRegime),
      3 < p → 0 < θ → DensityRegular D p θ S T → PhaseAdmissible D p φ G →
      ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), C*ε ≤ 1/2 → ∀ L : ℝ,
        let F := referenceEnergies energy η
        let tiles := fun side => actualTiles O frames η side he (by linarith)
        (∀ (side : CutoffSide) (P : TileProfile), P.cutoff = (tiles side).cutoffProfile →
          ∃ err : Position → ℝ, Integrable err ∧
            (∀ᵐ c, tileSign side*((tiles side).energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c) ≤ err c) ∧
            (∫ c, err c) ≤ L*integratedScaleCost mode D φ S T G p θ ε) →
        |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤
          (M+L)*integratedScaleCost mode D φ S T G p θ ε := by
  obtain ⟨M,hM,bound⟩ := actual_signed_global_bound_at_cost H product chain W sob quant tensor lsc
    O frames haar hs sk ha hb hc graf transport fourier rough hA₀
  refine ⟨M,hM,?_⟩
  intro D φ S T G p θ mode hp hθ reg phase ε he hle cg L
  exact bound mode hp hθ reg phase he hle cg L _ le_rfl

end TSGA.ManyBody
