import TSGA.ActualTileLocalization
import TSGA.ActualTileFisher
import TSGA.CoulombPeriodicKernel
import TSGA.TetrahedronConeMeasure

/-! # Two-sided localization of the physical phase-rotated spin density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Metric Set

private theorem rotated_skeleton_overhead (H : FiniteEnergyInputs) {D : Density} {φ : Phase}
    {S Z : MatrixGradient} (hm : Integrable (massDensity D φ)) {c : ℝ} (hc : 0 ≤ c)
    (hz : sqrtKinetic Z ≤ 2*sqrtKinetic S+2*(∫ x, D.charge x*‖φ.grad x‖^2)) :
    let U := H.interiorConstant*(2^(2/3:ℝ)*(2*c)+8*c+16*c) + H.loCoeff*2^(4/3-1:ℝ)*(2*c)
    variableWindowCost H (rotatedDensity D φ) Z 2 (2*c) (8*c) ≤
      U*((∫ x, massDensity D φ x)+sqrtKinetic S) := by
  intro U
  let M := ∫ x, massDensity D φ x
  let J := M+sqrtKinetic S
  have kin : 0 ≤ sqrtKinetic S := integral_nonneg fun x => sq_nonneg _
  have mj : M ≤ J := le_add_of_nonneg_right kin
  have kin' : sqrtKinetic Z ≤ 2*J := by
    have hp : (∫ x, D.charge x*‖φ.grad x‖^2) ≤ M := integral_mono_of_nonneg
      (ae_of_all _ fun x => mul_nonneg (D.charge_nonneg _) (sq_nonneg _)) hm
      (ae_of_all _ fun x => by dsimp [massDensity]; linarith [D.charge_nonneg x,sq_nonneg (D.charge x)])
    dsimp [J]
    linarith
  have mass : (∫ x, D.charge x) ≤ J := by
    apply le_trans _ mj
    apply integral_mono_of_nonneg (ae_of_all _ D.charge_nonneg) hm
    exact ae_of_all _ fun x => by
      unfold massDensity
      linarith only [sq_nonneg (D.charge x),mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)]
  have pow (a : ℝ) (h : a ∈ Icc 1 2) : chargeMoment D a ≤ J := by
    apply le_trans _ mj
    apply integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg (D.charge_nonneg x) _) hm
    apply ae_of_all
    intro x
    apply le_trans _ (le_add_of_nonneg_right (mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)))
    rcases (D.charge_nonneg x).eq_or_lt with e|e
    · simp [← e,Real.zero_rpow (show a ≠ 0 by linarith [h.1])]
    · exact BulkRegime.density_power_le e h
  simp only [variableWindowCost,chargeMoment,rotated_charge]
  change H.interiorConstant*(2^(2/3:ℝ)*(2*c*chargeMoment D (5/3))+2*(2*c*sqrtKinetic Z)+
    2*(8*c*(∫ x, D.charge x))) + H.loCoeff*2^(4/3-1:ℝ)*(2*c*chargeMoment D (4/3)) ≤ U*J
  calc
    _ ≤ H.interiorConstant*(2^(2/3:ℝ)*(2*c*J)+2*(2*c*(2*J))+2*(8*c*J)) +
        H.loCoeff*2^(4/3-1:ℝ)*(2*c*J) := by
      gcongr <;> first | positivity [H.interiorConstant_nonneg,H.lo_nonneg] |
        exact pow _ (by constructor <;> norm_num)
    _ = U*J := by dsimp [U]; ring

/-- One pair of constants works for every admissible density, phase and
tile size. The upper family has the shrunken tetrahedron and the lower
family has the full tetrahedron. -/
theorem coulomb_actual_tile_localization (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (W : WindowSobolevRules)
    (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (tensor : DisjointFockTensorization) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (haar : CubeFrameInvariant O)
    {η : Mollifier} (hs : tsupport η.kernel ⊆ closedBall 0 (1/100)) (sk : SkeletonFisherAverages η)
    {A B C : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (hc : 0 ≤ C) (graf : SmearedGrafSchenker η O C)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B) :
    ∃ U ≥ 0, ∃ L ≥ 0, ∀ {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient},
      DensityRegular D p θ S T → φ.Regular p → (Integrable fun x => D.charge x*‖φ.grad x‖^2) →
      ∀ {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/2), C*ε ≤ 1/2 →
      let F := referenceEnergies energy η
      let T := fun s => actualTiles O frames η s he (lt_of_le_of_lt he' (by norm_num))
      rotatedEnergy F D φ ≤ (∫ z, (T .upper).energy F D φ z) + ∫ x, tilingExterior D φ S ε U x ∧
      -rotatedEnergy F D φ ≤ (∫ z, -(T .lower).energy F D φ z) + ∫ x, tilingExterior D φ S ε L x := by
  let c := sk.coefficient
  let u := H.interiorConstant*(2^(2/3:ℝ)*(2*c)+8*c+16*c) + H.loCoeff*2^(4/3-1:ℝ)*(2*c)
  have c₀ : 0 ≤ c := sk.nonneg
  have u₀ : 0 ≤ u := by dsimp [u]; positivity [H.interiorConstant_nonneg,H.lo_nonneg]
  obtain ⟨b,b₀,global⟩ := H.rotated_bound chain
  refine ⟨u+54*A*B,by positivity,2*C*(b+10),by positivity,?_⟩
  intro D φ p θ S T hD hφ phase ε he he' small
  let R := rotatedDensity D φ
  obtain ⟨Z,domain,kin⟩ := rotated_tileDensityDomain chain hD hφ phase
  obtain ⟨K,k₀,area⟩ := tileCutoffAreaBound_of_sobolev sob quant η
  have e1 : ε < 1 := by linarith
  have hm : Integrable (massDensity D φ) := (hD.charge_L1.add hD.charge_L2.integrable_sq).add phase
  have hi := kineticDensity_integrable hD
  let F := referenceEnergies energy η
  let T' := fun s => actualTiles O frames η s he e1
  have eq (s : CutoffSide) (z : Position) : (T' s).energy F D φ z =
      ∫ p, actualTileWeight ε⁻¹ p.1 * actualWindowEnergy O η s ε⁻¹ R p z ∂(tileDilationLaw.prod O.law) := rfl
  change rotatedEnergy F D φ ≤ _ ∧ -rotatedEnergy F D φ ≤ _
  constructor
  · change energy R.matrix ≤ (∫ z, (T' .upper).energy F D φ z) + _
    simp_rw [eq]
    rw [integral_tilingExterior ε _ hm hi]
    have upper := actual_upper_localization H product W lsc tensor O frames haar k₀ area sk hs
      tetrahedronCone η.periodicKernelCalculus ha hb transport fourier domain he he'
    apply upper.trans
    have skcost := rotated_skeleton_overhead H hm c₀ kin
    have q : (∫ x, R.charge x^2) ≤ (∫ x, massDensity D φ x)+sqrtKinetic S := by
      apply le_trans _ (le_add_of_nonneg_right (integral_nonneg fun x => sq_nonneg (matrixGradNorm S x)))
      apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hm
      exact ae_of_all _ fun x => by
        simp only [R,rotated_charge,massDensity]
        linarith only [D.charge_nonneg x,mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)]
    have csk := mul_le_mul_of_nonneg_left skcost he.le
    have cq := mul_le_mul_of_nonneg_left q (show 0 ≤ 54*A*B*ε by positivity)
    dsimp only [c,u,R,sqrtKinetic] at *
    linarith only [csk,cq]
  · let G := actualTetrahedralCutoffs O frames η sob k₀ area .lower he e1
    refine G.lower_localization (F := F) (D := D) (φ := φ) (S := S) he hc b₀ small hm hi ?_
      ((le_abs_self _).trans (global hD hφ phase))
    have lower := actual_lower_localization H product W (levyLiebBorel_of_lowerSemicontinuous lsc)
      O frames k₀ area hc graf domain he e1 small
    have corr : G.lowerCorrection D C = ∫ t, lowerTilingError R ε C (tileDilation t) ∂tileDilationLaw := by
      change (∫ p : ℝ × O.Frames, lowerTilingError D ε C (tileDilation p.1) ∂tileDilationLaw.prod O.law) = _
      rw [integral_fun_fst (fun t => lowerTilingError D ε C (tileDilation t))]
      simp only [probReal_univ,one_smul,lowerTilingError,R,rotated_charge]
    rw [corr]
    exact lower

end TSGA.ManyBody
