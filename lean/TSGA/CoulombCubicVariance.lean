import TSGA.CoulombShellTransport
import TSGA.CoulombUpperTrialAssembly
import TSGA.CoulombFiniteLocalization

/-! # Quantitative Coulomb tiling from periodic transport and Fock products -/

noncomputable section
namespace TSGA.ManyBody
open SSW MeasureTheory Set Metric Skeleton
open scoped ComplexOrder

/-- Rotational and dilation average for an arbitrary unit-periodic charge
profile f. Its scale in physical coordinates is tℓ. -/
def periodicCoulombVariance (O : TileOrientationLaw) (f charge : Position → ℝ) (ℓ t : ℝ) : ℝ :=
  ∫ u, ∫ τ, hartree (fun x => f ((t*ℓ)⁻¹ • (O.frame u x-τ))*charge x)
    ∂latticeShiftMeasure (t*ℓ) ∂O.law

/-- The standard Fourier bound of Lewin–Lieb–Seiringer, Eqs. (41)–(43)
and Lemma 14. Its input is any bounded mean-zero periodic function. -/
def CoulombFourierAveraging (O : TileOrientationLaw) (B : ℝ) : Prop :=
  ∀ (f : Position → ℝ), unitPeriodic f → AEStronglyMeasurable f volume →
    (∃ N : ℝ, ∀ x, |f x| ≤ N) → (∫ x in latticeCube 1 0, f x) = 0 →
    ∀ charge : Position → ℝ, Integrable charge → Integrable (fun x => charge x^2) →
    ∀ {ℓ α : ℝ}, 0 < ℓ → 0 < α → α < 1/2 →
    scaleAverageAt α (periodicCoulombVariance O f charge ℓ) ≤
      B*Real.log α⁻¹*ℓ^2 * periodicNegativeNorm f * (∫ x, charge x^2)

/-- Bound for the physical Hartree variance of the translated tensor products.
The coefficient contains no tile-size, density, wavevector or smoothing-width dependence. -/
theorem coulomb_variable_cubic_variance (O : TileOrientationLaw) {η : Mollifier}
    (C : TetrahedronCone) (K : PeriodicKernelCalculus η)
    (hk : tsupport η.kernel ⊆ closedBall 0 (1/100)) {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    (charge : Position → ℝ) (hc : Integrable charge) (hc2 : Integrable (fun x => charge x^2))
    {ℓ δ α : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2) (hα : 0 < α) (hu : α < 1/2) :
    scaleAverageAt α (latticeVariance O η charge ℓ δ) ≤
      (54*A*B*(δ^3/ℓ))*(∫ x, charge x^2)*Real.log α⁻¹ := by
  classical
  let s := δ/ℓ
  have hℓ : 0 < ℓ := by linarith
  have hs : 0 < s := div_pos hδ hℓ
  have hhalf : s ≤ 1/2 := (div_le_iff₀ hℓ).mpr (by linarith)
  let f := fun x => latticeTotalWindow 1 s η x - 1
  have hp : unitPeriodic f := by
    intro m x
    change ((∑' p, latticeWindow 1 s η p (latticeShift 1 m+x)) +
      _*(1-∑' p, latticeWindow 1 (s/2) η p (latticeShift 1 m+x))) - 1 = _
    rw [latticeWindow_periodic,latticeWindow_periodic]
    rfl
  let w (r : ℝ) := smoothedIndicator (latticeShell 1 r) η r
  have heq (x) : f x = shellCoefficient s * w (s/2) x - w s x := by
    simpa only [f,w,latticeTotalWindow,div_one] using (lattice_charge_shells (by norm_num : (0:ℝ)<1) hs η x)
  have hwm {r : ℝ} (hr : 0 < r) : AEStronglyMeasurable (w r) volume :=
    (K.convolution _ (latticeShell_measurable _ _) (fun m x => latticeShell_mem_shift m x) hr).1
  have hfm : AEStronglyMeasurable f volume := by
    simp_rw [show f = _ from funext heq]
    exact ((hwm (half_pos hs)).const_mul _).sub (hwm hs)
  have hbound : ∃ N : ℝ, ∀ x, |f x| ≤ N := by
    refine ⟨3,fun x => ?_⟩
    rw [heq]
    have a := smoothedIndicator_bounds (latticeShell 1 s) η hs x
    have b := smoothedIndicator_bounds (latticeShell 1 (s/2)) η (half_pos hs) x
    have c := shellCoefficient_bounds hs hhalf
    change w s x ∈ Icc 0 1 at a
    change w (s/2) x ∈ Icc 0 1 at b
    have h := mul_le_mul c.2 b.2 b.1 (by norm_num)
    exact abs_le.mpr ⟨by linarith only [mul_nonneg c.1 b.1,a.2], by linarith only [h,a.1]⟩
  have hm : (∫ x in latticeCube 1 0, latticeTotalWindow 1 s η x) = 1 := by
    simpa [latticeTotalWindow] using latticeWindow_cube_integral hs hhalf ((subset_tsupport _).trans hk)
  have v : volume.real (latticeCube 1 0) = 1 := by
    simpa [regionVolume] using latticeCube_volume (by norm_num : (0:ℝ)<1) 0
  have hzero : (∫ x in latticeCube 1 0, f x) = 0 := by
    have vf : volume (latticeCube 1 0) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp (show 0 < volume.real (latticeCube 1 0) by rw [v]; norm_num)).2.ne
    rw [show (∫ x in latticeCube 1 0, f x) = _ from integral_sub
      (Integrable.of_integral_ne_zero (hm.trans_ne one_ne_zero)) (integrableOn_const vf), hm]
    simp [v]
  have scale {t : ℝ} (ht : 0 < t) (x : Position) :
      latticeTotalWindow (t*ℓ) (t*δ) η x-1 = f ((t*ℓ)⁻¹ • x) := by
    have h := lattice_fluctuation_dilate (mul_pos ht hℓ) 1 s η ((t*ℓ)⁻¹ • x)
    simpa only [f,latticeTotalWindow,mul_one,show (t*ℓ)*s = t*δ by dsimp [s]; field_simp,
      smul_inv_smul₀ (mul_pos ht hℓ).ne'] using h
  have rewrite_var : scaleAverageAt α (latticeVariance O η charge ℓ δ) =
      scaleAverageAt α (periodicCoulombVariance O f charge ℓ) := by
    unfold scaleAverageAt
    apply congrArg (fun a : ℝ => a / (∫ t in Icc (1 - α) (1 + α), scaleWeight t))
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have ht' : 0 < t := by linarith [ht.1]
    unfold latticeVariance periodicCoulombVariance
    simp_rw [scale ht']
  have h := fourier f hp hfm hbound hzero charge hc hc2 hℓ hα hu
  rw [rewrite_var]
  apply h.trans
  have hlog : 0 ≤ Real.log α⁻¹ := Real.log_nonneg ((one_le_inv₀ hα).mpr (by linarith))
  have hnorm := physical_lattice_negative_norm C K hk ha transport hs hhalf
  have hpos : 0 ≤ ∫ x, charge x^2 := integral_nonneg fun x => sq_nonneg (charge x)
  change periodicNegativeNorm f ≤ _ at hnorm
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ B*Real.log α⁻¹*ℓ^2 by positivity)) hpos).trans_eq
  rw [← skeleton_physical_scale hℓ]
  dsimp [s]
  ring

/-- Specialization to the smoothed constant charge of a finite gas sample. -/
theorem coulomb_lattice_cubic_variance (O : TileOrientationLaw) {η : Mollifier}
    (C : TetrahedronCone) (K : PeriodicKernelCalculus η)
    (hk : tsupport η.kernel ⊆ closedBall 0 (1/100)) {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B) :
    CoulombVarianceBound O η .cubic (54*A*B) := by
  classical
  intro Ω hop hbd χ d hd ρ hρ ℓ δ hδ hsc α hα hu charge
  have hi : Integrable (Ω.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hop.measurableSet).2 (integrableOn_const hbd.measure_lt_top.ne)
  have hi' : Integrable (smoothedIndicator Ω χ d) := hi.integrable_convolution _ (χ.scaled_integrable hd)
  have hc : Integrable charge := hi'.mul_const ρ
  have hc2 : Integrable (fun x => charge x^2) := (hc.mul_const ρ).mono' (hc.1.pow 2)
    (ae_of_all _ fun x => by
      have h := smoothedIndicator_bounds Ω χ hd x
      have h1 : 0 ≤ charge x := mul_nonneg h.1 hρ
      have h2 : charge x ≤ ρ := (mul_le_mul_of_nonneg_right h.2 hρ).trans_eq (one_mul _)
      rw [Real.norm_of_nonneg (sq_nonneg (charge x)),sq]
      exact mul_le_mul_of_nonneg_left h2 h1)
  exact coulomb_variable_cubic_variance O C K hk ha hb transport fourier charge hc hc2 hδ hsc hα hu

/-- All seven finite tiling comparisons, the Coulomb gas theorem, and the
finite tetrahedron rate at a common size threshold. The upper bound uses
the concrete lattice and the disjoint Fock construction. -/
theorem coulomb_sswGas_of_lattice_products {η : Mollifier} (H : FiniteEnergyInputs)
    (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients)
    (strong : SobolevDirectionalLimits) (lower : CoulombLowerLocalization η)
    (O : TileOrientationLaw) (haar : CubeFrameInvariant O) (tensor : DisjointFockTensorization)
    (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (hk : tsupport η.kernel ⊆ closedBall 0 (1/100)) (skeleton : SkeletonFisherAverages η)
    (C : TetrahedronCone) (K : PeriodicKernelCalculus η) {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    (regular : ∀ {Ω : Set Position}, IsOpen Ω → Bornology.IsBounded Ω → 0 < regionVolume Ω →
      ∀ (χ : Mollifier) {d : ℝ}, 0 < d → ∀ {M : SpinMatrix}, M.PosSemidef → ∀ q : Position,
      ∀ {ℓ δ : ℝ}, 0 < δ → δ ≤ ℓ/2 → CoulombLatticeIntegrals O η (smoothedIndicator Ω χ d) M q ℓ δ) :
    SSWGasTheorem (referenceEnergies energy η) ∧
      ∃ L ≥ H.roughThreshold sob strong.toDifferenceBounds η, CoulombTilingComparisons η L ∧
        FiniteRateTiling energy η L := by
  have variance : CoulombVarianceBound O η .cubic (54*A*B) :=
    coulomb_lattice_cubic_variance O C K hk ha hb transport fourier
  let upper := CoulombUpperLocalization.of_lattice H W sob strong.toDifferenceBounds O haar tensor
    lsc ((subset_tsupport _).trans hk) skeleton (by positivity : 0 ≤ 54*A*B) variance regular
  have borel := levyLiebBorel_of_lowerSemicontinuous lsc
  obtain ⟨L,hL,h⟩ := coulomb_finite_tiling_comparisons H sob strong.toDifferenceBounds borel lower upper
  exact ⟨coulomb_sswGas_of_finite_tilings H sob strong hL (h L le_rfl),
    L,hL,h L le_rfl,(h L le_rfl).rate H sob strong.toDifferenceBounds hL⟩

end TSGA.ManyBody
