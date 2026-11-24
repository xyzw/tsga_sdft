import TSGA.ActualTileAssembly
import TSGA.CoulombFrozenTile

/-! # Finite-size comparison for a frozen physical tile

A rigid motion turns each translated spiral into the reference tetrahedron
with rotated wavevector. The weight uses the original cell volume, including
on the upper family where the cutoff occupies only the inner tetrahedron.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set SSW TSGA.Localization
open scoped ComplexOrder

private theorem frozen_rigid_motion (O : TileOrientationLaw) (η : Mollifier) (side : CutoffSide)
    {ε : ℝ} (he : 0 < ε) (hle : ε < 1) (B : SpinMatrix) (q c : Position) (i : ℝ × O.Frames) :
    actualTileWeight ε⁻¹ i.1 * energy (cutoffSpiral (fun x => actualTileShape O η side ε⁻¹ i (c-x)) B q) =
      side.mass ε * tileEnergy energy η B (tileDilation i.1*tileSideLength side ε⁻¹) (tileDilation i.1) (O.frame i.2 q) := by
  let t := tileDilation i.1
  let L := tileSideLength side ε⁻¹
  have ht : 0 < t := tileDilation_pos _
  have hL : 0 < L := tileSideLength_pos side he hle
  have cov := centered_energy η (t*L) t (O.frame i.2) c B q
  have hv := tetrahedron_volume_pos (mul_pos ht hL)
  have vol : actualTileWeight ε⁻¹ i.1 * regionVolume (tetrahedron (t*L)) = side.mass ε := by
    rw [tetrahedron_volume (mul_pos ht hL)]
    cases side <;> dsimp [L,t,tileSideLength,CutoffSide.mass,actualTileWeight] <;> field_simp [he.ne', (tileDilation_pos i.1).ne']
  rw [← cov, ← vol]
  have shape : (fun x => actualTileShape O η side ε⁻¹ i (c-x)) = centeredWindow η (t*L) t (O.frame i.2) c := by
    funext x
    simp [actualTileShape, centeredWindow, t, L]
  rw [shape]
  field_simp [hv.ne']

/-- The weighted frozen energy is integrable in the frame and dilation. Its
integral is the angular and dilation average at the physical side length. -/
theorem actual_frozen_average (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (side : CutoffSide) {ε K : ℝ} (he : 0 < ε) (hle : ε < 1)
    (rate : FiniteRateTiling energy η K) {B : SpinMatrix} (hB : B.PosSemidef) (q c : Position) :
    let T := actualTiles O frames η side he hle
    let L := tileSideLength side ε⁻¹
    T.FrozenIntegrable (referenceEnergies energy η) B q c ∧
      T.frozenEnergy (referenceEnergies energy η) B q c = side.mass ε *
        scaleAverage (fun t => averagedTile energy η B q (t*L) (t*1)) := by
  intro T L
  let F := fun i : ℝ × O.Frames => energy (cutoffSpiral (fun x => actualTileShape O η side ε⁻¹ i (c-x)) B q)
  let f := fun i : ℝ × O.Frames => actualTileWeight ε⁻¹ i.1 * F i
  let g := fun t => averagedTile energy η B q (tileDilation t*L) (tileDilation t)
  let m := side.mass ε
  have hm : 0 ≤ m := by cases side <;> dsimp [m,CutoffSide.mass] <;> positivity
  have hL : 0 < L := tileSideLength_pos side he hle
  have hρ : 0 ≤ B.trace.re := (RCLike.nonneg_iff.mp hB.trace_nonneg).1
  have sh : Measurable (fun a : (ℝ × O.Frames) × Position => actualTileShape O η side ε⁻¹ a.1 (c-a.2)) :=
    (measurable_actualTileShape O frames η side _).comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  have entries (j k : Fin 2) : Measurable (fun a : (ℝ × O.Frames) × Position =>
      cutoffSpiral (fun x => actualTileShape O η side ε⁻¹ a.1 (c-x)) B q a.2 j k) := by
    dsimp only [cutoffSpiral,Matrix.smul_apply,smul_eq_mul]
    simp_rw [rotate_by_entry]
    apply (Complex.measurable_ofReal.comp sh).mul
    unfold phaseFactor
    fun_prop
  have me : Measurable F := by
    apply measurable_coulomb_energy_family borel _ entries
    intro i j k
    have ms := actualTiles_shape_mass O frames η side he hle i
    have massPos : 0 < side.mass ε := by cases side <;> simp [CutoffSide.mass, sub_pos.mpr hle]
    have integ : Integrable (fun x => actualTileShape O η side ε⁻¹ i (c-x)) := by
      have ht := tileDilation_pos i.1
      have original : Integrable (actualTileShape O η side ε⁻¹ i) := Integrable.of_integral_ne_zero
        (ms.trans_ne (by positivity : side.mass ε*(tileDilation i.1*ε⁻¹)^3/24 ≠ 0))
      exact (volume.measurePreserving_sub_left c).integrable_comp_of_integrable original
    apply memLp_one_iff_integrable.mpr
    apply (integ.mul_const ‖B j k‖).mono' ((entries j k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp [cutoffSpiral,rotate_by_entry,phaseFactor,Complex.norm_exp,
        abs_of_nonneg (smoothedIndicator_bounds _ η (tileDilation_pos i.1) _).1, actualTileShape]
  have mf : Measurable f := ((measurable_actualTileWeight _).comp measurable_fst).mul me
  have rigid (t : ℝ) (u : O.Frames) : f (t,u) = m * tileEnergy energy η B
      (tileDilation t*L) (tileDilation t) (O.frame u q) := frozen_rigid_motion O η side he hle B q c (t,u)
  have frame (t : ℝ) : Integrable (fun u => f (t,u)) O.law ∧ (∫ u, f (t,u) ∂O.law) = m*g t := by
    have ang := O.average _ (coulomb_continuous_tile H sob η (mul_pos (tileDilation_pos t) hL) (tileDilation_pos t) hB) q
    simp_rw [rigid,integral_const_mul]
    exact ⟨ang.1.const_mul _,congrArg (m * ·) ang.2⟩
  let floor := m*(H.loCoeff*B.trace.re^(4/3:ℝ))
  have lower (t : ℝ) (u : O.Frames) : -floor ≤ f (t,u) := by
    rw [rigid]
    simpa only [floor,mul_neg] using mul_le_mul_of_nonneg_left
      (tile_floor H sob η (mul_pos (tileDilation_pos t) hL) (tileDilation_pos t) hB (O.frame u q)) hm
  have bound (t : ℝ) : g t ≤ K*(B.trace.re*rateGrowth B.trace.re q + B.trace.re/(L/4)) := by
    let s := tileDilation t
    have hs : 1/2 ≤ s := (tileDilation_mem t).1
    have ht : 0 < s := tileDilation_pos t
    have ht' : L/4 ≤ (s*L)*s := by
      have hh : (1/2:ℝ)*(1/2) ≤ s*s := mul_le_mul hs hs (by norm_num) ht.le
      nlinarith only [mul_le_mul_of_nonneg_right hh hL.le]
    have rough := (rate.rough B hB q _ _ (mul_pos ht hL) ht).2
    have hK := zero_le_one.trans rate.one_le
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hρ (by positivity : 0 < L/4) ht') hK
    dsimp only [g,s] at *
    linarith only [hh, rough, mul_nonneg hK (mul_nonneg hρ (Real.rpow_nonneg hρ (1/3:ℝ)))]
  have hi : Integrable f (tileDilationLaw.prod O.law) := by
    apply (integrable_prod_iff mf.aestronglyMeasurable).2
    refine ⟨ae_of_all _ fun t => (frame t).1, (integrable_const
      (m*(K*(B.trace.re*rateGrowth B.trace.re q + B.trace.re/(L/4))) + 2*floor)).mono'
      mf.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_⟩
    refine ae_of_all _ fun t => ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have compare (u : O.Frames) : ‖f (t,u)‖ ≤ f (t,u) + 2*floor := by
      have hf : 0 ≤ floor := mul_nonneg hm (mul_nonneg H.lo_nonneg (Real.rpow_nonneg hρ _))
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith only [lower t u, hf]
    calc
      _ ≤ ∫ u, f (t,u) + 2*floor ∂O.law :=
        integral_mono (frame t).1.norm ((frame t).1.add (integrable_const _)) compare
      _ = m*g t + 2*floor := by rw [integral_add (frame t).1 (integrable_const _),integral_const,
                                      probReal_univ,one_smul,(frame t).2]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (bound t) hm) le_rfl
  refine ⟨hi,?_⟩
  change (∫ i, f i ∂tileDilationLaw.prod O.law) = _
  rw [integral_prod _ hi]
  simp_rw [(frame _).2]
  rw [integral_const_mul]
  congr 1
  rw [← integral_tileDilationLaw]
  exact integral_congr_ae (tileDilationLaw_mem.mono fun t ht => by simp [g,tileDilation_of_mem ht])

/-- Uniform finite-size error for a frozen matrix of trace ρ and the same
wavevector on every tile at the center. -/
def smallFrozenSizeCost (K ε ρ : ℝ) (q : Position) : ℝ :=
  8*(K^2+K)*(ε*ρ*(2+ρ+rateGrowth ρ q))

/-- Instantiate the signed finite-volume rate with the two actual tetrahedra. -/
theorem actual_frozen_scale (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (side : CutoffSide) {ε K a : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2)
    (admissible : ε*(K+1) ≤ 1) (rate : FiniteRateTiling energy η K)
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) {B : SpinMatrix} (hB : B.PosSemidef) (q c : Position) :
    let tiles := actualTiles O frames η side he (by linarith : ε < 1)
    tiles.FrozenIntegrable (referenceEnergies energy η) B q c ∧
      ∃ F : CoulombFreezeScale rate tiles B q c (tileSign side),
        F.error = smallFrozenSizeCost K ε B.trace.re q := by
  intro tiles
  have hle' : ε < 1 := by linarith
  let L := tileSideLength side ε⁻¹
  let ρ := B.trace.re
  have hL : 0 < L := tileSideLength_pos side he hle'
  have hK : 0 ≤ K := zero_le_one.trans rate.one_le
  have hρ : 0 ≤ ρ := (RCLike.nonneg_iff.mp hB.trace_nonneg).1
  have R₀ : 0 ≤ rateGrowth ρ q := by unfold rateGrowth; positivity
  have hbase : K+1 ≤ ε⁻¹ := by rw [← one_div]; exact (le_div_iff₀ he).2 (by rwa [mul_comm])
  have hscale : 1*K ≤ L := by cases side <;> dsimp [L,tileSideLength] <;> linarith
  have hfrac : 1 ≤ 2*ε*L := by
    cases side <;> dsimp [L,tileSideLength] <;> nlinarith only [mul_inv_cancel₀ he.ne', hle]
  have hquot : ρ/L ≤ 2*ε*ρ := (div_le_iff₀ hL).2 (by nlinarith only [mul_le_mul_of_nonneg_left hfrac hρ])
  let E := ρ/L*(2+ρ+rateGrowth ρ q)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have Emax : E ≤ 2*ε*ρ*(2+ρ+rateGrowth ρ q) :=
    mul_le_mul_of_nonneg_right hquot (by positivity)
  have up : upperRateError ρ q L 1 = E := by simp only [upperRateError,lowerRateError,inv_one,one_pow,one_mul,E]; ring
  have lo : lowerRateError ρ q L 1 ≤ E := by rw [← up,upperRateError]; exact le_add_of_nonneg_left (div_nonneg hρ hL.le)
  have mass := (actualTetrahedralCutoffs O frames η sob ha area side he hle').cutoff_mass he
  have hm : side.mass ε ≤ 1 := by
    cases side with
    | upper => exact pow_le_one₀ (by linarith) (by linarith)
    | lower => exact le_rfl
  have m₀ : 0 ≤ side.mass ε := by cases side <;> dsimp [CutoffSide.mass] <;> positivity
  have hcoef : 0 ≤ K^2+K := by positivity
  have main : (K^2+K)*(4*E) ≤ smallFrozenSizeCost K ε ρ q := by
    have h := mul_le_mul_of_nonneg_left Emax (by positivity : 0 ≤ (K^2+K)*4)
    dsimp [smallFrozenSizeCost]
    linarith only [h]
  obtain ⟨integ,cov⟩ := actual_frozen_average H sob borel O frames η side he hle' rate hB q c
  refine ⟨integ, {
    length := L
    width := 1
    length_pos := hL
    width_pos := zero_lt_one
    admissible := hscale
    averaged := true
    fixed_sign := by simp
    covariance := by simpa only [tiles,L,mass,ite_true] using cov
    error := smallFrozenSizeCost K ε ρ q
    nonneg := by unfold smallFrozenSizeCost; positivity
    scalar := ?_ }, rfl⟩
  rw [show (∫ z, tiles.cutoffProfile z) = side.mass ε from mass]
  cases side with
  | upper =>
    simp only [tileSign,ite_true] at *
    change CutoffSide.upper.mass ε*((K^2+K)*(4*upperRateError ρ q L 1)) ≤ _
    rw [up]
    exact (mul_le_of_le_one_left (by positivity : 0 ≤ (K^2+K)*(4*E)) hm).trans main
  | lower =>
    change CutoffSide.lower.mass ε * (if (-1:ℝ)=1 then _ else K*lowerRateError ρ q L 1) ≤ _
    rw [ite_eq_right_iff.mpr (by norm_num), show CutoffSide.lower.mass ε = 1 from rfl,one_mul]
    apply (mul_le_mul_of_nonneg_left lo hK).trans
    exact (by nlinarith only [mul_nonneg (sq_nonneg K) hE, mul_nonneg hK hE] : K*E ≤ (K^2+K)*(4*E)).trans main

end TSGA.ManyBody
