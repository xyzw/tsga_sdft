import TSGA.SmallBallIntegratedError
import TSGA.RegularLargeTile

/-! # Normalizing the large-oscillation remainder on the physical tile families -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Set Metric

/-- Coefficient of the four normalized error terms on a large ball. -/
def largeTileBallCoefficient (mode : BulkRegime) (p θ κ C : ℝ) : ℝ :=
  let k := bulkOscillationThreshold mode p θ κ
  let L := largeBallConstant mode p θ k C
  ballVolume 3*(2/k^(mode.holderPower p θ) + (2:ℝ)^p*(1+(2:ℝ)^p*L^2))

private theorem threshold_pos (mode : BulkRegime) {p θ κ : ℝ}
    (hp : 0 < p) (hθ : 0 < θ) (hκ : 0 < κ) : 0 < bulkOscillationThreshold mode p θ κ := by
  cases mode <;> first | exact hκ | exact div_pos hκ (mul_pos hp hθ)

theorem largeTileBallCoefficient_nonneg (mode : BulkRegime) {p θ κ C : ℝ}
    (hp : 0 < p) (hθ : 0 < θ) (hκ : 0 < κ) (_hC : 0 ≤ C) :
    0 ≤ largeTileBallCoefficient mode p θ κ C := by
  let k := bulkOscillationThreshold mode p θ κ
  have hk : 0 < k := threshold_pos mode hp hθ hκ
  unfold largeTileBallCoefficient
  positivity [ballVolume_pos (by norm_num : (0:ℝ)<3), Real.rpow_pos_of_pos hk (mode.holderPower p θ)]

private theorem scaled_closedBall_integral {ε : ℝ} (he : 0 < ε) (c : Position) (f : Position → ℝ) :
    ε^3*(∫ x in closedBall c (3*ε⁻¹), f x) = ballVolume 3*ballAverage (3*ε⁻¹) f c := by
  let R := 3*ε⁻¹
  have hi : (∫ x in closedBall c R, f x) = ballIntegral R f c :=
    setIntegral_congr_set (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume c R).le measurableSet_ball.nullMeasurableSet
      (isCompact_closedBall c R).measure_lt_top.ne).symm
  have hv : ballVolume R = ε⁻¹^3*ballVolume 3 := by
    simpa only [R,mul_comm ε⁻¹ (3:ℝ)] using ballVolume_scaled (inv_pos.mpr he) 3
  change ε^3*(∫ x in closedBall c R, f x) = ballVolume 3*(ballIntegral R f c / ballVolume R)
  rw [hi,hv]
  field_simp [he.ne', (ballVolume_pos (by norm_num : (0:ℝ)<3)).ne']

/-- After the factor from the physical cell volume, the rough Coulomb trial
has the same mass, bulk and phase majorant used for freezing. -/
theorem largeTileBallCost_bound (mode : BulkRegime) {p θ κ C ε : ℝ}
    (hp : 0 < p) (hθ : 0 < θ) (hκ : 0 < κ) (hC : 0 ≤ C) (he : 0 < ε)
    {D : Density} {φ : Phase} {S T G : MatrixGradient} (reg : DensityRegular D p θ S T)
    (phase : PhaseAdmissible D p φ G) (c : Position) :
    ε^3*largeTileBallCost mode p θ κ ε C c D φ T G ≤
      largeTileBallCoefficient mode p θ κ C * smallBallErrorDensity mode D φ S T G p θ ε C c := by
  let R := 3*ε⁻¹
  let Ω := closedBall c R
  let k := bulkOscillationThreshold mode p θ κ
  let L := largeBallConstant mode p θ k C
  let V := ballVolume 3
  let w := smallBallErrorDensity mode D φ S T G p θ ε C c
  let m := ε*bulkAverage D φ R c
  let t := ballAverage R (kineticDensity S) c/ε
  let g := tileMorreyCoefficient p C * ballAverage R (bulkDensity mode T G p) c / ε^(mode.exponent p θ)
  let f := ballAverage R (phaseDensity D φ G p) c / ε^(2*p-1)
  have hV : 0 ≤ V := (ballVolume_pos (by norm_num : (0:ℝ)<3)).le
  have hk : 0 < k := threshold_pos mode hp hθ hκ
  have hB : 0 ≤ tileMorreyCoefficient p C :=
    mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC
  have h2 : 0 ≤ (2:ℝ)^p := Real.rpow_nonneg (by norm_num) _
  have hm : 0 ≤ m := mul_nonneg he.le (ballAverage_nonnegative R (massDensity_nonneg D φ) c)
  have ht : 0 ≤ t := div_nonneg (ballAverage_nonnegative R (fun x => sq_nonneg _) c) he.le
  have hg : 0 ≤ g := div_nonneg (mul_nonneg hB (ballAverage_nonnegative R (bulkDensity_nonneg mode T G p) c))
    (Real.rpow_nonneg he.le _)
  have hf : 0 ≤ f := div_nonneg (ballAverage_nonnegative R (phaseDensity_nonneg D φ G p) c) (Real.rpow_nonneg he.le _)
  have ew : w = m+t+g+f := rfl
  have volumeScale : ε^3*volume.real Ω = V := by
    have vol : volume.real Ω = ballVolume R := by
      rw [Measure.real,Measure.addHaar_closedBall_eq_addHaar_ball]
      exact Measure.addHaar_real_ball_center volume c R
    have hv : ballVolume R = ε⁻¹^3*ballVolume 3 := by
      simpa only [R,mul_comm ε⁻¹ (3:ℝ)] using ballVolume_scaled (inv_pos.mpr he) 3
    rw [vol,hv]
    dsimp only [V]
    field_simp [he.ne']
  let n := fun x => D.charge x+D.charge x^2
  have hmc := massDensity_integrable reg phase
  have bnd (u : Position → ℝ) (hu : Integrable u) (le : ∀ x, u x ≤ massDensity D φ x) :
      ε^3*(ε*∫ x in Ω, u x) ≤ V*m := by
    calc
      _ ≤ ε^3*(ε*∫ x in Ω, massDensity D φ x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (setIntegral_mono hu.integrableOn hmc.integrableOn le) he.le) (by positivity)
      _ = ε*(ε^3*∫ x in Ω, massDensity D φ x) := by ring
      _ = V*m := by
        rw [show ε^3*(∫ x in Ω, massDensity D φ x) = _ from scaled_closedBall_integral he c (massDensity D φ)]
        change ε*(V*bulkAverage D φ R c) = V*(ε*bulkAverage D φ R c)
        ring
  have nle := bnd n (reg.charge_L1.add reg.charge_L2.integrable_sq) (fun x =>
    le_add_of_nonneg_right (mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)))
  have rle := bnd D.charge reg.charge_L1 (fun x =>
    (le_add_of_nonneg_right (sq_nonneg (D.charge x))).trans
      (le_add_of_nonneg_right (mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖))))
  have peq : (∫ x in Ω, weightedRoot φ G p x) + (∫ x in Ω, D.charge x*φ.hessianNorm x^p) =
      ∫ x in Ω, phaseDensity D φ G p x := by
    change _ = ∫ x in Ω, D.charge x*φ.hessianNorm x^p + weightedRoot φ G p x
    rw [integral_add phase.curvature.integrableOn (integrable_weightedRoot phase).integrableOn,add_comm]
  let u := 2/k^(mode.holderPower p θ)
  let v := (2:ℝ)^p*L^2
  have hu : 0 ≤ u := div_nonneg (by norm_num) (Real.rpow_nonneg hk.le _)
  have hv : 0 ≤ v := mul_nonneg h2 (sq_nonneg _)
  have bulk : ε^3*(2*((ε*∫ x in Ω, n x)+volume.real Ω*g)/k^(mode.holderPower p θ)) ≤ u*(V*w) := by
    calc
      _ = u*(ε^3*(ε*∫ x in Ω, n x) + ε^3*volume.real Ω*g) := by dsimp only [u]; ring
      _ ≤ u*(V*m+V*g) := mul_le_mul_of_nonneg_left (add_le_add nle (by rw [volumeScale])) hu
      _ ≤ u*(V*w) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [ew,ht,hf]) hV) hu
  have phaseBound : ε^3*((2:ℝ)^p*((ε*∫ x in Ω, D.charge x) + v/ε^(2*p-1)*
      (∫ x in Ω, phaseDensity D φ G p x))) ≤ (2:ℝ)^p*(1+v)*(V*w) := by
    calc
      _ = (2:ℝ)^p*(ε^3*(ε*∫ x in Ω, D.charge x) + v*((ε^3*∫ x in Ω, phaseDensity D φ G p x)/ε^(2*p-1))) := by ring
      _ = (2:ℝ)^p*(ε^3*(ε*∫ x in Ω, D.charge x) + v*(V*f)) := by
        rw [show ε^3*(∫ x in Ω, phaseDensity D φ G p x) = _ from scaled_closedBall_integral he c _]
        dsimp only [f,V,R]
        ring
      _ ≤ (2:ℝ)^p*(V*w + v*(V*w)) := by
        apply mul_le_mul_of_nonneg_left _ h2
        exact add_le_add (rle.trans (mul_le_mul_of_nonneg_left (by linarith only [ew,ht,hg,hf]) hV))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [ew,hm,ht,hg]) hV) hv)
      _ = _ := by ring
  dsimp only [largeTileBallCost]
  rw [mul_add,peq]
  exact (add_le_add bulk phaseBound).trans_eq (by
    change u*(V*w) + (2:ℝ)^p*(1+v)*(V*w) = (V*(u+(2:ℝ)^p*(1+v)))*w
    ring)

theorem actualLargeKinetic_nonneg (H : FiniteEnergyInputs) (O : TileOrientationLaw)
    (frames : TileFrameMeasurable O) (η : Mollifier) (side : CutoffSide) {ε : ℝ}
    (he : 0 < ε) (hle : ε < 1) (D : Density) (S : MatrixGradient) (c : Position) :
    0 ≤ actualLargeKinetic H O frames η side he hle D S c := by
  let T := actualTiles O frames η side he hle
  have shape (z : Position) : 0 ≤ T.cutoffProfile z :=
    integral_nonneg (fun i => mul_nonneg (T.weight_nonneg i) (T.shape_mem i z).1)
  have kernel (z : Position) : 0 ≤ ∫ i : ℝ × O.Frames, actualTileWeight ε⁻¹ i.1 *
      ‖actualTileGradient O η side ε⁻¹ i z‖^2 ∂tileDilationLaw.prod O.law :=
    integral_nonneg (fun i => mul_nonneg (actualTileWeight_nonneg (inv_pos.mpr he).le i.1) (sq_nonneg _))
  unfold actualLargeKinetic
  exact add_nonneg (mul_nonneg (by positivity [H.interiorConstant_nonneg])
    (integral_nonneg (fun x => mul_nonneg (sq_nonneg (matrixGradNorm S x)) (shape (c-x)))))
    (mul_nonneg (by positivity [H.interiorConstant_nonneg])
      (integral_nonneg (fun x => mul_nonneg (D.charge_nonneg x) (kernel (c-x)))))

end TSGA.ManyBody
