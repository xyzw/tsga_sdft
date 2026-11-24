import TSGA.SmallBallBulk
import TSGA.SmallBallPhaseScale
import TSGA.ReplacementScale

/-! # Reduction of small-ball freezing errors to the localized error density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization Metric Set

/-- The local average on the right of the TSGA bound. -/
def smallBallErrorDensity (mode : BulkRegime) (D : Density) (φ : Phase) (S T G : MatrixGradient)
    (p θ ε C : ℝ) (c : Position) : ℝ :=
  let R := 3*ε⁻¹
  ε*bulkAverage D φ R c + ballAverage R (kineticDensity S) c/ε +
    tileMorreyCoefficient p C*ballAverage R (bulkDensity mode T G p) c/ε^(mode.exponent p θ) +
    ballAverage R (phaseDensity D φ G p) c/ε^(2*p-1)

theorem smallBallErrorDensity_nonneg (mode : BulkRegime) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p θ : ℝ) {ε C : ℝ} (he : 0 < ε) (hC : 0 ≤ C) (c : Position) :
    0 ≤ smallBallErrorDensity mode D φ S T G p θ ε C c := by
  have hB : 0 ≤ tileMorreyCoefficient p C :=
    mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg he.le (ballAverage_nonnegative _ (massDensity_nonneg D φ) c))
    (div_nonneg (ballAverage_nonnegative _ (f := kineticDensity S) (fun x => sq_nonneg (matrixGradNorm S x)) c) he.le))
    (div_nonneg (mul_nonneg hB (ballAverage_nonnegative _ (bulkDensity_nonneg mode T G p) c)) (Real.rpow_nonneg he.le _)))
    (div_nonneg (ballAverage_nonnegative _ (phaseDensity_nonneg D φ G p) c) (Real.rpow_nonneg he.le _))

def smallBallErrorConstant (p θ Cmat Cvec U V : ℝ) : ℝ :=
  let ph := tileConstant p (smallBallPhaseConstant p Cmat Cvec)
  let residual := (6/θ)^(3/2:ℝ)+(6/θ)^2
  U*(4+ph+ballVolume 3+5*residual) + V*(10+ph)

private theorem scaled_kinetic_ball (S : MatrixGradient) {ε : ℝ} (he : 0 < ε) (c : Position) :
    ε^3 * (∫ x in closedBall c (3*ε⁻¹), kineticDensity S x) =
      ballVolume 3*ballAverage (3*ε⁻¹) (kineticDensity S) c := by
  let R := 3*ε⁻¹
  have hi : (∫ x in closedBall c R, kineticDensity S x) = ballIntegral R (kineticDensity S) c :=
    setIntegral_congr_set (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume c R).le measurableSet_ball.nullMeasurableSet
      (isCompact_closedBall c R).measure_lt_top.ne).symm
  have hv : ballVolume R = ε⁻¹^3*ballVolume 3 := by
    simpa only [R,mul_comm ε⁻¹ (3:ℝ)] using ballVolume_scaled (inv_pos.mpr he) 3
  change ε^3*(∫ x in closedBall c R, kineticDensity S x) = ballVolume 3*(ballIntegral R (kineticDensity S) c / ballVolume R)
  rw [hi,hv]
  field_simp [he.ne', (ballVolume_pos (by norm_num : (0:ℝ)<3)).ne']

theorem charge_scale_le_bulkAverage {N D : Density} {φ : Phase} {p θ R : ℝ}
    {S T G : MatrixGradient} (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    {c : Position} (s : SmallBallScale N R c) (e : N.matrix =ᵐ[volume] D.matrix) (hR : 0 < R) :
    s.r+s.r^2 ≤ 4*bulkAverage D φ R c := by
  have hvol : volume.real (ball c R) = ballVolume R := Measure.addHaar_real_ball_center volume c R
  have hm := massDensity_integrable reg phase
  have lhs : IntegrableOn (fun _ : Position => s.r+s.r^2) (ball c R) :=
    integrableOn_const (measure_ball_lt_top (μ := volume) (x := c) (r := R)).ne
  have hp : ∀ᵐ x ∂volume.restrict (ball c R), s.r+s.r^2 ≤ 4*massDensity D φ x := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (densityCharge_ae_congr e)] with x hx hh
    have h := s.comparable x (ball_subset_closedBall hx)
    rw [hh] at h
    have h' : s.r ≤ 2*D.charge x := by linarith
    unfold massDensity
    nlinarith only [h',pow_le_pow_left₀ s.r_nonneg h' 2,D.charge_nonneg x,mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)]
  have bound := integral_mono_ae lhs (hm.integrableOn.const_mul 4) hp
  change (∫ x in ball c R, s.r+s.r^2) ≤ ∫ x in ball c R, 4*massDensity D φ x at bound
  rw [setIntegral_const, smul_eq_mul,hvol,integral_const_mul] at bound
  change _ ≤ 4*((∫ x in ball c R, massDensity D φ x)/ballVolume R)
  rw [← mul_div_assoc,le_div_iff₀ (ballVolume_pos hR)]
  linarith only [bound]

/-- The θ-power, active-root, curvature, and taper costs share a single
constant uniform in the ball, the data and ε. The global-root application
uses the endpoint θp = 2. -/
theorem SmallBallScale.error_density_bound {N D : Density} {φ : Phase} {S T G : MatrixGradient}
    {p θ ν ε Cmat Cvec U V : ℝ} {c : Position} (s : SmallBallScale N (3*ε⁻¹) c)
    (mode : BulkRegime) (e : N.matrix =ᵐ[volume] D.matrix) (reg : DensityRegular D p θ S T)
    (phase : PhaseAdmissible D p φ G) (hr : RegimeHyp mode ν D G p)
    (M : MatrixSobolevMorrey p Cmat) (vec : VectorMorreyOnBalls p Cvec)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hθ : 0 < θ) (hle : θ ≤ 1)
    (he : 0 < ε) (he' : ε ≤ 1) (hmat : 0 ≤ Cmat) (hvec : 0 ≤ Cvec)
    (powers : ∀ a : ℝ, 0 < a → Continuous (N.power a)) (small : s.omega θ ≤ s.r^θ)
    (endpoint : mode = .globalRoot → θ*p = 2) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    let radius := 3*ε⁻¹
    let ph := smallBallPhaseCost s.r (s.omega (1/p)/s.r^(1/p)) ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)
    let k := ∫ x in closedBall c radius, kineticDensity S x
    let cap := 6*s.omega 1
    let b := mode.densityPower p θ
    let gas := (s.r^(4/3:ℝ)+s.r^(5/3:ℝ))*(s.omega b/s.r^b)^(mode.holderPower p θ)
    U*(ε*(s.r+s.r^2)+ph+ε^3*k/ε+cap*(√(cap/ε)+cap/ε)) + V*(gas+ph) ≤
      smallBallErrorConstant p θ Cmat Cvec U V*smallBallErrorDensity mode D φ S T G p θ ε Cmat c := by
  intro R ph k cap b gas
  let w := smallBallErrorDensity mode D φ S T G p θ ε Cmat c
  let B := tileMorreyCoefficient p Cmat
  let L := (6/θ)^(3/2:ℝ)+(6/θ)^2
  let H := tileConstant p (smallBallPhaseConstant p Cmat Cvec)
  let mass := ε*bulkAverage D φ R c
  let kin := ballAverage R (kineticDensity S) c/ε
  let grad := B*ballAverage R (bulkDensity mode T G p) c/ε^(mode.exponent p θ)
  let curv := ballAverage R (phaseDensity D φ G p) c/ε^(2*p-1)
  have hp₀ : 0 < p := by linarith
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hmat
  have hm : 0 ≤ mass := mul_nonneg he.le (ballAverage_nonnegative _ (massDensity_nonneg D φ) c)
  have hk : 0 ≤ kin := div_nonneg (ballAverage_nonnegative R (fun x => sq_nonneg _) c) he.le
  have hg : 0 ≤ grad := div_nonneg (mul_nonneg hB (ballAverage_nonnegative R (bulkDensity_nonneg mode T G p) c)) (Real.rpow_nonneg he.le _)
  have hc : 0 ≤ curv := div_nonneg (ballAverage_nonnegative R (phaseDensity_nonneg D φ G p) c) (Real.rpow_nonneg he.le _)
  have ew : w = mass+kin+grad+curv := rfl
  have mass_le : ε*(s.r+s.r^2) ≤ 4*w := by
    have z := mul_le_mul_of_nonneg_left (charge_scale_le_bulkAverage reg phase s e (by positivity)) he.le
    change ε*(s.r+s.r^2) ≤ ε*(4*bulkAverage D φ R c) at z
    rw [mul_left_comm ε 4] at z
    change ε*(s.r+s.r^2) ≤ 4*mass at z
    linarith only [ew,hk,hg,hc,z]
  have kin_le : ε^3*k/ε ≤ ballVolume 3*w := by
    have hz : ε^3*k/ε = ballVolume 3*kin := by
      rw [show ε^3*k = _ from scaled_kinetic_ball S he c]
      dsimp only [kin]
      ring
    rw [hz]
    exact mul_le_mul_of_nonneg_left (by linarith only [ew,hm,hg,hc]) (ballVolume_pos (by norm_num : (0:ℝ)<3)).le
  have phase_le : ph ≤ H*w := by
    have h := s.phase_bound e reg phase M vec hp he he' hmat hvec (powers _ (one_div_pos.mpr hp₀))
    have hH : 0 ≤ H := tileConstant_nonneg p (by unfold smallBallPhaseConstant; positivity)
    exact h.trans (mul_le_mul_of_nonneg_left (by change mass+curv ≤ w; linarith only [ew,hk,hg]) hH)
  have rn := densityRegular_of_ae e.symm reg
  have rhr := regimeHyp_of_ae e.symm hr
  have gas_le : gas ≤ 10*w := by
    have h := s.bulk_interpolation M mode hp hpθ hmat he rn rhr powers
    change gas ≤ 2*(ε*(s.r+s.r^2)+grad) at h
    linarith only [h,mass_le,ew,hm,hk,hc]
  have native : p+max p (3*θ*p-3)-1 = mode.replacementExponent p θ := by
    cases mode with
    | general | minority => rfl
    | globalRoot =>
      have ee : θ = 2/p := (eq_div_iff hp₀.ne').2 (endpoint rfl)
      rw [ee]
      exact BulkRegime.nativeReplacement_at_two_div hp
  have res_le : cap*(√(cap/ε)+cap/ε) ≤ 5*L*w := by
    have h := s.residual_interpolation M hp hθ hle hpθ hmat he rn (powers θ hθ) small
    have ae : ballAverage R (rootPower T p) c ≤ ballAverage R (bulkDensity mode T G p) c := by
      apply div_le_div_of_nonneg_right _ (ballVolume_pos (by positivity : 0 < R)).le
      exact setIntegral_mono (rootPower_integrable hp₀ reg.theta_Lp).integrableOn
        (bulkDensity_integrable hp₀ reg hr).integrableOn (rootPower_le_bulkDensity mode T G p)
    have av := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ae hB) (Real.rpow_nonneg he.le (mode.replacementExponent p θ))
    have sc := mode.replacement_cost_le p θ he he' (mul_nonneg hB (ballAverage_nonnegative R (bulkDensity_nonneg mode T G p) c))
    change cap*(√(cap/ε)+cap/ε) ≤ L*(ε*(s.r+s.r^2)+ B*ballAverage R (rootPower T p) c/ε^(p+max p (3*θ*p-3)-1)) at h
    rw [native] at h
    have last : ε*(s.r+s.r^2)+B*ballAverage R (rootPower T p) c/ε^(mode.replacementExponent p θ) ≤ 5*w := by
      change _ ≤ grad at sc
      linarith only [av,sc,ew,hm,hk,hc,mass_le]
    have hL : 0 ≤ L := add_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
    exact (h.trans (mul_le_mul_of_nonneg_left last hL)).trans_eq (by ring)
  have a : ε*(s.r+s.r^2)+ph+ε^3*k/ε+cap*(√(cap/ε)+cap/ε) ≤ (4+H+ballVolume 3+5*L)*w := by
    linarith only [mass_le,phase_le,kin_le,res_le]
  have g : gas+ph ≤ (10+H)*w := by linarith only [gas_le,phase_le]
  exact (add_le_add (mul_le_mul_of_nonneg_left a hU) (mul_le_mul_of_nonneg_left g hV)).trans_eq (by
    change U*((4+H+ballVolume 3+5*L)*w)+V*((10+H)*w) = (U*(4+H+ballVolume 3+5*L)+V*(10+H))*w
    ring)

end TSGA.ManyBody
