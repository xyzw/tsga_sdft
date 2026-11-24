import TSGA.SmallBallMatrices
import TSGA.RegularLargeTile
import TSGA.ReplacementInterpolation

/-! # Averaged bulk and residual-charge errors on a small ball -/

noncomputable section
namespace TSGA.ManyBody.SmallBallScale
open MeasureTheory TSGA.Localization PhaseLocalization Metric Set

variable {N : Density} {c : Position} {ε p θ ν C : ℝ}
  (s : SmallBallScale N (3*ε⁻¹) c)

private theorem morrey_max {a : ℝ} {f : Position → ℝ} (ha : 0 < a) (he : 0 < ε)
    (estimate : ∀ x ∈ closedBall c (3*ε⁻¹), ∀ y ∈ closedBall c (3*ε⁻¹),
      hilbertSchmidt (N.power a x-N.power a y)^p ≤ C*(3*ε⁻¹)^(p-3)*
        ∫ z in closedBall c (3*ε⁻¹), f z) :
    s.omega a^p ≤ ε^(-p)*(tileMorreyCoefficient p C*ballAverage (3*ε⁻¹) f c) := by
  obtain ⟨x,hx,y,hy,h⟩ := s.omega_max a ha
  rw [h]
  exact tile_ball_morrey_average he c (tile_ball_morrey_scale he c (estimate x hx y hy))

/-- Interpolate the density part of the gas modulus at the actual oscillation.
The global-root regime uses the supplied global gradient of the matrix root. -/
theorem bulk_interpolation (M : MatrixSobolevMorrey p C) (mode : BulkRegime)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hC : 0 ≤ C) (he : 0 < ε)
    {S T G : MatrixGradient} (reg : DensityRegular N p θ S T) (hr : RegimeHyp mode ν N G p)
    (cp : ∀ a : ℝ, 0 < a → Continuous (N.power a)) :
    (s.r^(4/3:ℝ)+s.r^(5/3:ℝ))*(s.omega (mode.densityPower p θ)/s.r^(mode.densityPower p θ))^
      (mode.holderPower p θ) ≤ 2*(ε*(s.r+s.r^2) +
      tileMorreyCoefficient p C*ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c/ε^(mode.exponent p θ)) := by
  have hp₀ : 0 < p := by linarith
  have hθ : 0 < θ := pos_of_mul_pos_right (by linarith : 0 < p*θ) hp₀.le
  have hR : 0 < 3*ε⁻¹ := by positivity
  let u := mode.densityPower p θ
  have hu : 0 < u := (one_div_pos.mpr hp₀).trans_le (mode.root_le_densityPower hp₀ hpθ)
  have hω := s.omega_nonneg u hu
  have osc : s.omega u^p ≤ ε^(-p)*(tileMorreyCoefficient p C*ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c) := by
    apply s.morrey_max hu he
    intro x hx y hy
    cases mode with
    | general | minority => exact M.theta_pair hp reg (cp θ hθ) hR x hx y hy
    | globalRoot =>
      apply (M.global_pair hp hr.1 hr.2 (cp (1/p) (one_div_pos.mpr hp₀)) hR x hx y hy).trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg hR.le _))
      have it := rootPower_integrable hp₀ reg.theta_Lp
      have ig := rootPower_integrable hp₀ hr.2
      exact setIntegral_mono ig.integrableOn (it.add ig).integrableOn
        (fun z => le_add_of_nonneg_left (rootPower_nonneg T p z))
  rcases s.r_nonneg.eq_or_lt with hz | hpos
  · have hB : 0 ≤ tileMorreyCoefficient p C :=
      mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC
    rw [← hz,Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0),Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
    have bg := ballAverage_nonnegative (3*ε⁻¹) (bulkDensity_nonneg mode T G p) c
    simpa only [zero_add,zero_mul,zero_pow (by decide : 2 ≠ 0),mul_zero] using
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (div_nonneg (mul_nonneg hB bg) (Real.rpow_nonneg he.le _)))
  · simpa only [one_mul,mul_one] using mode.combined_bound (V := 1) hp hpθ he zero_lt_one hpos hω
      (by simpa only [one_mul] using osc)

/-- The two terms of the residual-charge error use the native replacement
exponent, including at zero density. -/
theorem residual_interpolation (M : MatrixSobolevMorrey p C) (hp : 3 < p) (hθ : 0 < θ)
    (hle : θ ≤ 1) (hpθ : 2 ≤ p*θ) (hC : 0 ≤ C) (he : 0 < ε)
    {S T : MatrixGradient} (reg : DensityRegular N p θ S T) (cp : Continuous (N.power θ))
    (smallθ : s.omega θ ≤ s.r^θ) :
    let capacity := 6*s.omega 1
    capacity*(Real.sqrt (capacity/ε)+capacity/ε) ≤ ((6/θ)^(3/2:ℝ)+(6/θ)^2)*
      (ε*(s.r+s.r^2)+tileMorreyCoefficient p C*ballAverage (3*ε⁻¹) (rootPower T p) c/
        ε^(p+max p (3*θ*p-3)-1)) := by
  intro capacity
  have hp₀ : 0 < p := by linarith
  let k := max p (3*θ*p-3)
  let g := tileMorreyCoefficient p C*ballAverage (3*ε⁻¹) (rootPower T p) c
  let B := ε*(s.r+s.r^2)+g/ε^(p+k-1)
  have hcap : 0 ≤ capacity := mul_nonneg (by norm_num) (s.omega_nonneg _ zero_lt_one)
  have hL : 0 ≤ 6/θ := by positivity
  have hg : 0 ≤ g := mul_nonneg
    (mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC)
    (ballAverage_nonnegative _ (rootPower_nonneg T p) c)
  have hb : 0 ≤ B := add_nonneg (mul_nonneg he.le (add_nonneg s.r_nonneg (sq_nonneg _)))
    (div_nonneg hg (Real.rpow_nonneg he.le _))
  have cap : capacity ≤ (6/θ)*(s.r^(1-θ)*s.omega θ) := by
    calc
      _ ≤ 6*((1/θ*s.r^(1-θ))*s.omega θ) := mul_le_mul_of_nonneg_left (s.omega_one_le θ hθ hle) (by norm_num)
      _ = _ := by ring
  rcases s.r_nonneg.eq_or_lt with hz | hpos
  · have hz' : capacity=0 := le_antisymm (by dsimp only [capacity]; linarith only [s.small,hz]) hcap
    change capacity*_ ≤ _*B
    rw [hz',zero_mul]
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg hL _) (sq_nonneg _)) hb
  · have osc : s.omega θ^p ≤ ε^(-p)*g :=
      s.morrey_max hθ he (M.theta_pair hp reg cp (by positivity))
    have scale : ε^(1-k)*(ε^(-p)*g) = g/ε^(p+k-1) := by
      rw [div_eq_mul_inv,← Real.rpow_neg he.le,← mul_assoc,← Real.rpow_add he]
      ring_nf
    have bound (m : ℝ) (hm : m ∈ Set.Icc (3/2:ℝ) 2) :
        ε^(1-m)*capacity^m ≤ (6/θ)^m*B := by
      have h := residual_charge_interpolation (V := 1) hp (by linarith only [hpθ,mul_comm θ p]) hm he hpos
        zero_le_one hL hcap (s.omega_nonneg θ hθ) smallθ cap (by simpa only [one_mul] using osc)
      simpa only [one_mul,mul_one,← scale,B,k] using h
    have h₁ := bound (3/2) (by constructor <;> norm_num)
    have h₂ := bound 2 (by constructor <;> norm_num)
    have heq₁ : ε^(1-(3/2:ℝ))*capacity^(3/2:ℝ) = capacity*Real.sqrt (capacity/ε) := by
      rw [Real.sqrt_eq_rpow,Real.div_rpow hcap he.le,
        show (3/2:ℝ)=1/2+1 by norm_num,Real.rpow_add_one' hcap (by norm_num : (1/2:ℝ) + 1 ≠ 0),
        show (1:ℝ)-(1/2+1)=-(1/2) by norm_num,Real.rpow_neg he.le]
      ring
    have heq₂ : ε^(1-(2:ℝ))*capacity^(2:ℝ) = capacity*(capacity/ε) := by
      rw [show (1:ℝ)-2= -(1:ℝ) by norm_num,Real.rpow_neg he.le,Real.rpow_one,Real.rpow_two]
      ring
    rw [heq₁] at h₁
    rw [heq₂,Real.rpow_two] at h₂
    change _ ≤ _*B
    rw [mul_add,add_mul]
    exact add_le_add h₁ h₂

end TSGA.ManyBody.SmallBallScale
