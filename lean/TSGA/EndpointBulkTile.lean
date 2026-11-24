import TSGA.EndpointInterpolation
import TSGA.SmallBallErrorDensity
import TSGA.SmallBallGas

/-! # The local Young inequality for a power modulus at full polarization -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization Metric Set

/-- The extra centerwise error for the intermediate endpoint exponent. -/
def endpointTileCost (D : Density) (T : MatrixGradient) (p b ε C : ℝ) (c : Position) : ℝ :=
  ε*bulkAverage D Phase.zero (3*ε⁻¹) c +
    tileMorreyCoefficient p C*ballAverage (3*ε⁻¹) (rootPower T p) c/ε^b

private theorem endpoint_young {p θ α r ω ε g m : ℝ}
    (hp : 3 < p) (hθ : 0 < θ) (hα : 0 < α) (hpθ : 2 ≤ θ*p) (hr : 0 < r)
    (he : 0 < ε) (homega : 0 ≤ ω) (hm : m ∈ Icc (4/3:ℝ) (5/3))
    (osc : ω^p ≤ ε^(-p)*g) :
    let a := min (min 1 (α/θ)) (p/(3*(θ*p-1)))
    r^m*(ω/r^θ)^a ≤ ε*(r+r^2)+g/ε^(endpointBulkExponent p θ α) := by
  intro a
  have hp₀ : 0 < p := by linarith
  have hd : 0 < 3*(θ*p-1) := by linarith
  have ha : 0 < a := lt_min (lt_min zero_lt_one (div_pos hα hθ)) (div_pos hp₀ hd)
  have ha₁ : a ≤ 1 := (min_le_left ..).trans (min_le_left ..)
  have hpa : 0 < p-a := by linarith
  let t := a/p
  let γ := (m-θ*a)*p/(p-a)
  have ht : 0 < t := div_pos ha hp₀
  have ht₁ : t < 1 := (div_lt_one hp₀).2 (by linarith)
  have upper := (le_div_iff₀ hd).mp (show a ≤ p/(3*(θ*p-1)) from min_le_right ..)
  have range : γ ∈ Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hpa).2
      nlinarith only [upper,mul_nonneg (sub_nonneg.mpr hm.1) hp₀.le]
    · apply (div_le_iff₀ hpa).2
      nlinarith only [hp₀.le,mul_nonneg (sub_nonneg.mpr hm.2) hp₀.le,mul_nonneg (sub_nonneg.mpr hpθ) ha.le]
  have e1 : (1-p/a)*t+(1-t)=0 := by dsimp [t]; field_simp [ha.ne',hp₀.ne']; ring
  have e2 : γ*(1-t)=m-θ*a := by dsimp [γ,t]; field_simp [hp₀.ne',hpa.ne']
  have e3 : p*t=a := by dsimp [t]; field_simp
  let X := ε^(1-p/a)*ω^p
  let Y := ε*r^γ
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have xy : X^t*Y^(1-t)=r^m*(ω/r^θ)^a := by
    dsimp only [X,Y]
    rw [Real.mul_rpow (Real.rpow_nonneg he.le _) (Real.rpow_nonneg homega _),
      Real.mul_rpow he.le (Real.rpow_nonneg hr.le _),←Real.rpow_mul he.le,←Real.rpow_mul homega,
      ←Real.rpow_mul hr.le,e2,e3]
    calc
      _ = (ε^((1-p/a)*t)*ε^(1-t))*r^(m-θ*a)*ω^a := by ring
      _ = _ := by rw [←Real.rpow_add he,e1,Real.rpow_zero,one_mul,Real.rpow_sub hr,
        Real.div_rpow homega (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le]; ring
  have b := endpointBulkExponent_from_holder hp₀ hθ hα (by linarith : 1 < θ*p)
  change p+p/a-1 = _ at b
  have bx : X ≤ g/ε^(endpointBulkExponent p θ α) := calc
    _ ≤ ε^(1-p/a)*(ε^(-p)*g) := mul_le_mul_of_nonneg_left osc (Real.rpow_nonneg he.le _)
    _ = _ := by rw [←mul_assoc,←Real.rpow_add he,show 1-p/a+ -p = -endpointBulkExponent p θ α by linarith,
      Real.rpow_neg he.le]; ring
  have by' := mul_le_mul_of_nonneg_left (BulkRegime.density_power_le hr range) he.le
  have young := Real.geom_mean_le_arith_mean2_weighted ht.le (sub_nonneg.mpr ht₁.le) hX hY (by ring : t+(1-t)=1)
  rw [←xy]
  change Y ≤ _ at by'
  nlinarith only [young,mul_nonneg (sub_nonneg.mpr ht₁.le) hX,mul_nonneg ht.le hY,bx,by']

/-- The gas modulus on a small comparison ball contributes the stated
interpolated power of ε after Morrey's inequality and Young's inequality. -/
theorem SmallBallScale.endpoint_bulk {D N : Density} {T S : MatrixGradient} {p θ α ε C : ℝ}
    {c : Position} (s : SmallBallScale N (3*ε⁻¹) c) (M : MatrixSobolevMorrey p C)
    (hp : 3 < p) (hθ : 0 < θ) (hα : 0 < α) (hpθ : 2 ≤ p*θ) (he : 0 < ε) (hC : 0 ≤ C)
    (reg : DensityRegular D p θ S T) (eq : N.matrix =ᵐ[volume] D.matrix)
    (cn : Continuous (N.power θ)) (small : s.omega θ ≤ s.r^θ) :
    smallGasBulk s.r (s.omega θ) θ (min 1 (α/θ)) ≤
      8*endpointTileCost D T p (endpointBulkExponent p θ α) ε C c := by
  let g := tileMorreyCoefficient p C * ballAverage (3*ε⁻¹) (rootPower T p) c
  have hg : 0 ≤ g := mul_nonneg
    (mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC)
    (ballAverage_nonnegative _ (rootPower_nonneg T p) c)
  let mass := ε*bulkAverage D Phase.zero (3*ε⁻¹) c
  let grad := g/ε^(endpointBulkExponent p θ α)
  have grad0 : 0 ≤ grad := div_nonneg hg (Real.rpow_nonneg he.le _)
  have m0 : 0 ≤ mass := mul_nonneg he.le (ballAverage_nonnegative _ (massDensity_nonneg D Phase.zero) c)
  have e : endpointTileCost D T p (endpointBulkExponent p θ α) ε C c = mass+grad := rfl
  have hp₀ : 0 < p := by linarith
  have hpθ' : 2 ≤ θ*p := by rwa [mul_comm]
  have phase := phaseAdmissible_zero D hp₀ (0 : MatrixGradient)
  have massBound := mul_le_mul_of_nonneg_left (charge_scale_le_bulkAverage reg phase s eq (by positivity)) he.le
  change ε*(s.r+s.r^2) ≤ ε*(4*bulkAverage D Phase.zero (3*ε⁻¹) c) at massBound
  rw [mul_left_comm ε 4] at massBound
  change _ ≤ 4*mass at massBound
  obtain ⟨x,hx,y,hy,h⟩ := s.omega_max θ hθ
  have regN := densityRegular_of_ae eq.symm reg
  have osc := tile_ball_morrey_average he c (tile_ball_morrey_scale he c (M.theta_pair hp regN cn (by positivity) x hx y hy))
  rw [←h] at osc
  let a := min (min 1 (α/θ)) (p/(3*(θ*p-1)))
  have ha : 0 ≤ a := le_min (le_min zero_le_one (div_nonneg hα.le hθ.le))
    (div_nonneg hp₀.le (by linarith))
  let u := s.omega θ/s.r^θ
  have hu : 0 ≤ u := div_nonneg (s.omega_nonneg θ hθ) (Real.rpow_nonneg s.r_nonneg _)
  have hu₁ : u ≤ 1 := div_le_one_of_le₀ small (Real.rpow_nonneg s.r_nonneg _)
  have shrink := Real.rpow_le_rpow_of_exponent_ge' hu hu₁ ha (show a ≤ min 1 (α/θ) from min_le_left ..)
  have part {m : ℝ} (hm : m ∈ Icc (4/3:ℝ) (5/3)) : s.r^m*u^(min 1 (α/θ)) ≤ 4*mass+grad := by
    rcases s.r_nonneg.eq_or_lt with hz | hr
    · rw [←hz,Real.zero_rpow (by linarith [hm.1] : m ≠ 0),zero_mul]
      positivity
    have bound := endpoint_young hp hθ hα hpθ' hr he (s.omega_nonneg θ hθ) hm osc
    exact (mul_le_mul_of_nonneg_left shrink (Real.rpow_nonneg hr.le _)).trans (bound.trans (add_le_add massBound le_rfl))
  unfold smallGasBulk
  rw [e,add_mul]
  linarith only [part (m := 4/3) (by constructor <;> norm_num),part (m := 5/3) (by constructor <;> norm_num),grad0]

end TSGA.ManyBody
