import TSGA.TetrahedronFlux
import TSGA.TetrahedralLattice

/-! # Coupling homothetic shells at different smoothing widths

Sampling both shells with the same face point and the same uniform radial
quantile moves a particle by at most a constant times the shell thickness.
The random displacements used to mollify the two shells are coupled as well.
-/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set Metric Skeleton

/-- The volume coordinate on a three-dimensional homothetic shell.
The variable v is uniform on the unit interval. -/
def shellQuantile (s v : ℝ) : ℝ := ((1-v)*(1-s)^3+v)^(1/3:ℝ)

theorem shellQuantile_bounds {s v : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    shellQuantile s v ∈ Icc (1-s) 1 := by
  have ha : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hab : (1-s)^3 ≤ 1 := by simpa using pow_le_pow_left₀ ha (show 1-s ≤ 1 by linarith [hs.1]) 3
  have lower : (1-s)^3 ≤ (1-v)*(1-s)^3+v := by nlinarith only [mul_nonneg hv.1 (sub_nonneg.mpr hab)]
  have upper : (1-v)*(1-s)^3+v ≤ 1 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hab)]
  constructor
  · have h := Real.rpow_le_rpow (pow_nonneg ha 3) lower (show (0:ℝ) ≤ 1/3 by norm_num)
    have heq : ((1-s)^3)^(1/3:ℝ) = 1-s := by
      convert Real.pow_rpow_inv_natCast (n:=3) ha (by decide) using 2
      norm_num
    rw [heq] at h
    exact h
  · exact (Real.rpow_le_rpow ((pow_nonneg ha 3).trans lower) upper (by norm_num : (0:ℝ)≤1/3)).trans_eq (by simp)

def shellSample (p : CubeOrientation) (s v : ℝ) (y k : Position) : Position :=
  (latticeChartEquiv 1 (0,p)).symm (shellQuantile s v • y) + s • k

/-- Uniform displacement of the explicitly coupled, mollified shell charges
in an actual affine cell of the unit cube. -/
theorem shellSample_dist {s v : ℝ} (hs : 0 < s) (hu : s ≤ 1/2) (hv : v ∈ Icc (0:ℝ) 1)
    {y k : Position} (hy : ‖y‖ ≤ 2) (hk : ‖k‖ ≤ 1/100) (p : CubeOrientation) :
    dist (shellSample p s v y k) (shellSample p (s/2) v y k) ≤ 3*s := by
  have a := shellQuantile_bounds (s:=s) ⟨hs.le,by linarith⟩ hv
  have b := shellQuantile_bounds (s:=s/2) ⟨by linarith,by linarith⟩ hv
  have diff : |shellQuantile s v-shellQuantile (s/2) v| ≤ s :=
    abs_le.mpr ⟨by linarith [a.1,b.2],by linarith [a.2,b.1]⟩
  apply (dist_add_add_le _ _ _ _).trans
  rw [(latticeChartEquiv 1 (0,p)).symm.dist_eq, dist_eq_norm, ← sub_smul,
    dist_eq_norm,← sub_smul,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ s-s/2 by linarith)]
  linarith only [mul_le_mul diff hy (norm_nonneg y) hs.le,
    mul_le_mul_of_nonneg_left hk (show 0 ≤ s-s/2 by linarith),hs.le]

/-- Total squared transport cost per unit volume. The removed mass is the
shell fraction and every coupled pair moves by at most 3s. -/
theorem shellSample_transport_cost {s v : ℝ} (hs : 0 < s) (hu : s ≤ 1/2) (hv : v ∈ Icc (0:ℝ) 1)
    {y k : Position} (hy : ‖y‖ ≤ 2) (hk : ‖k‖ ≤ 1/100) (p : CubeOrientation) :
    shellFraction s * dist (shellSample p s v y k) (shellSample p (s/2) v y k)^2 ≤ 27*s^3 := by
  have h := mul_le_mul (shellFraction_le hs.le (by linarith))
    (pow_le_pow_left₀ dist_nonneg (shellSample_dist hs hu hv hy hk p) 2)
    (sq_nonneg _) (show 0 ≤ 3*s by positivity)
  linarith only [h]

end TSGA.SSW
