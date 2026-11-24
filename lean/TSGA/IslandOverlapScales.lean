import TSGA.IslandCoulombKernel

/-! # The length scales in the overlap and thin-shell estimates -/

noncomputable section
namespace TSGA.ManyBody
open TSGA.Islands

def overlapScale (L : ℝ) := (1+Real.exp 1)*islandCoulombConstant*L^4

theorem overlapScale_nonneg (L : ℝ) : 0 ≤ overlapScale L := by
  unfold overlapScale
  have h := zero_le_one.trans islandCoulombConstant_one_le
  positivity

/-- The cube mass, boundary-layer mass and pointwise hit intensity are
the three inputs to the radius and width calculation. -/
theorem island_overlap_coefficients {L v r δ t c d : ℝ} (hL : 1 ≤ L) (hv : 0 < v) (hv' : v ≤ 1)
    (hr : 0 < r) (hδ : 0 < δ) (ht : 0 ≤ t) (ht' : t ≤ L*v*δ/r)
    (hc : |c| ≤ L*δ/r) (hd : |d| ≤ L/v) :
    c^2*(islandCoulombConstant*((L*r)^3)^(2/3:ℝ)*v) +
      (islandCoulombConstant*(L^3*r^2*δ)^(2/3:ℝ)*(L*v*δ/r) +
        Real.exp 1*t^2*(islandCoulombConstant*(L*r)^2)) ≤
        overlapScale L*v*(δ^2+r^(1/3:ℝ)*δ^(5/3:ℝ)) ∧
    d^2*(islandCoulombConstant*((L*r)^3)^(2/3:ℝ)*v) ≤
        overlapScale L*(r^2/v) := by
  let C := islandCoulombConstant
  let E := Real.exp 1
  have hC : 0 ≤ C := zero_le_one.trans islandCoulombConstant_one_le
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hL' := zero_lt_one.trans_le hL
  have cube {x : ℝ} (hx : 0 ≤ x) : (x^3)^(2/3:ℝ) = x^2 := by
    rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
    norm_num
  have shell : C*(L^3*r^2*δ)^(2/3:ℝ)*(L*v*δ/r) =
      C*L^3*v*(r^(1/3:ℝ)*δ^(5/3:ℝ)) := by
    rw [Real.mul_rpow (by positivity) hδ.le,Real.mul_rpow (by positivity) (sq_nonneg r),cube hL'.le,
      ← Real.rpow_natCast r 2,← Real.rpow_mul hr.le]
    have rpow : r^(((2:ℕ):ℝ)*(2/3:ℝ)) = r^(1/3:ℝ)*r := by
      convert (Real.rpow_add_one hr.ne' (1/3:ℝ)) using 1; norm_num
    have dpow : δ^(5/3:ℝ) = δ^(2/3:ℝ)*δ := by
      convert (Real.rpow_add_one hδ.ne' (2/3:ℝ)) using 1; norm_num
    rw [rpow,dpow]; field_simp
  have full := cube (mul_nonneg hL'.le hr.le)
  have cs : c^2 ≤ (L*δ/r)^2 := (sq_le_sq).mpr (hc.trans (le_abs_self _))
  have ds : d^2 ≤ (L/v)^2 := (sq_le_sq).mpr (hd.trans (le_abs_self _))
  have ts : t^2 ≤ (L*v*δ/r)^2 := (sq_le_sq₀ ht (by positivity)).mpr ht'
  have first : c^2*(C*(L*r)^2*v) ≤ C*L^4*v*δ^2 := by
    calc
      _ ≤ (L*δ/r)^2*(C*(L*r)^2*v) := mul_le_mul_of_nonneg_right cs (by positivity)
      _ = _ := by field_simp
  have extra : E*t^2*(C*(L*r)^2) ≤ E*C*L^4*v*δ^2 := by
    calc
      _ ≤ E*(L*v*δ/r)^2*(C*(L*r)^2) := by gcongr
      _ = (E*C*L^4*δ^2)*v^2 := by field_simp
      _ ≤ (E*C*L^4*δ^2)*v := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hv')]) (by positivity)
      _ = _ := by ring
  have hLpow : L^3 ≤ L^4 := by simpa only [pow_succ L 3] using (le_mul_of_one_le_right (by positivity : 0 ≤ L^3) hL)
  have bg : C*L^3*v*(r^(1/3:ℝ)*δ^(5/3:ℝ)) ≤ C*L^4*v*(r^(1/3:ℝ)*δ^(5/3:ℝ)) := by gcongr
  have added : d^2*(C*(L*r)^2*v) ≤ C*L^4*(r^2/v) := by
    calc
      _ ≤ (L/v)^2*(C*(L*r)^2*v) := mul_le_mul_of_nonneg_right ds (by positivity)
      _ = C*L^4*(r^2/v) := by field_simp
  change c^2*(C*((L*r)^3)^(2/3:ℝ)*v)+(C*(L^3*r^2*δ)^(2/3:ℝ)*(L*v*δ/r)+E*t^2*(C*(L*r)^2)) ≤
      ((1+E)*C*L^4)*v*(δ^2+r^(1/3:ℝ)*δ^(5/3:ℝ)) ∧ _ ≤ ((1+E)*C*L^4)*(r^2/v)
  rw [full,shell]
  constructor
  · linarith only [first,bg,extra,show 0 ≤ E*C*L^4*v*(r^(1/3:ℝ)*δ^(5/3:ℝ)) by positivity]
  · apply added.trans; linarith only [show 0 ≤ E*C*L^4*(r^2/v) by positivity]

end TSGA.ManyBody
