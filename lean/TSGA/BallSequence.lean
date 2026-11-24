import TSGA.SSWDomain
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # A concrete admissible domain sequence for the SSW limit -/

noncomputable section

namespace TSGA.SSW.DomainSequence

open Filter MeasureTheory Metric
open scoped Topology

def unitVolume : ℝ := regionVolume (ball (0 : Position) 1)

theorem unitVolume_pos : 0 < unitVolume :=
  ENNReal.toReal_pos ((isOpen_ball.measure_pos volume (nonempty_ball.mpr zero_lt_one)).ne')
    (measure_ball_lt_top (μ := (volume : Measure Position)) (x := (0 : Position)) (r := 1)).ne

theorem ball_volume {R : ℝ} (hR : 0 ≤ R) :
    regionVolume (ball (0 : Position) R) = R^3 * unitVolume := by
  change (volume (ball (0 : Position) R)).toReal = R^3 * (volume (ball (0 : Position) 1)).toReal
  rw [Measure.addHaar_ball volume 0 hR, ENNReal.toReal_mul]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_ofReal (pow_nonneg hR 3)]

/-- For thickness at most the radius, the boundary layer is contained in the
difference of the concentric balls of radii R+r and R−r. -/
theorem ball_frontier_volume_le {R r : ℝ} (hr : 0 < r) (hle : r ≤ R) :
    volume (thickening r (frontier (ball (0 : Position) R))) ≤
      ENNReal.ofReal (8 * regionVolume (ball (0 : Position) 1) * r * R^2) := by
  let out := ball (0 : Position) (R+r)
  let inn := ball (0 : Position) (R-r)
  have hio : inn ⊆ out := ball_subset_ball (by linarith)
  have hsub : thickening r (frontier (ball (0 : Position) R)) ⊆ out \ inn := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
    have hd : dist y 0 = R := mem_sphere.mp (frontier_ball_subset_sphere hy)
    constructor
    · change dist x 0 < R+r
      linarith only [dist_triangle x y 0, hxy, hd]
    · change ¬dist x 0 < R-r
      have ht := dist_triangle y x 0
      rw [dist_comm y x] at ht
      linarith only [ht, hxy, hd]
  have hfin : volume out ≠ ⊤ := measure_ball_lt_top.ne
  have hδ : volume.real (out \ inn) = (R+r)^3 * unitVolume - (R-r)^3 * unitVolume := by
    rw [measureReal_sdiff hio measurableSet_ball hfin]
    exact congrArg₂ (· - ·) (ball_volume (by linarith : 0 ≤ R+r)) (ball_volume (sub_nonneg.mpr hle))
  calc
    _ ≤ volume (out \ inn) := measure_mono hsub
    _ = ENNReal.ofReal (volume.real (out \ inn)) := (ofReal_measureReal (measure_ne_top_of_subset Set.sdiff_subset hfin)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [hδ]
      change _ ≤ 8 * unitVolume * r * R^2
      have hrr : r^2 ≤ R^2 := (sq_le_sq₀ hr.le (hr.le.trans hle)).2 hle
      nlinarith only [mul_le_mul_of_nonneg_right hrr (mul_nonneg hr.le unitVolume_pos.le)]

theorem ball_boundary : ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 0 < r →
    r ≤ regionVolume (ball (0 : Position) R) ^ (1/3 : ℝ) / C →
    volume (thickening r (frontier (ball (0 : Position) R))) ≤
      ENNReal.ofReal (C * r * regionVolume (ball (0 : Position) R) ^ (2/3 : ℝ)) := by
  let a := unitVolume ^ (1/3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos unitVolume_pos _
  have ha3 : a^3 = unitVolume := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul unitVolume_pos.le]; norm_num
  refine ⟨8*a, by positivity, ?_⟩
  intro R r hR hr hsmall
  have hvol : regionVolume (ball (0 : Position) R) = (R*a)^3 := by rw [ball_volume hR.le, mul_pow, ha3]
  have hRa : 0 ≤ R*a := mul_nonneg hR.le ha.le
  have hroot : regionVolume (ball (0 : Position) R) ^ (1/3:ℝ) = R*a := by
    rw [hvol, ← Real.rpow_natCast, ← Real.rpow_mul hRa]; norm_num
  have hsquare : regionVolume (ball (0 : Position) R) ^ (2/3:ℝ) = (R*a)^2 := by
    rw [hvol, ← Real.rpow_natCast, ← Real.rpow_mul hRa]; norm_num
  rw [hroot, le_div_iff₀ (by positivity)] at hsmall
  have hle : r ≤ R := (mul_le_mul_iff_left₀ ha).1 (by nlinarith only [hsmall, mul_pos hr ha])
  apply (ball_frontier_volume_le hr hle).trans
  apply ENNReal.ofReal_le_ofReal
  change 8 * unitVolume * r * R^2 ≤ _
  rw [hsquare, ← ha3]
  exact le_of_eq (by ring)

/-- Balls of radius n+1 centered at zero, with outer smoothing width one
and the prescribed mollifier. -/
def balls (η : Mollifier) : DomainSequence := by
  let R (n : ℕ) : ℝ := (n : ℝ) + 1
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  have hlim : Tendsto R atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hvol : Tendsto (fun n => regionVolume (ball (0 : Position) (R n))) atTop atTop := by
    have ht := ((tendsto_pow_atTop (α := ℝ) (by decide : (3:ℕ) ≠ 0)).comp hlim).atTop_mul_const unitVolume_pos
    simpa only [Function.comp_apply, ball_volume (hR _).le] using ht
  have hlen : Tendsto (fun n => regionVolume (ball (0 : Position) (R n)) ^ (1/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp hvol
  exact {
    region := fun n => ball 0 (R n)
    region_open := fun _ => isOpen_ball
    region_connected := fun n => isConnected_ball (hR n)
    region_bounded := fun _ => isBounded_ball
    vol_tendsto := hvol
    boundary := by
      obtain ⟨C, hC, hb⟩ := ball_boundary
      exact ⟨C, hC, fun n r => hb (R n) r (hR n)⟩
    delta := fun _ => 1
    delta_pos := fun _ => zero_lt_one
    delta_ratio := hlen.const_div_atTop 1
    delta_product := by simpa only [one_mul] using hlen
    mollifier := η }

@[simp] theorem balls_region (η : Mollifier) (n : ℕ) :
    (balls η).region n = ball (0 : Position) ((n : ℝ) + 1) := rfl

@[simp] theorem balls_delta (η : Mollifier) (n : ℕ) : (balls η).delta n = 1 := rfl

@[simp] theorem balls_mollifier (η : Mollifier) : (balls η).mollifier = η := rfl

end TSGA.SSW.DomainSequence
