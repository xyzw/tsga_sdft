import TSGA.TetrahedronBoundary
import TSGA.SkeletonRays

/-! # Radial flux in a physical tetrahedron

The maximum of the four normalized face coordinates is the homothetic
radius. Its sublevel sets are precisely the concentric tetrahedra.
-/
noncomputable section
namespace TSGA.SSW
open MeasureTheory Set TSGA.Skeleton

def tetrahedronRadius (x : Position) : ℝ :=
  max (4*(|x 2|-x 1)) (max (8*(x 1-x 0)) (8*x 0))

theorem tetrahedronRadius_lt {x : Position} {r : ℝ} :
    tetrahedronRadius x < r ↔ x ∈ tetrahedron r := by
  unfold tetrahedronRadius tetrahedron
  simp only [max_lt_iff,mem_ofPred_eq]
  constructor <;> rintro ⟨h₁,h₂,h₃⟩ <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem tetrahedronRadius_smul {t : ℝ} (ht : 0 ≤ t) (x : Position) :
    tetrahedronRadius (t • x) = t * tetrahedronRadius x := by
  unfold tetrahedronRadius
  simp only [PiLp.smul_apply, smul_eq_mul,abs_mul,abs_of_nonneg ht, mul_max_of_nonneg _ _ ht]
  congr 1 <;> ring_nf

theorem continuous_tetrahedronRadius : Continuous tetrahedronRadius := by
  unfold tetrahedronRadius
  fun_prop

/-- Exact fractional volume of a shell of relative thickness s. -/
theorem tetrahedron_shell_volume {s : ℝ} (hs : 0 ≤ s) (hu : s < 1) :
    volume.real {x : Position | x ∈ tetrahedron 1 ∧ 1-s ≤ tetrahedronRadius x} =
      shellFraction s * regionVolume (tetrahedron 1) := by
  have he : {x : Position | x ∈ tetrahedron 1 ∧ 1-s ≤ tetrahedronRadius x} =
      tetrahedron 1 \ tetrahedron (1-s) := by
    ext x
    simp only [mem_ofPred_eq,mem_sdiff,← tetrahedronRadius_lt,not_lt]
  have hfin := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos (by norm_num : (0:ℝ)<1))).2.ne
  rw [he, measureReal_sdiff (tetrahedron_mono (show 1-s ≤ 1 by linarith))
    (tetrahedron_open _).measurableSet hfin]
  change regionVolume (tetrahedron 1) - regionVolume (tetrahedron (1-s)) = _
  rw [tetrahedron_volume (by norm_num : (0:ℝ)<1),tetrahedron_volume (sub_pos.mpr hu)]
  dsimp [shellFraction]
  ring

/-- The primitive divided by the three-dimensional radial Jacobian
factor, continued by zero outside the cell. -/
def shellFluxFactor (s t : ℝ) : ℝ := if t ≤ 1 then rayPrimitive s t / t^3 else 0

theorem shellFluxFactor_face {s : ℝ} (hs : 0 < s) (hu : s ≤ 1/2) : shellFluxFactor s 1 = 0 := by
  simp [shellFluxFactor,rayPrimitive_outer hs hu]

private theorem deriv_tail {u t : ℝ} (h : t ≠ 1-u) :
    HasDerivAt (tailPrimitive u) ((if 1-u < t then 1 else 0)*t^2) t := by
  rcases lt_or_gt_of_ne h with hl | hr
  · have eqn : tailPrimitive u =ᶠ[nhds t] (fun _ => 0) :=
      (gt_mem_nhds hl).mono fun r hr => by simp [tailPrimitive,not_le.mpr hr]
    simpa only [ite_eq_right (not_lt.mpr hl.le),zero_mul] using
      (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq eqn
  · have eqn : tailPrimitive u =ᶠ[nhds t] (fun r => (r^3-(1-u)^3)/3) :=
      (lt_mem_nhds hr).mono fun r hr => by simp [tailPrimitive,hr.le]
    have hd := (((hasDerivAt_pow 3 t).sub_const ((1-u)^3)).div_const 3).congr_of_eventuallyEq eqn
    rw [ite_eq_left hr,one_mul]
    apply hd.congr_deriv
    norm_num

/-- The divergence of x times the radial factor recovers the unregularized
charge on every open shell. The factor vanishes on the external face. -/
theorem shellFluxFactor_divergence {s t : ℝ} (ht : 0 < t) (hu : t < 1)
    (h₁ : t ≠ 1-s) (h₂ : t ≠ 1-s/2) :
    let charge := shellCoefficient s * (if 1-s/2 < t then 1 else 0) - (if 1-s < t then 1 else 0)
    ∃ d, HasDerivAt (shellFluxFactor s) d t ∧ 3*shellFluxFactor s t + t*d = charge := by
  intro charge
  have hd := ((deriv_tail h₂).const_mul (shellCoefficient s)).sub (deriv_tail h₁)
  change HasDerivAt (rayPrimitive s) _ t at hd
  have heq : shellFluxFactor s =ᶠ[nhds t] (fun r => rayPrimitive s r / r^3) :=
    (gt_mem_nhds hu).mono fun r hr => by simp [shellFluxFactor,hr.le]
  have h := (hd.div (hasDerivAt_pow 3 t) (pow_ne_zero _ ht.ne')).congr_of_eventuallyEq heq
  refine ⟨_,h,?_⟩
  dsimp only [shellFluxFactor,charge]
  rw [ite_eq_left hu.le]
  field_simp [ht.ne']
  ring

/-- One component of the compactly supported physical flux. -/
def tetrahedronShellFlux (s : ℝ) (j : Fin 3) (x : Position) : ℝ :=
  x j * shellFluxFactor s (tetrahedronRadius x)

theorem tetrahedronShellFlux_L2 {s : ℝ} (hs : 0 < s) (hu : s ≤ 1/2) (j : Fin 3) :
    (∫ x, |tetrahedronShellFlux s j x|^2) ≤ 3 * 32^2 * regionVolume (tetrahedron 1) * s^3 := by
  classical
  let B := {x : Position | x ∈ tetrahedron 1 ∧ 1-s ≤ tetrahedronRadius x}
  have hB : MeasurableSet B := (tetrahedron_open 1).measurableSet.inter
    (measurableSet_le measurable_const continuous_tetrahedronRadius.measurable)
  have hfin := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos (by norm_num : (0:ℝ)<1))).2.ne
  have hBfin : volume B ≠ ⊤ := measure_ne_top_of_subset (fun _ h => h.1) hfin
  have hp (x : Position) : |tetrahedronShellFlux s j x| ≤ B.indicator (fun _ => 32*s) x := by
    by_cases hc : tetrahedronRadius x < 1
    · have hx := tetrahedronRadius_lt.mp hc
      have hnorm := Metric.mem_closedBall.mp (tetrahedron_subset (by norm_num : (0:ℝ)<1) hx)
      have hcoord : |x j| ≤ 2 := by
        simpa using (PiLp.norm_apply_le x j).trans (by simpa using hnorm)
      by_cases hthin : 1-s ≤ tetrahedronRadius x
      · rw [indicator_of_mem (show x ∈ B from ⟨hx,hthin⟩)]
        simpa [tetrahedronShellFlux,shellFluxFactor,hc.le,mul_div_assoc,show (16:ℝ)*2=32 by norm_num] using
          rayFlux_bound hs hu hc.le hcoord
      · rw [indicator_of_notMem (show x ∉ B from fun h => hthin h.2)]
        simp [tetrahedronShellFlux,shellFluxFactor,hc.le,rayPrimitive_off_shell hs.le (lt_of_not_ge hthin)]
    · rw [indicator_of_notMem (show x ∉ B from fun h => hc (tetrahedronRadius_lt.mpr h.1))]
      rcases eq_or_lt_of_le (le_of_not_gt hc) with he | h
      · simp [tetrahedronShellFlux,← he,shellFluxFactor_face hs hu]
      · simp [tetrahedronShellFlux,shellFluxFactor,not_le.mpr h]
  have hi : Integrable (B.indicator (fun _ => (32*s)^2)) :=
    (integrable_indicator_iff hB).2 (integrableOn_const hBfin)
  have hle := integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg |tetrahedronShellFlux s j x|) hi
    (ae_of_all _ fun x => (pow_le_pow_left₀ (abs_nonneg _) (hp x) 2).trans_eq (by
      by_cases h : x ∈ B <;> simp [h]))
  rw [integral_indicator_const _ hB,smul_eq_mul,tetrahedron_shell_volume hs.le (by linarith : s<1)] at hle
  have hfrac := mul_le_mul_of_nonneg_right (shellFraction_le hs.le (by linarith : s ≤ 1))
    (mul_nonneg (show 0 ≤ regionVolume (tetrahedron 1) from ENNReal.toReal_nonneg) (sq_nonneg (32*s)))
  linarith only [hle,hfrac]

end TSGA.SSW
