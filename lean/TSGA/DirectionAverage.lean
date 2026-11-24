import TSGA.Sobolev
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average

/-! # Direction average of a finite SSW tile

Directions in three-space are sampled with the normalized surface measure on
the unit sphere. At fixed radius this is the spherical form of the normalized
rotation average in `eq:def_e_bar`.
-/

namespace TSGA.SSW

open MeasureTheory

/-- Average a wavevector-dependent energy over the sphere of radius `radius`,
using the angular measure induced by Euclidean volume in polar coordinates. -/
noncomputable def directionAverage (f : Position → ℝ) (radius : ℝ) : ℝ :=
  ⨍ ω : Metric.sphere (0 : Position) 1, f (radius • (ω : Position))
    ∂(volume : Measure Position).toSphere

@[simp] theorem directionAverage_const (c radius : ℝ) :
    directionAverage (fun _ => c) radius = c := by
  let : NeZero (volume : Measure Position).toSphere := ⟨Measure.toSphere_ne_zero volume⟩
  exact average_const _ c

@[simp] theorem directionAverage_zero (f : Position → ℝ) :
    directionAverage f 0 = f 0 := by
  unfold directionAverage
  simp only [zero_smul]
  exact directionAverage_const (f 0) 0

/-- The spherical average at a wavevector is unchanged by any orthogonal map,
in particular by every proper rotation of physical space. -/
theorem directionAverage_isometry (f : Position → ℝ) (R : Position ≃ₗᵢ[ℝ] Position)
    (q : Position) : directionAverage f ‖R q‖ = directionAverage f ‖q‖ := by
  rw [R.norm_map]

end TSGA.SSW
