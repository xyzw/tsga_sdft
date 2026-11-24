import TSGA.CoulombShellTransport

/-! # Periodic convolution of the physical mollifier

The smoothing law is Lebesgue measure with the original mollifier density.
Translating a fundamental cube preserves the integral of any lattice-periodic
function. Applying this identity between two Fubini interchanges gives the
duality formula for every measurable periodic set.
-/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set
open scoped BoundedContinuousFunction Pointwise

private def kernelLaw (η : Mollifier) : Measure Position :=
  volume.withDensity (fun y => ENNReal.ofReal (η.kernel y))

private instance kernelLaw_probability (η : Mollifier) : IsProbabilityMeasure (kernelLaw η) := by
  constructor
  rw [kernelLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal η.integrable (ae_of_all _ η.nonneg),η.mass]
  norm_num

private theorem kernelLaw_support (η : Mollifier) : ∀ᵐ y ∂kernelLaw η, y ∈ tsupport η.kernel := by
  apply (ae_withDensity_iff' η.integrable.aemeasurable.ennreal_ofReal).2
  refine ae_of_all _ fun y hy => subset_closure ?_
  exact fun h => hy (by simp [h])

private def kernelProbe (η : Mollifier) (d : ℝ) (φ : Position →ᵇ ℝ) : Position →ᵇ ℝ := by
  let f (x y : Position) := φ (x+d • y)
  have bound (x y) : ‖f x y‖ ≤ ‖φ‖ := φ.norm_coe_le_norm _
  refine BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ y, f x y ∂kernelLaw η) ?_ ‖φ‖ ?_
  · apply continuous_of_dominated (bound := fun _ => ‖φ‖)
    · intro x
      exact (φ.continuous.comp (show Continuous (fun y : Position => x+d • y) by fun_prop)).aestronglyMeasurable
    · exact fun x => ae_of_all _ (bound x)
    · exact integrable_const _
    · exact ae_of_all _ fun y => φ.continuous.comp (continuous_id.add continuous_const)
  · intro x
    simpa using (norm_integral_le_of_norm_le_const (μ := kernelLaw η) (f := f x)
      (ae_of_all _ (bound x)))

/-- Change of variables from the rescaled physical convolution to a fixed
probability law. No continuity or finite-volume assumption on the set is needed. -/
private theorem smoothed_eq_kernelLaw (η : Mollifier) (S : Set Position) {d : ℝ} (hd : 0 < d)
    (x : Position) : smoothedIndicator S η d x =
      ∫ y, S.indicator (fun _ => (1:ℝ)) (x-d • y) ∂kernelLaw η := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let i := S.indicator (fun _ => (1:ℝ))
  let F := fun y => η.kernel y * i (x-d • y)
  change (∫ y, i y * η.scaled d (x-y)) = _
  rw [← integral_sub_left_eq_self (fun y => i y * η.scaled d (x-y)) volume x]
  simp only [sub_sub_self]
  change _ = ∫ y, i (x-d • y) ∂volume.withDensity _
  rw [integral_withDensity_eq_integral_toReal_smul₀ η.integrable.aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (η.nonneg _),smul_eq_mul]
  calc
    _ = (d^3)⁻¹ * ∫ y, F (d⁻¹ • y) := by
      rw [← integral_const_mul]
      congr 1
      funext y
      simp only [F,Mollifier.scaled,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
      ring
    _ = _ := by
      rw [Measure.integral_comp_inv_smul_of_nonneg volume F hd.le]
      simp [F,finrank_euclideanSpace,smul_eq_mul,hd.ne']

private theorem cube_periodic_translate (g : Position → ℝ) (hp : unitPeriodic g) (v : Position) :
    (∫ x in latticeCube 1 0, g (v+x)) = ∫ x in latticeCube 1 0, g x := by
  let : Countable (latticeShift 1).range := Set.Countable.to_subtype
    (s := Set.range (latticeShift 1)) (Set.countable_range _)
  have h := latticeCube_fundamental (by norm_num : (0:ℝ)<1)
  calc
    _ = ∫ x in v +ᵥ latticeCube 1 0, g x :=
      ((measurePreserving_add_left volume v).setIntegral_image_emb
        (Homeomorph.addLeft v).measurableEmbedding g (latticeCube 1 0)).symm
    _ = _ := (h.vadd_of_comm v).setIntegral_eq h (by
      rintro ⟨_,m,rfl⟩ x
      exact hp m x)

private theorem cube_shift_indicator (S : Set Position)
    (hs : ∀ m x, latticeShift 1 m+x ∈ S ↔ x ∈ S)
    (φ : Position →ᵇ ℝ) (hp : unitPeriodic φ) (v : Position) :
    (∫ x in latticeCube 1 0, S.indicator (fun _ => (1:ℝ)) (x-v) * φ x) =
      ∫ x in latticeCube 1 0, S.indicator (fun _ => (1:ℝ)) x * φ (x+v) := by
  classical
  let g := fun x => S.indicator (fun _ => (1:ℝ)) x * φ (x+v)
  have hgp : unitPeriodic g := by
    intro m x
    dsimp only [g]
    rw [add_assoc,hp m (x+v)]
    by_cases hx : x ∈ S <;> simp [hx,hs]
  calc
    _ = ∫ x in latticeCube 1 0, g (-v+x) := by
      congr 1
      funext x
      simp [g,sub_eq_add_neg,add_comm]
    _ = _ := cube_periodic_translate g hgp (-v)

/-- The standard mollifier on the periodic unit cube supplies every
component of the periodic kernel calculus. -/
def Mollifier.periodicKernelCalculus (η : Mollifier) : PeriodicKernelCalculus η where
  law := kernelLaw η
  probability := inferInstance
  support := kernelLaw_support η
  probe := kernelProbe η
  probe_eq := fun _ _ _ => rfl
  convolution := by
    classical
    intro S hS hs d hd
    let i := S.indicator (fun _ => (1:ℝ))
    have hi : Measurable i := measurable_const.indicator hS
    have hib (x) : ‖i x‖ ≤ 1 := by by_cases hx : x ∈ S <;> simp [i,hx]
    have hj : Measurable (fun p : Position × Position => i (p.1-d • p.2)) :=
      hi.comp (show Measurable (fun p : Position × Position => p.1-d • p.2) by fun_prop)
    have hsm : smoothedIndicator S η d = fun x => ∫ y, i (x-d • y) ∂kernelLaw η :=
      funext (smoothed_eq_kernelLaw η S hd)
    refine ⟨by rw [hsm]; exact hj.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,?_⟩
    intro φ hp
    let C := latticeCube 1 0
    have vpos : 0 < volume.real C := by
      change 0 < regionVolume (latticeCube 1 0)
      rw [latticeCube_volume (by norm_num : (0:ℝ)<1)]
      norm_num
    let : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp vpos).2.ne
    have ha : Integrable (fun z : Position × Position => i (z.1-d • z.2)*φ z.1)
        ((volume.restrict C).prod (kernelLaw η)) :=
      (integrable_const ‖φ‖).mono'
        ((hj.mul (φ.continuous.measurable.comp measurable_fst)).aestronglyMeasurable)
        (ae_of_all _ fun z => (norm_mul_le _ _).trans
          ((mul_le_mul (hib _) (φ.norm_coe_le_norm _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)))
    have hb : Integrable (fun z : Position × Position => i z.1*φ (z.1+d • z.2))
        ((volume.restrict C).prod (kernelLaw η)) :=
      (integrable_const ‖φ‖).mono'
        (((hi.comp measurable_fst).mul (φ.continuous.measurable.comp
          (show Measurable (fun p : Position × Position => p.1+d • p.2) by fun_prop))).aestronglyMeasurable)
        (ae_of_all _ fun z => (norm_mul_le _ _).trans
          ((mul_le_mul (hib _) (φ.norm_coe_le_norm _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)))
    calc
      _ = ∫ x in C, ∫ y, i (x-d • y)*φ x ∂kernelLaw η := by
        simp_rw [integral_mul_const,hsm]
        rfl
      _ = ∫ y, (∫ x in C, i (x-d • y)*φ x) ∂kernelLaw η :=
        integral_integral_swap ha
      _ = ∫ y, (∫ x in C, i x*φ (x+d • y)) ∂kernelLaw η :=
        integral_congr_ae (ae_of_all _ fun y => cube_shift_indicator S hs φ hp (d • y))
      _ = ∫ x in C, ∫ y, i x*φ (x+d • y) ∂kernelLaw η :=
        (integral_integral_swap hb).symm
      _ = ∫ x in C, S.indicator (kernelProbe η d φ) x := by
        simp_rw [integral_const_mul]
        congr 1
        funext x
        by_cases hx : x ∈ S <;> simp [i,hx,kernelProbe]
      _ = _ := setIntegral_indicator hS

end TSGA.SSW
