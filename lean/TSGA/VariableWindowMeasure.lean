import TSGA.CoulombDilationMeasure
import TSGA.DensityMeasurability
import TSGA.RayRegularity

/-! # Measuring the constrained energy of a windowed density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

/-- Jointly Borel windows give a Borel function of their parameters, even
when the spin density is specified by an almost-everywhere representative. -/
theorem measurable_variableWindowEnergy {P : Type*} [MeasurableSpace P]
    (borel : LevyLiebBorel) {F : Position → SpinMatrix}
    (hi : ∀ i j, Integrable (fun x => F x i j)) (w : P → Position → ℝ)
    (hw : Measurable (fun z : P × Position => w z.1 z.2)) {B : ℝ}
    (bound : ∀ p x, |w p x| ≤ B) :
    Measurable (fun p => energy (fun x => (w p x : ℂ) • F x)) := by
  classical
  let m := fun i j => (hi i j).aestronglyMeasurable
  let F' := fun (x : Position) (i j : Fin 2) => (m i j).mk _ x
  have eq : F =ᵐ[volume] F' := by
    have h : ∀ i j, ∀ᵐ x ∂volume, F x i j = F' x i j := fun i j => (m i j).ae_eq_mk
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (h i)] with x hx
    exact funext fun i => funext (hx i)
  have entries (i j : Fin 2) : Measurable (fun z : P × Position =>
      ((w z.1 z.2 : ℂ) • F' z.2) i j) :=
    (Complex.measurable_ofReal.comp hw).mul ((m i j).stronglyMeasurable_mk.measurable.comp measurable_snd)
  have val (p : P) : energy (fun x => (w p x : ℂ) • F x) =
      energy (fun x => (w p x : ℂ) • F' x) :=
    energy_congr (eq.mono fun x e => congrArg (fun M : SpinMatrix => (w p x : ℂ) • M) e)
  simp_rw [val]
  apply measurable_coulomb_energy_family borel _ entries
  intro p i j
  apply memLp_one_iff_integrable.mpr
  have hi' := (hi i j).congr (m i j).ae_eq_mk
  apply (hi'.norm.const_mul B).mono' ((entries i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards with x
  change ‖(w p x : ℂ) * F' x i j‖ ≤ B * ‖F' x i j‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (bound p x) (norm_nonneg _)

/-- Positivity controls every matrix entry by the particle density. -/
theorem integrable_spin_entries {D : Density} (hm : AEMeasurable D.matrix volume)
    (hρ : Integrable D.charge) (i j : Fin 2) : Integrable (fun x => D.matrix x i j) := by
  have m := (measurable_pi_apply j).comp_aemeasurable ((measurable_pi_apply i).comp_aemeasurable hm)
  exact hρ.mono' m.aestronglyMeasurable (ae_of_all _ fun x =>
    (SSW.norm_entry_le_hs _ i j).trans (SSW.hilbertSchmidt_le_trace (D.positive x)))

end TSGA.ManyBody
