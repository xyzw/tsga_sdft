import TSGA.VariableWindowAverage
import TSGA.CoulombUpperTrialAssembly

/-! # The periodic skeleton for a spatially varying Coulomb density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set Metric SSW TSGA.Localization

private theorem weak_scale {u v : Position → ℝ} {i : Fin 3} (h : WeakPartialOn univ i u v) (c : ℝ) :
    WeakPartialOn univ i (fun x => c*u x) (fun x => c*v x) := by
  refine ⟨h.1.smul c,h.2.1.smul c,?_⟩
  intro ψ hψ hc hs
  have e := congrArg (c * ·) (h.2.2 ψ hψ hc hs)
  simp only [smul_eq_mul,mul_neg,← integral_const_mul] at e
  simpa only [smul_eq_mul,mul_left_comm c] using e

/-- The physical skeleton is twice the normalized scalar window. Its mean
mass is bounded by 2c d/b and its mean Fisher energy by 2c/(bd). -/
theorem FiniteEnergyInputs.variable_skeleton (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S)
    (entries : ∀ i j, Integrable (fun x => D.matrix x i j))
    (p₅ : Integrable fun x => D.charge x^(5/3:ℝ)) (p₄ : Integrable fun x => D.charge x^(4/3:ℝ))
    {η : Mollifier} (sk : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {b d : ℝ} (hd : 0 < d) (hsc : d ≤ b/2) (R : Position ≃ₗᵢ[ℝ] Position) :
    let μ := latticeShiftMeasure b
    let F := fun τ => latticeBlockDensity b d η R D.matrix τ none
    (∀ᵐ τ ∂μ, ∃ Γ, feasible (F τ) Γ) ∧ Integrable (fun τ => energy (F τ)) μ ∧
      (∫ τ, |energy (F τ)| ∂μ) ≤
        variableWindowCost H D S 2 (2*(sk.coefficient*(d/b))) (2*(sk.coefficient/(b*d))) := by
  intro μ F
  have hb : 0 < b := by linarith
  let : IsProbabilityMeasure μ := latticeShiftMeasure_probability hb
  let w := fun τ x => latticeBlock b d η none (R x-τ)
  let n := normalizedSkeleton η b d R
  obtain ⟨h,_,hm,dh,ma,fa⟩ := sk.averages hd hsc R
  let g := fun τ x => √2 • h τ x
  have wn (τ x) : w τ x = 2*n τ x := by dsimp [w,n,normalizedSkeleton]; ring
  have unit (τ x) : w τ x ∈ Icc 0 2 := latticeBlock_bounds hd hsc hs none _
  have wm : Measurable (fun z : Position × Position => w z.1 z.2) :=
    (latticeBlock_measurable b hd η none).comp ((R.continuous.measurable.comp measurable_snd).sub measurable_fst)
  have gm : AEStronglyMeasurable (fun z : Position × Position => g z.1 z.2) (μ.prod volume) :=
    hm.const_smul (√2 : ℝ)
  have hg (τ x) : ‖g τ x‖^2 = 2*‖h τ x‖^2 := by
    simp [g,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt]
  apply H.variable_windows_average product reg p₅ p₄ w g (by norm_num) unit wm.aestronglyMeasurable gm
  · filter_upwards [dh] with τ hτ
    intro i
    simp_rw [wn,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact weak_scale (hτ i) _
  · positivity [sk.nonneg]
  · positivity [sk.nonneg]
  · filter_upwards [ma] with x hx
    simp_rw [wn,integral_const_mul]
    exact ⟨hx.1.const_mul _,mul_le_mul_of_nonneg_left hx.2 (by norm_num)⟩
  · filter_upwards [fa] with x hx
    simp_rw [hg,integral_const_mul]
    exact ⟨hx.1.const_mul _,mul_le_mul_of_nonneg_left hx.2 (by norm_num)⟩
  · exact (measurable_variableWindowEnergy borel entries w wm fun τ x =>
      (abs_of_nonneg (unit τ x).1).trans_le (unit τ x).2).aestronglyMeasurable

end TSGA.ManyBody
