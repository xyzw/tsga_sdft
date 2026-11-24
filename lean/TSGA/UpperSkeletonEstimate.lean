import TSGA.ActualTileLocalization

/-! # The signed upper bound for the periodic skeleton of Theorem 4.10 -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set TSGA.Localization SSW Metric

/-- The two contributions of the one-body trial are its local density term
and the square-root kinetic energy. -/
def variableWindowUpper (H : FiniteEnergyInputs) (D : Density) (S : MatrixGradient)
    (b m s : ℝ) : ℝ :=
  H.interiorConstant*(b^(2/3:ℝ)*(m*chargeMoment D (5/3))+2*(m*sqrtKinetic S)+2*(s*∫ x, D.charge x))

theorem FiniteEnergyInputs.variable_windows_upper (H : FiniteEnergyInputs)
    (product : WeakScalarMatrixProduct) {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S)
    (p₅ : Integrable fun x => D.charge x^(5/3:ℝ)) (p₄ : Integrable fun x => D.charge x^(4/3:ℝ))
    {P : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ]
    (w : P → Position → ℝ) (g : P → Position → Position) {b m s : ℝ}
    (bb : 0 ≤ b) (unit : ∀ j x, w j x ∈ Icc 0 b)
    (wm : AEStronglyMeasurable (fun z : P × Position => w z.1 z.2) (μ.prod volume))
    (gm : AEStronglyMeasurable (fun z : P × Position => g z.1 z.2) (μ.prod volume))
    (weak : ∀ᵐ j ∂μ, ∀ i, WeakPartialOn univ i (fun x => √(w j x)) (fun x => g j x i))
    (m₀ : 0 ≤ m) (s₀ : 0 ≤ s)
    (mean : ∀ᵐ x, Integrable (fun j => w j x) μ ∧ (∫ j, w j x ∂μ) ≤ m)
    (fisher : ∀ᵐ x, Integrable (fun j => ‖g j x‖^2) μ ∧ (∫ j, ‖g j x‖^2 ∂μ) ≤ s)
    (em : AEStronglyMeasurable (fun j => energy (fun x => (w j x : ℂ) • D.matrix x)) μ) :
    let F := fun j x => (w j x : ℂ) • D.matrix x
    (∫ j, energy (F j) ∂μ) ≤ variableWindowUpper H D S b m s := by
  intro F
  have ei := (H.variable_windows_average product reg p₅ p₄ w g bb unit wm gm weak m₀ s₀ mean fisher em).2.1
  have kin : Integrable (kineticDensity S) := reg.grad.integrable_sq
  have w₀ := fun j x => (unit j x).1
  have a := weighted_profile_average p₅ (fun x => Real.rpow_nonneg (D.charge_nonneg x) _) wm w₀ m₀ mean
  have k := weighted_profile_average kin (fun x => sq_nonneg _) wm w₀ m₀ mean
  have d := weighted_profile_average reg.charge D.charge_nonneg (gm.norm.pow 2)
    (fun j x => sq_nonneg _) s₀ fisher
  let A := fun j => ∫ x, D.charge x^(5/3:ℝ)*w j x
  let K := fun j => ∫ x, kineticDensity S x*w j x
  let G := fun j => ∫ x, D.charge x*‖g j x‖^2
  let Q := fun j => H.interiorConstant*(b^(2/3:ℝ)*A j+2*K j+2*G j)
  have point : ∀ᵐ j ∂μ, energy (F j) ≤ Q j := by
    filter_upwards [weak,d.1.prod_right_ae] with j hj dj
    let N := windowDensity D (w j) (w₀ j)
    have id : N.matrix = F j := by ext x i v; exact Complex.real_smul
    obtain ⟨Γ,rep,inter,upper⟩ := H.window_trial product reg (unit j) hj dj p₅
    have high := levyLieb_le rep
    simp_rw [mul_comm (w j _)] at upper
    rw [←id]
    change levyLieb N.matrix-hartree N.charge ≤ Q j
    dsimp only [Q,A,K,G,N] at *
    linarith only [high,upper,inter]
  have ai : Integrable A μ := a.1.integral_prod_left
  have ki : Integrable K μ := k.1.integral_prod_left
  have gi : Integrable G μ := d.1.integral_prod_left
  have i₀ : Integrable (fun j => b^(2/3:ℝ)*A j+2*K j) μ := (ai.const_mul _).add (ki.const_mul _)
  have i₁ : Integrable (fun j => b^(2/3:ℝ)*A j+2*K j+2*G j) μ := i₀.add (gi.const_mul _)
  apply (integral_mono_ae ei (i₁.const_mul H.interiorConstant) point).trans
  dsimp only [variableWindowUpper]
  rw [integral_const_mul,integral_add i₀ (gi.const_mul _),integral_add (ai.const_mul _) (ki.const_mul _)]
  simp only [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left a.2 (Real.rpow_nonneg bb _)) (mul_le_mul_of_nonneg_left k.2 (by norm_num)))
    (mul_le_mul_of_nonneg_left d.2 (by norm_num))) H.interiorConstant_nonneg

private theorem weak_scale_upper {u v : Position → ℝ} {i : Fin 3} (h : WeakPartialOn univ i u v) (c : ℝ) :
    WeakPartialOn univ i (fun x => c*u x) (fun x => c*v x) := by
  refine ⟨h.1.smul c,h.2.1.smul c,?_⟩
  intro ψ hψ hc hs
  have e := congrArg (c * ·) (h.2.2 ψ hψ hc hs)
  simp only [smul_eq_mul,mul_neg,← integral_const_mul] at e
  simpa only [smul_eq_mul,mul_left_comm c] using e

theorem FiniteEnergyInputs.variable_skeleton_upper (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S)
    (entries : ∀ i j, Integrable (fun x => D.matrix x i j))
    (p₅ : Integrable fun x => D.charge x^(5/3:ℝ)) (p₄ : Integrable fun x => D.charge x^(4/3:ℝ))
    {η : Mollifier} (sk : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {b d : ℝ} (hd : 0 < d) (hsc : d ≤ b/2) (R : Position ≃ₗᵢ[ℝ] Position) :
    let μ := latticeShiftMeasure b
    let F := fun τ => latticeBlockDensity b d η R D.matrix τ none
    (∫ τ, energy (F τ) ∂μ) ≤ variableWindowUpper H D S 2 (2*(sk.coefficient*(d/b))) (2*(sk.coefficient/(b*d))) := by
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
  apply H.variable_windows_upper product reg p₅ p₄ w g (by norm_num) unit wm.aestronglyMeasurable gm
  · filter_upwards [dh] with τ hτ
    intro i
    simp_rw [wn,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact weak_scale_upper (hτ i) _
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
