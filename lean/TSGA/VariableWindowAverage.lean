import TSGA.VariableWindowMeasure
import TSGA.VariableWindowTrial
import TSGA.CoulombUpperBoundaryEnergy

/-! # Absolute energy of randomly placed windows of a variable density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set TSGA.Localization SSW

/-- Averaged trial and Lieb–Oxford costs, with separate contributions from
the mean scalar window and the mean square gradient of its square root. -/
def variableWindowCost (H : FiniteEnergyInputs) (D : Density) (S : MatrixGradient)
    (b m s : ℝ) : ℝ :=
  H.interiorConstant * (b^(2/3:ℝ)*(m*chargeMoment D (5/3)) +
    2*(m*sqrtKinetic S) + 2*(s*∫ x, D.charge x)) +
    H.loCoeff * b^(4/3-1:ℝ)*(m*chargeMoment D (4/3))

theorem FiniteEnergyInputs.variable_windows_average (H : FiniteEnergyInputs)
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
    (∀ᵐ j ∂μ, ∃ Γ, feasible (F j) Γ) ∧ Integrable (fun j => energy (F j)) μ ∧
      (∫ j, |energy (F j)| ∂μ) ≤ variableWindowCost H D S b m s := by
  intro F
  have kin : Integrable (kineticDensity S) := reg.grad.integrable_sq
  have w₀ := fun j x => (unit j x).1
  have a := weighted_profile_average p₅ (fun x => Real.rpow_nonneg (D.charge_nonneg x) _) wm w₀ m₀ mean
  have l := weighted_profile_average p₄ (fun x => Real.rpow_nonneg (D.charge_nonneg x) _) wm w₀ m₀ mean
  have k := weighted_profile_average kin (fun x => sq_nonneg _) wm w₀ m₀ mean
  have d := weighted_profile_average reg.charge D.charge_nonneg (gm.norm.pow 2)
    (fun j x => sq_nonneg _) s₀ fisher
  let A := fun j => ∫ x, D.charge x^(5/3:ℝ)*w j x
  let L := fun j => ∫ x, D.charge x^(4/3:ℝ)*w j x
  let K := fun j => ∫ x, kineticDensity S x*w j x
  let G := fun j => ∫ x, D.charge x*‖g j x‖^2
  let C := fun j => H.interiorConstant*(b^(2/3:ℝ)*A j+2*K j+2*G j) + H.loCoeff*b^(4/3-1:ℝ)*L j
  have c₀ := H.interiorConstant_nonneg
  have r₀ := Real.rpow_nonneg bb (2/3:ℝ)
  have l₀ := mul_nonneg H.lo_nonneg (Real.rpow_nonneg bb (4/3-1:ℝ))
  have point : ∀ᵐ j ∂μ, (∃ Γ, feasible (F j) Γ) ∧ |energy (F j)| ≤ C j := by
    filter_upwards [weak,d.1.prod_right_ae] with j hj dj
    let N := windowDensity D (w j) (w₀ j)
    have id : N.matrix = F j := by
      ext x u v
      exact Complex.real_smul
    obtain ⟨Γ,rep,inter,upper⟩ := H.window_trial product reg (unit j) hj dj p₅
    have low := le_levyLieb (M := N.matrix) ⟨_,rep⟩ (a := hartree N.charge-H.loCoeff*chargeMoment N (4/3))
      fun γ hγ => (H.liebOxford N γ hγ).trans (le_add_of_nonneg_left γ.kinetic_nonneg)
    have moment := (window_charge_moment (D := D) (unit j) (window_measurable _ (w₀ j) hj) p₄ (by norm_num)).2
    have low' := mul_le_mul_of_nonneg_left moment H.lo_nonneg
    have high := levyLieb_le rep
    have lc : 0 ≤ H.loCoeff*b^(4/3-1:ℝ)*L j := mul_nonneg l₀ (integral_nonneg fun x =>
      mul_nonneg (Real.rpow_nonneg (D.charge_nonneg x) _) (w₀ j x))
    have uc : 0 ≤ H.interiorConstant*(b^(2/3:ℝ)*A j+2*K j+2*G j) := by
      apply mul_nonneg c₀
      have ap : 0 ≤ A j := integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (D.charge_nonneg x) _) (w₀ j x)
      have kp : 0 ≤ K j := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (w₀ j x)
      have gp : 0 ≤ G j := integral_nonneg fun x => mul_nonneg (D.charge_nonneg x) (sq_nonneg _)
      positivity
    simp_rw [mul_comm (w j _)] at upper low'
    rw [← id]
    refine ⟨⟨Γ,rep⟩,abs_le.mpr ⟨?_,?_⟩⟩
    · change -C j ≤ levyLieb N.matrix-hartree N.charge
      dsimp only [C,A,L,K,G] at *
      linarith only [low,low',uc]
    · change levyLieb N.matrix-hartree N.charge ≤ C j
      dsimp only [C,A,L,K,G] at *
      linarith only [high,upper,inter,lc]
  have ai : Integrable A μ := a.1.integral_prod_left
  have li : Integrable L μ := l.1.integral_prod_left
  have ki : Integrable K μ := k.1.integral_prod_left
  have gi : Integrable G μ := d.1.integral_prod_left
  have i₀ : Integrable (fun j => b^(2/3:ℝ)*A j+2*K j) μ := (ai.const_mul _).add (ki.const_mul _)
  have i₁ : Integrable (fun j => b^(2/3:ℝ)*A j+2*K j+2*G j) μ := i₀.add (gi.const_mul _)
  have ci : Integrable C μ := (i₁.const_mul _).add (li.const_mul _)
  have ei : Integrable (fun j => energy (F j)) μ := ci.mono' em (point.mono fun j hj => hj.2)
  refine ⟨point.mono fun j hj => hj.1, ei, (integral_mono_ae ei.abs ci (point.mono fun j hj => hj.2)).trans ?_⟩
  dsimp only [C,variableWindowCost]
  rw [integral_add (i₁.const_mul _) (li.const_mul _),integral_const_mul,integral_const_mul,
    integral_add i₀ (gi.const_mul _),
    integral_add (ai.const_mul _) (ki.const_mul _)]
  simp only [integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left a.2 r₀) (mul_le_mul_of_nonneg_left k.2 (by norm_num)))
    (mul_le_mul_of_nonneg_left d.2 (by norm_num))) c₀) (mul_le_mul_of_nonneg_left l.2 l₀)

end TSGA.ManyBody
