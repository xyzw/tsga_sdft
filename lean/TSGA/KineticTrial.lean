import TSGA.KineticEnergy
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # From the smooth layer-cake trial to the kinetic upper bound

The trace identity of the localized Fermi projectors and the gradient estimate
for their matrix amplitudes are inputs about a specified one-body state.
The infimum and its constants are evaluated here.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization
open scoped ComplexOrder

def trialMoment (η : ℝ → ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), η t * t ^ (2/3 : ℝ)

def trialStiffness (η : ℝ → ℝ) : ℝ :=
  4 * ∫ t in Set.Ioi (0 : ℝ), t^2 * (deriv (fun s => Real.sqrt (η s)) t)^2

def layerAmplitude (η : ℝ → ℝ) (D : Density) (t : ℝ) (x : Position) : SpinMatrix :=
  (D.positive x).isHermitian.cfc (fun r => if r = 0 then 0 else Real.sqrt (η (t / r)))

def layerCost (V : ℝ → MatrixGradient) (x : Position) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), kineticDensity (V t) x

/-- The finite one-body trial at one smoothing parameter. These are the
projector trace and derivative formulas before minimizing in the density. -/
structure LayerTrialData (D : Density) (cTF κ₁ κ₂ ε : ℝ) where
  gamma : OneBody
  profile : ℝ → ℝ
  profile_nonneg : ∀ t, 0 ≤ profile t
  profile_mass : (∫ t in Set.Ioi (0 : ℝ), profile t) = 1
  profile_pauli : (∫ t in Set.Ioi (0 : ℝ), profile t / t) ≤ 1
  gradient : ℝ → MatrixGradient
  weak_gradient : ∀ t > 0, IsMatrixGradientOn Set.univ (layerAmplitude profile D t) (gradient t)
  density : gamma.matrixDensity =ᵐ[volume] D.matrix
  kinetic_trace : gamma.kinetic = (∫ x, layerCost gradient x) + cTF * traceMoment D (5/3) * trialMoment profile
  integrable : Integrable (layerCost gradient)
  moment_bound : trialMoment profile ≤ 1 + κ₁ * ε
  stiffness_bound : trialStiffness profile ≤ κ₂ * (1 + Real.sqrt ε)^2 / ε

/-- The same trial with its matrix-amplitude gradient estimate. -/
structure LayerTrial (D : Density) (S : MatrixGradient) (cTF κ₁ κ₂ ε : ℝ)
    extends LayerTrialData D cTF κ₁ κ₂ ε where
  gradient_estimate : ∀ᵐ x, layerCost gradient x ≤ (1 + Real.sqrt (trialStiffness profile))^2 * kineticDensity S x

/-- The trial construction of Appendix B, in the three-dimensional space
of the TSGA. Its constants refer to the scalar profiles in the layer cake. -/
def LayerTrials (cTF κ₁ κ₂ : ℝ) : Prop := ∀ (D : Density) (S : MatrixGradient), SqrtRegular D S →
  ∀ ε : ℝ, 0 < ε → Nonempty (LayerTrial D S cTF κ₁ κ₂ ε)

theorem trialStiffness_nonneg (η : ℝ → ℝ) : 0 ≤ trialStiffness η := by
  apply mul_nonneg (by norm_num)
  exact integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The kinetic and interacting upper bounds hold with the same constants,
including for arbitrary polarization. -/
theorem kinetic_and_energy_upper {cTF κ₁ κ₂ : ℝ} (hc : 0 ≤ cTF) (H : LayerTrials cTF κ₁ κ₂)
    (qf : QuasiFreeRealization) {D : Density} {S : MatrixGradient} (hD : SqrtRegular D S)
    {ε : ℝ} (hε : 0 < ε) :
    energy D.matrix ≤ bestKinetic D.matrix ∧ bestKinetic D.matrix ≤
      cTF * (1 + κ₁ * ε) * traceMoment D (5/3) +
      (2 * (1 + κ₂)) * (1 + Real.sqrt ε)^2 / ε * sqrtKinetic S := by
  obtain ⟨w⟩ := H D S hD ε hε
  refine ⟨energy_le_bestKinetic qf ⟨w.gamma, w.density⟩, (bestKinetic_le w.density).trans ?_⟩
  have hI : Integrable (kineticDensity S) := by
    unfold kineticDensity
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hD.grad.integrable_norm_pow (p := 2) (by decide))
  have hgrad := integral_mono_ae w.integrable (hI.const_mul _) w.gradient_estimate
  rw [integral_const_mul] at hgrad
  have hT : 0 ≤ traceMoment D (5/3) := integral_nonneg fun x => tracePower_nonneg D x _
  have hs : 0 ≤ sqrtKinetic S := integral_nonneg fun x => sq_nonneg _
  let W := (1 + Real.sqrt ε)^2 / ε
  have hW : 1 ≤ W := by
    apply (le_div_iff₀ hε).2
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have hK := w.stiffness_bound
  rw [mul_div_assoc] at hK
  change trialStiffness w.profile ≤ κ₂ * W at hK
  have h₁ : (1 + Real.sqrt (trialStiffness w.profile))^2 ≤ 2 * (1 + κ₂) * W := by
    nlinarith [Real.sq_sqrt (trialStiffness_nonneg w.profile), sq_nonneg (1 - Real.sqrt (trialStiffness w.profile))]
  have hx := (mul_le_mul_of_nonneg_right h₁ hs)
  have hη := mul_le_mul_of_nonneg_left w.moment_bound (mul_nonneg hc hT)
  rw [w.kinetic_trace, mul_div_assoc]
  change (∫ x, layerCost w.gradient x) ≤ _ * sqrtKinetic S at hgrad
  change _ ≤ _ + (2 * (1 + κ₂)) * W * sqrtKinetic S
  linarith only [hgrad, hx, hη]

end TSGA.ManyBody
