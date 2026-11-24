import TSGA.PhaseLocalization

/-! # Integrable error densities in the TSGA localization argument -/

noncomputable section

namespace TSGA.Localization

open MeasureTheory PhaseLocalization
open scoped ComplexOrder

def massDensity (D : Density) (φ : Phase) (x : Position) : ℝ :=
  D.charge x + D.charge x ^ 2 + D.charge x * ‖φ.grad x‖ ^ 2

def kineticDensity (S : MatrixGradient) (x : Position) : ℝ := matrixGradNorm S x ^ 2

def phaseDensity (D : Density) (φ : Phase) (G : MatrixGradient) (p : ℝ) (x : Position) : ℝ :=
  D.charge x * φ.hessianNorm x ^ p + weightedRoot φ G p x

def rotatedEnergy (F : GasEnergies) (D : Density) (φ : Phase) : ℝ :=
  F.energy (fun x => rotate (φ.value x) (D.matrix x))

def localEnergy (F : GasEnergies) (D : Density) (φ : Phase) (x : Position) : ℝ :=
  F.ssw (D.matrix x) (φ.grad x)

theorem massDensity_nonneg (D : Density) (φ : Phase) (x : Position) : 0 ≤ massDensity D φ x :=
  add_nonneg (add_nonneg (D.charge_nonneg _) (sq_nonneg _))
    (mul_nonneg (D.charge_nonneg _) (sq_nonneg _))

theorem massDensity_integrable {D : Density} {φ : Phase} {p θ : ℝ} {S T G : MatrixGradient}
    (hD : DensityRegular D p θ S T) (hφ : PhaseAdmissible D p φ G) :
    Integrable (massDensity D φ) := by
  have hs : Integrable (fun x => D.charge x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hD.charge_L2.integrable_norm_pow (p := 2) (by decide))
  exact (hD.charge_L1.add hs).add hφ.kinetic

theorem kineticDensity_integrable {D : Density} {p θ : ℝ} {S T : MatrixGradient}
    (hD : DensityRegular D p θ S T) : Integrable (kineticDensity S) := by
  unfold kineticDensity
  simpa only [Real.norm_eq_abs, sq_abs] using
    (hD.sqrt_L2.integrable_norm_pow (p := 2) (by decide))

theorem rootPower_integrable {G : MatrixGradient} {p : ℝ} (hp : 0 < p)
    (h : MemLp (matrixGradNorm G) (ENNReal.ofReal p)) : Integrable (rootPower G p) := by
  have hn (x : Position) : ‖matrixGradNorm G x‖ = matrixGradNorm G x :=
    Real.norm_of_nonneg (Real.sqrt_nonneg _)
  unfold rootPower
  simpa only [hn, ENNReal.toReal_ofReal hp.le] using
    h.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top

theorem phaseDensity_nonneg (D : Density) (φ : Phase) (G : MatrixGradient) (p : ℝ)
    (x : Position) : 0 ≤ phaseDensity D φ G p x :=
  add_nonneg (mul_nonneg (D.charge_nonneg x) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    (weightedRoot_nonneg ..)

theorem phaseDensity_integrable {D : Density} {φ : Phase} {G : MatrixGradient} {p : ℝ}
    (hφ : PhaseAdmissible D p φ G) : Integrable (phaseDensity D φ G p) :=
  hφ.curvature.add (integrable_weightedRoot hφ)

theorem integral_phaseDensity {D : Density} {φ : Phase} {G : MatrixGradient} {p : ℝ}
    (hφ : PhaseAdmissible D p φ G) :
    (∫ x, phaseDensity D φ G p x) = (∫ x, D.charge x * φ.hessianNorm x ^ p) +
      ∫ x in φ.active, ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p := by
  simp only [phaseDensity, integral_add hφ.curvature (integrable_weightedRoot hφ),
    integral_weightedRoot_active]

/-- The whole-space a priori estimates before localization. The local gas
growth follows from the SSW bounds. The finite energy bound uses the kinetic
upper bound, the spiral square-root inequality and the Lieb–Oxford lower bound. -/
structure APriori (F : GasEnergies) (A : ℝ) : Prop where
  gas_growth : ∀ (M : SpinMatrix), M.PosSemidef → ∀ q : Position,
    |F.ssw M q| ≤ A * (M.trace.re + M.trace.re ^ 2 + M.trace.re * ‖q‖ ^ 2)
  measurable : ∀ {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient},
    3 < p → 0 < θ → DensityRegular D p θ S T → φ.Regular p →
    AEStronglyMeasurable (localEnergy F D φ) volume
  energy_bound : ∀ {D : Density} {φ : Phase} {p θ : ℝ} {S T G : MatrixGradient},
    3 < p → 0 < θ → DensityRegular D p θ S T → PhaseAdmissible D p φ G →
      |rotatedEnergy F D φ| ≤ A * ((∫ x, massDensity D φ x) + ∫ x, kineticDensity S x)

/-- Integrability of the local SSW energy uses only the finite phase kinetic
energy, even when one of the gradient-error integrals diverges. -/
theorem APriori.integrable_local {F : GasEnergies} {A : ℝ} (H : APriori F A)
    {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient} (hp : 3 < p) (hθ : 0 < θ)
    (hD : DensityRegular D p θ S T) (hr : φ.Regular p)
    (hkin : Integrable (fun x => D.charge x * ‖φ.grad x‖ ^ 2)) :
    Integrable (localEnergy F D φ) := by
  have hs : Integrable (fun x => D.charge x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hD.charge_L2.integrable_norm_pow (p := 2) (by decide))
  have hm : Integrable (massDensity D φ) := (hD.charge_L1.add hs).add hkin
  exact (hm.const_mul A).mono' (H.measurable hp hθ hD hr)
    (ae_of_all _ fun x => H.gas_growth (D.matrix x) (D.positive x) (φ.grad x))

theorem APriori.rough_bound {F : GasEnergies} {A : ℝ} (H : APriori F A) (hA : 0 ≤ A)
    {D : Density} {φ : Phase} {p θ : ℝ} {S T G : MatrixGradient} (hp : 3 < p) (hθ : 0 < θ)
    (hD : DensityRegular D p θ S T) (hφ : PhaseAdmissible D p φ G) :
    Integrable (localEnergy F D φ) ∧
      |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤
        (2 * A) * ((∫ x, massDensity D φ x) + ∫ x, kineticDensity S x) := by
  have hmass := massDensity_integrable hD hφ
  have hg (x : Position) : ‖localEnergy F D φ x‖ ≤ A * massDensity D φ x :=
    H.gas_growth (D.matrix x) (D.positive x) (φ.grad x)
  have hi := H.integrable_local hp hθ hD hφ.regular hφ.kinetic
  refine ⟨hi, ?_⟩
  have hb := (norm_integral_le_integral_norm (localEnergy F D φ)).trans
    (integral_mono hi.norm (hmass.const_mul A) hg)
  rw [integral_const_mul, Real.norm_eq_abs] at hb
  have hS : 0 ≤ ∫ x, kineticDensity S x := integral_nonneg fun x => sq_nonneg _
  have hdiff := norm_sub_le (rotatedEnergy F D φ) (∫ x, localEnergy F D φ x)
  simp only [Real.norm_eq_abs] at hdiff
  nlinarith [H.energy_bound hp hθ hD hφ, mul_nonneg hA hS]

end TSGA.Localization
