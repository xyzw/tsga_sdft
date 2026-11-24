import TSGA.CoulombLocalToGlobal

/-! # The SSW gas and the transverse spin-gradient approximation for the Coulomb model -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

/-- Theorem 3.1 for the reference energies used in the Coulomb TSGA. -/
theorem CoulombModelInputs.sswGas (P : CoulombModelInputs μ ι η) :
    SSWGasTheorem (referenceEnergies energy η) := P.gas.1

/-- Extended estimates for the grand-canonical constrained search, including
the refinement for a positive minority fraction. The phase remainders may be infinite. -/
theorem CoulombModelInputs.tsga (P : CoulombModelInputs μ ι η) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) := by
  obtain ⟨K,⟨L⟩⟩ := P.gas.2
  apply levyLieb_tsga_of_small_scale_bounds P.fock.oneBody L P.phaseProduct P.composition P.difference
  · intro p θ hp hθ hθ' hpθ
    exact P.smallScale L .general hp hθ hθ'.le hpθ (by simp) (by simp)
  · intro p θ ν hp hθ hθ' hpθ hν hν'
    exact P.smallScale L .minority hp hθ hθ'.le hpθ (fun _ => ⟨hν,hν'⟩) (by simp)
  · intro p hp
    have hp₀ : 0 < p := by linarith
    have eq : (2/p)*p = 2 := div_mul_cancel₀ _ hp₀.ne'
    exact P.smallScale L .globalRoot hp (by positivity) ((div_le_one hp₀).2 (by linarith))
      (by linarith only [eq,mul_comm (2/p) p]) (by simp) (fun _ => eq)

/-- The finite-error estimates, including the refinement for a positive minority fraction. -/
theorem CoulombModelInputs.tsgaFinite (P : CoulombModelInputs μ ι η) :
    MainTSGAEstimate (referenceEnergies energy η) :=
  P.tsga.toFinite

/-- Theorem 3.3 for the fixed spin axis. The rotating-frame density is arbitrary.
The global-root estimate has a constant uniform in the admissible power θ. -/
theorem CoulombModelInputs.fixedAxisTSGA (P : CoulombModelInputs μ ι η) {p : ℝ} (hp : 3 < p) :
    let F := referenceEnergies energy η
    (∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ →
      ∃ C > 0, TSGAEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∃ C > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ → SharpTSGAEstimate F p θ C) :=
  ⟨fun θ => P.tsgaFinite.general p θ hp, P.tsgaFinite.sharp p hp⟩

end TSGA.ManyBody
