import TSGA.SSWLocalization
import TSGA.SSWBounds
import TSGA.Thermodynamic
import TSGA.LocalEstimate

/-! # The thermodynamic limit of the spin-spiral-wave gas

Theorem `sswGas_theorem` combines `thm:spiral_limit` and `prop:SSW_properties` of `tsga.tex`.
The localization hypotheses compare finite volumes. The finite constrained
search supplies the spin, averaging and boost laws used for the energy bounds.
-/

noncomputable section

namespace TSGA.SSW

open Filter
open scoped Topology ComplexOrder

/-- Conclusions of Theorem 3.1 and Proposition 3.2 for the physical energy and both reference
energies. The same functions work for every domain sequence, smoothing width
and outer mollifier. -/
structure SSWGasTheorem (F : GasEnergies) : Prop where
  limit : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ (q : Position) (D : DomainSequence),
    Tendsto (fun n => D.energyDensity F.energy M n q) atTop (𝓝 (F.ssw M q))
  uniform_limit : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ D : DomainSequence,
    Tendsto (fun n => F.energy (fun x => (D.cutoff n x : ℂ) • M) / D.vol n) atTop (𝓝 (F.ueg M))
  vacuum_limit : ∀ (D : DomainSequence) (q : Position),
    Tendsto (fun n => D.energyDensity F.energy 0 n q) atTop (𝓝 0)
  vacuum_ssw : ∀ q : Position, F.ssw 0 q = 0
  vacuum_ueg : F.ueg 0 = 0
  isotropic : ∀ (M : SpinMatrix) (R : Position ≃ₗᵢ[ℝ] Position) (q : Position),
    F.ssw M (R q) = F.ssw M q
  concave : ∀ {M : SpinMatrix} {ζ θ : ℝ}, SpinParameters M ζ θ →
    ConcaveOn ℝ Set.univ (fun q => F.ssw M q - ‖q‖ ^ 2 / 4 * M.trace.re)
  bounds : ∀ {M : SpinMatrix} {ζ θ : ℝ}, SpinParameters M ζ θ → GasBounds M ζ θ F.ssw

/-- The concrete specialization of the energy data used in the LSDA corollary.
The zero-wavevector law is proved by evaluating the finite spherical average. -/
def referenceEnergies (E : EnergyFunctional) (η : Mollifier) : GasEnergies where
  energy := E
  ssw := sswEnergy E η
  ueg := uniformEnergy E η
  zero_mode M _ := sswEnergy_zero_wavevector E η M

/-- The finite spin comparisons pass to any common thermodynamic limit
of the constrained-search energy. One admissible sequence suffices for the
concavity and polarization conclusions. -/
theorem sswGas_theorem_of_convergence {E : EnergyFunctional} (η : Mollifier) (vacuum : E 0 = 0)
    (limits : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re →
      ∀ (q : Position) (D : DomainSequence),
        Tendsto (fun n => D.energyDensity E M n q) atTop (𝓝 (sswEnergy E η M q)))
    (D₀ : DomainSequence)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, FiniteSpinLaws M ζ θ (D₀.vol n) (fun A k => D₀.totalEnergy E A n k)) :
    SSWGasTheorem (referenceEnergies E η) where
  limit M hM hρ q D := limits M hM hρ q D
  uniform_limit M hM hρ D := by
    have h := limits M hM hρ 0 D
    have hfield (n : ℕ) : D.spiralField M n 0 = fun x => (D.cutoff n x : ℂ) • M :=
      funext (cutoffSpiral_zero_wavevector (D.cutoff n) M)
    simpa only [DomainSequence.energyDensity, DomainSequence.totalEnergy, hfield,
      sswEnergy_zero_wavevector, referenceEnergies] using h
  vacuum_limit D q := by
    have hz (n : ℕ) : D.spiralField 0 n q = 0 := funext (cutoffSpiral_zero_matrix _ q)
    simp [DomainSequence.energyDensity, DomainSequence.totalEnergy, referenceEnergies, hz, vacuum]
  vacuum_ssw := sswEnergy_vacuum vacuum η
  vacuum_ueg := uniformEnergy_vacuum vacuum η
  isotropic M R q := sswEnergy_isotropic E η M (R.norm_map q)
  concave {M ζ θ} h := by
    let laws := states M ζ θ h
    exact Thermodynamic.correctedEnergyDensity_concave (volume := D₀.vol)
      (stateEnergy := fun n => (laws n).stateEnergy) (spinCurrent := fun n => (laws n).spinCurrent)
      D₀.vol_pos (fun n => (laws n).variational)
      (fun q => limits M h.positive h.charge_pos q D₀)
  bounds {M ζ θ} h := by
    apply bounds_of_convergence (E := fun n A q => D₀.totalEnergy E A n q) h D₀.vol_pos
    · exact finiteSpinBounds_of_laws h D₀.vol_pos (states M ζ θ h)
    · exact fun q => limits M h.positive h.charge_pos q D₀
    · exact limits _ h.diagonal_positive h.diagonal_charge_pos 0 D₀

/-- The thermodynamic limit holds along every admissible sequence.
The finite-system comparisons on one sequence give the corrected concavity
and bounds in Proposition 3.2. -/
theorem sswGas_theorem {E : EnergyFunctional} (η : Mollifier) (vacuum : E 0 = 0)
    (localize : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re →
      ∀ q : Position, FiniteLocalization E η M q)
    (D₀ : DomainSequence)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, FiniteSpinLaws M ζ θ (D₀.vol n) (fun A k => D₀.totalEnergy E A n k)) :
    SSWGasTheorem (referenceEnergies E η) :=
  sswGas_theorem_of_convergence η vacuum (fun M hM hρ q D => (localize M hM hρ q).tendsto D) D₀ states

/-- Radial monotonicity at the end of the proof of Proposition 3.2. -/
theorem radial_monotonicity {E : EnergyFunctional} {η : Mollifier}
    (H : SSWGasTheorem (referenceEnergies E η)) {M : SpinMatrix} {ζ θ : ℝ}
    (h : SpinParameters M ζ θ) (e : Position) :
    AntitoneOn (fun r : ℝ => sswEnergy E η M (r • e) - ‖r • e‖ ^ 2 / 4 * M.trace.re)
      (Set.Ici 0) :=
  Thermodynamic.correctedEnergyDensity_antitoneOn_ray (H.concave h)
    (fun _ _ heq => sswEnergy_isotropic E η M heq) e

end TSGA.SSW
