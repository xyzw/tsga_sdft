import TSGA.StateMixing

/-! # Convexity of the SSW gas at fixed charge

A common cutoff and wavevector give identical charge profiles for any two
constant matrices of equal trace. The finite-volume mixing inequality hence
passes to their gas energies along one admissible domain sequence.
-/

noncomputable section

namespace TSGA.SSW

open Filter MeasureTheory
open scoped ComplexOrder Topology

/-- Positive spin matrices of prescribed charge. -/
def fixedCharge (ρ : ℝ) : Set SpinMatrix := {M | M.PosSemidef ∧ M.trace.re = ρ}

theorem convex_fixedCharge (ρ : ℝ) : Convex ℝ (fixedCharge ρ) := by
  intro M hM N hN a b ha hb hab
  refine ⟨(hM.1.smul ha).add (hN.1.smul hb), ?_⟩
  simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
    Complex.re_ofReal_mul, hM.2, hN.2, ← add_mul, hab, one_mul]

theorem DomainSequence.spiralField_mix (D : DomainSequence) (M N : SpinMatrix) (n : ℕ)
    (q : Position) (a b : ℝ) :
    D.spiralField (a • M + b • N) n q = fun x => a • D.spiralField M n q x + b • D.spiralField N n q x := by
  funext x
  simp only [DomainSequence.spiralField, cutoffSpiral, rotate, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [smul_comm (D.cutoff n x : ℂ) a, smul_comm (D.cutoff n x : ℂ) b]

theorem DomainSequence.spiralField_equal_charge (D : DomainSequence) {M N : SpinMatrix}
    (h : M.trace.re = N.trace.re) (n : ℕ) (q x : Position) :
    (D.spiralField M n q x).trace.re = (D.spiralField N n q x).trace.re := by
  simp only [DomainSequence.spiralField, cutoffSpiral, Matrix.trace_smul, trace_rotate, smul_eq_mul,
    Complex.re_ofReal_mul, h]

/-- A finite convexity estimate on a single domain sequence suffices. -/
theorem SSWGasTheorem.convex_fixedCharge_of_finite {F : GasEnergies} (H : SSWGasTheorem F)
    (D : DomainSequence) (q : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (hfinite : ∀ M ∈ fixedCharge ρ, ∀ N ∈ fixedCharge ρ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      ∀ n, F.energy (fun x => a • D.spiralField M n q x + b • D.spiralField N n q x) ≤
        a * F.energy (D.spiralField M n q) + b * F.energy (D.spiralField N n q)) :
    ConvexOn ℝ (fixedCharge ρ) (fun M => F.ssw M q) := by
  refine ⟨convex_fixedCharge ρ, ?_⟩
  intro M hM N hN a b ha hb hab
  have hsum := convex_fixedCharge ρ hM hN ha hb hab
  have hlim (P : SpinMatrix) (hP : P ∈ fixedCharge ρ) :
      Tendsto (fun n => D.energyDensity F.energy P n q) atTop (𝓝 (F.ssw P q)) :=
    H.limit P hP.1 (hP.2.symm ▸ hρ) q D
  have hbound (n : ℕ) : D.energyDensity F.energy (a • M + b • N) n q ≤
      a * D.energyDensity F.energy M n q + b * D.energyDensity F.energy N n q := by
    have h := div_le_div_of_nonneg_right (hfinite M hM N hN a b ha hb hab n) (D.vol_pos n).le
    simpa only [DomainSequence.energyDensity, DomainSequence.totalEnergy, D.spiralField_mix,
      add_div, mul_div_assoc] using h
  exact le_of_tendsto_of_tendsto' (hlim _ hsum) (((hlim M hM).const_mul a).add ((hlim N hN).const_mul b)) hbound

end TSGA.SSW

namespace TSGA.ManyBody

open SSW MeasureTheory
open scoped ComplexOrder

/-- Proposition E.2(ii) for the Coulomb constrained search. Only the two
endpoints of each finite mixture need independent representing states.
The mixture itself is constructed by interleaving the two ensembles. -/
theorem ssw_convex_fixed_charge {η : Mollifier} (H : SSWGasTheorem (referenceEnergies energy η))
    (D : DomainSequence) (q : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (repr : ∀ M ∈ fixedCharge ρ, ∀ n, ∃ Γ : MixedState, feasible (D.spiralField M n q) Γ) :
    ConvexOn ℝ (fixedCharge ρ) (fun M => sswEnergy energy η M q) := by
  apply H.convex_fixedCharge_of_finite D q hρ
  intro M hM N hN a b ha hb hab n
  exact energy_convex_fixed_charge (repr M hM n) (repr N hN n)
    (ae_of_all _ (D.spiralField_equal_charge (hM.2.trans hN.2.symm) n q)) ha hb hab

end TSGA.ManyBody
