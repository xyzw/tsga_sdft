import TSGA.RankOneMarginal
import TSGA.RankOneWaveCurrent
import TSGA.SSWDomain

/-! # Current alignment for fully polarized Coulomb states

A constant spin row of zero marginal expectation annihilates each occupied
wave of positive weight. The proportionality between its two spin-resolved
currents persists under countable mixtures.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

/-- Every state with a fully polarized spin matrix multiplied by a scalar
density has axial spin current equal to the axial component of its polarization
times its charge current. -/
theorem MixedState.spinMomentum_of_full_polarization (Γ : MixedState) {M : SpinMatrix}
    {θ : ℝ} {f : Position → ℝ} (hM : SSW.SpinParameters M 1 θ)
    (rep : feasible (fun x => (f x : ℂ) • M) Γ) :
    Γ.spinMomentum 0 - Γ.spinMomentum 1 = Real.cos θ • (Γ.spinMomentum 0 + Γ.spinMomentum 1) := by
  obtain ⟨c,d,hzero,hpos,hcos⟩ := spinDefect_full_polarization hM
  have comp (k : ℕ) (j : Fin 3) :
      Γ.weight k * (‖c‖^2 * (Γ.component k).spinMomentum 0 j) =
      Γ.weight k * (‖d‖^2 * (Γ.component k).spinMomentum 1 j) := by
    rcases (Γ.weight_nonneg k).eq_or_lt with hk | hk
    · rw [← hk,zero_mul,zero_mul]
    · apply congrArg (Γ.weight k * ·)
      have hz := Γ.component_defect_zero rep hzero k hk
      generalize hs : Γ.component k = s at hz ⊢
      cases s with
      | vacuum => simp [PureState.spinMomentum]
      | occupied ψ => exact ψ.spinMomentum_of_zero_row (fun t => ψ.row_zero hz t) j
  have weighted (j : Fin 3) : ‖c‖^2 * Γ.spinMomentum 0 j = ‖d‖^2 * Γ.spinMomentum 1 j := by
    simp only [Γ.spinMomentum_apply,← tsum_mul_left]
    apply tsum_congr
    intro k
    simpa only [mul_left_comm (Γ.weight k)] using comp k j
  ext j
  change Γ.spinMomentum 0 j - Γ.spinMomentum 1 j = Real.cos θ * (Γ.spinMomentum 0 j + Γ.spinMomentum 1 j)
  apply mul_left_cancel₀ hpos.ne'
  calc
    _ = (‖d‖^2-‖c‖^2) * (Γ.spinMomentum 0 j+Γ.spinMomentum 1 j) := by
      linear_combination 2 * weighted j
    _ = _ := by rw [hcos]; ring

/-- Full polarization aligns the currents of every competitor for the
unrotated finite-volume gas. -/
theorem MixedState.spinMomentum_of_polarized_spiral {Γ : MixedState} (D : SSW.DomainSequence)
    {M : SpinMatrix} {θ : ℝ} (hM : SSW.SpinParameters M 1 θ) (n : ℕ)
    (rep : feasible (D.spiralField M n 0) Γ) :
    Γ.spinMomentum 0 - Γ.spinMomentum 1 = Real.cos θ • (Γ.spinMomentum 0 + Γ.spinMomentum 1) := by
  apply Γ.spinMomentum_of_full_polarization (f := D.cutoff n) hM
  exact rep.mono fun x hx => hx.trans (SSW.cutoffSpiral_zero_wavevector _ _ _)

end TSGA.ManyBody
