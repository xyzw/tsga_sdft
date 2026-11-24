import TSGA.StateMixing
import TSGA.StateSpinRotation

/-! # Removing the transverse spin by a half-turn

Averaging a Coulomb state with its axial rotation through π preserves its
energy and removes its off-diagonal spin density. The same construction
works for a position-dependent input density and for every spiral cutoff.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Filter SSW TSGA.Localization
open scoped Topology ComplexOrder

/-- The energy search over the actual mixed states of a fixed density. -/
theorem energy_isGLB {M : Position → SpinMatrix} (hr : ∃ Γ, feasible M Γ) :
    IsGLB (Set.range fun s : {Γ // feasible M Γ} =>
      s.val.kinetic + s.val.interaction - hartree (fun x => (M x).trace.re)) (energy M) := by
  constructor
  · rintro _ ⟨s, rfl⟩
    exact sub_le_sub_right (levyLieb_le s.property) _
  · intro b hb
    apply le_sub_iff_add_le.mpr
    apply le_levyLieb hr
    intro Γ hΓ
    exact le_sub_iff_add_le.mp (hb (Set.mem_range_self (⟨Γ, hΓ⟩ : {s // feasible M s})))

private theorem half_turn_average (M : SpinMatrix) :
    (1/2 : ℝ) • M + (1/2 : ℝ) • rotate Real.pi M = diagonalSpin M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotate_by_entry, axialWeight, diagonalSpin, Matrix.diagonal_apply, Matrix.diag,
      phaseFactor, Complex.real_smul, Complex.exp_pi_mul_I, Complex.exp_neg_pi_mul_I, neg_mul] <;> ring

/-- The half-and-half ensemble has exactly the original kinetic and
interaction energies. Its spin density is diagonal in the chosen basis. -/
theorem MixedState.exists_diagonal (Γ : MixedState) :
    ∃ Λ : MixedState, Λ.kinetic = Γ.kinetic ∧ Λ.interaction = Γ.interaction ∧
      Λ.matrixDensity =ᵐ[volume] fun x => diagonalSpin (Γ.matrixDensity x) := by
  let Λ := Γ.rotateSpin Real.pi
  let h : (0 : ℝ) ≤ 1/2 := by norm_num
  let hn : (1/2 : ℝ) + 1/2 = 1 := by norm_num
  obtain ⟨hk, hw, hm⟩ := Γ.mix_laws Λ h h hn
  refine ⟨Γ.mix Λ _ _ h h hn, ?_, ?_, ?_⟩
  · rw [hk, show Λ.kinetic = Γ.kinetic from Γ.rotate_kinetic _]
    ring
  · rw [hw, show Λ.interaction = Γ.interaction from Γ.rotate_interaction _]
    ring
  · filter_upwards [hm] with x hx
    rw [hx, show Λ.matrixDensity x = _ from Γ.rotate_matrix Real.pi x, half_turn_average]

/-- Discarding transverse magnetization lowers the constrained Coulomb energy. -/
theorem energy_diagonal_le {M : Position → SpinMatrix} (hr : ∃ Γ, feasible M Γ) :
    energy (fun x => diagonalSpin (M x)) ≤ energy M := by
  have bound : levyLieb (fun x => diagonalSpin (M x)) ≤ levyLieb M := by
    apply le_levyLieb hr
    intro Γ hΓ
    obtain ⟨Λ, hk, hw, hρ⟩ := Γ.exists_diagonal
    have hΛ : feasible (fun x => diagonalSpin (M x)) Λ :=
      hρ.trans (hΓ.mono fun _ hx => congrArg diagonalSpin hx)
    simpa only [hk, hw] using levyLieb_le hΛ
  simpa only [energy, trace_diagonalSpin, sub_le_sub_iff_right] using bound

theorem diagonal_spiral (D : DomainSequence) (M : SpinMatrix) (n : ℕ) (q : Position) (x : Position) :
    diagonalSpin (D.spiralField M n q x) = D.spiralField (diagonalSpin M) n 0 x := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [DomainSequence.spiralField, cutoffSpiral, diagonalSpin, Matrix.diag]
  · simp [DomainSequence.spiralField, cutoffSpiral, diagonalSpin, h]

/-- The diagonal lower bound in Proposition 3.2 from finite localization and
the Coulomb ensemble. Both thermodynamic limits use the same domains. -/
theorem ssw_diagonal_le {η : Mollifier} {M : SpinMatrix} (hM : M.PosSemidef) (hr : 0 < M.trace.re)
    (D : DomainSequence) (q : Position)
    (repr : ∀ n, ∃ Γ, feasible (D.spiralField M n q) Γ)
    (loc : ∀ A : SpinMatrix, A.PosSemidef → 0 < A.trace.re →
      ∀ k : Position, FiniteLocalization energy η A k) :
    sswEnergy energy η (diagonalSpin M) 0 ≤ sswEnergy energy η M q := by
  have hd : (diagonalSpin M).PosSemidef := Matrix.PosSemidef.diagonal fun _ => hM.diag_nonneg
  apply le_of_tendsto_of_tendsto' ((loc _ hd (by simpa) 0).tendsto D) ((loc _ hM hr q).tendsto D)
  intro n
  have h := energy_diagonal_le (repr n)
  simp_rw [diagonal_spiral D M n q] at h
  exact div_le_div_of_nonneg_right h (D.vol_pos n).le

end TSGA.ManyBody
