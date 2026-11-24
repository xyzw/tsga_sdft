import TSGA.Spin
import TSGA.SpiralEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Spin populations and thermodynamic bounds for the SSW gas

For a constant spin matrix, the scalar cutoff has integral equal to the
volume. The total particle number and third magnetization are therefore
the corresponding matrix quantities multiplied by the volume.
-/

namespace TSGA.SSW

open Filter FiniteSpiral
open scoped ComplexOrder Matrix InnerProductSpace Topology

/-- Third component of the magnetization of a spin density matrix. -/
def thirdMagnetization (M : SpinMatrix) : ℝ := (M 0 0).re - (M 1 1).re

/-- Discard the transverse magnetization while keeping both spin populations. -/
def diagonalSpin (M : SpinMatrix) : SpinMatrix := Matrix.diagonal M.diag

/-- Diagonal density matrix with spin-up and spin-down population densities. -/
def populations (up down : ℝ) : SpinMatrix := Matrix.diagonal ![(up : ℂ), (down : ℂ)]

/-- Polarization and polar angle of the magnetization. At zero magnetization
the defining equations allow every polar angle. -/
structure SpinParameters (M : SpinMatrix) (ζ θ : ℝ) : Prop where
  positive : M.PosSemidef
  charge_pos : 0 < M.trace.re
  polarization_mem : ζ ∈ Set.Icc 0 1
  angle_mem : θ ∈ Set.Icc 0 Real.pi
  magnitude : Real.sqrt (‖transverseMagnetization M‖ ^ 2 + thirdMagnetization M ^ 2) =
    ζ * M.trace.re
  axial : thirdMagnetization M = ζ * M.trace.re * Real.cos θ

variable {M : SpinMatrix} {ζ θ : ℝ}

theorem SpinParameters.diagonal_positive (h : SpinParameters M ζ θ) :
    (diagonalSpin M).PosSemidef :=
  Matrix.PosSemidef.diagonal fun _ => h.positive.diag_nonneg

@[simp] theorem trace_diagonalSpin (M : SpinMatrix) : (diagonalSpin M).trace = M.trace := by
  simp [diagonalSpin, Matrix.trace]

theorem SpinParameters.diagonal_charge_pos (h : SpinParameters M ζ θ) :
    0 < (diagonalSpin M).trace.re := by simpa using h.charge_pos

theorem SpinParameters.diagonal_eq_populations (h : SpinParameters M ζ θ) :
    diagonalSpin M = populations ((1 + ζ * Real.cos θ) / 2 * M.trace.re)
      ((1 - ζ * Real.cos θ) / 2 * M.trace.re) := by
  unfold diagonalSpin populations
  congr 1
  have hsum : (M 0 0).re + (M 1 1).re = M.trace.re := by simp [Matrix.trace_fin_two]
  have hdiff := h.axial
  unfold thirdMagnetization at hdiff
  funext i
  fin_cases i
  · change M 0 0 = ((_ : ℝ) : ℂ)
    rw [← h.positive.isHermitian.coe_re_apply_self 0]
    congr 1
    change (M 0 0).re = (1 + ζ * Real.cos θ) / 2 * M.trace.re
    linear_combination (hsum + hdiff) / 2
  · change M 1 1 = ((_ : ℝ) : ℂ)
    rw [← h.positive.isHermitian.coe_re_apply_self 1]
    congr 1
    change (M 1 1).re = (1 - ζ * Real.cos θ) / 2 * M.trace.re
    linear_combination (hsum - hdiff) / 2

/-- The three conclusions of the finite-system spin-spiral theorem specialized
to a constant spin matrix times the cutoff. These are inequalities for total
energies, before division by volume. -/
structure FiniteSpinBounds (M : SpinMatrix) (ζ θ : ℝ) (volume : ℕ → ℝ)
    (energy : ℕ → SpinMatrix → Wavevector → ℝ) : Prop where
  lower : ∀ n q, energy n (diagonalSpin M) 0 ≤ energy n M q
  upper : ∀ n q, energy n M q ≤ energy n M 0 + ‖q‖ ^ 2 / 4 *
    (M.trace.re * volume n - (thirdMagnetization M * volume n) ^ 2 / (M.trace.re * volume n))
  full : ζ = 1 → ∀ n q, energy n M q = energy n M 0 +
    ‖q‖ ^ 2 / 4 * (1 - (Real.cos θ) ^ 2) * (M.trace.re * volume n)

/-- Physical inputs to the finite-system comparisons in one volume. States
in the constrained searches have the indicated spin density. The diagonal
averaging maps to states of the diagonal matrix with the same cutoff. -/
structure FiniteSpinLaws (M : SpinMatrix) (ζ θ volume : ℝ)
    (energy : SpinMatrix → Wavevector → ℝ) where
  State : Type*
  stateEnergy : State → ℝ
  momentum : State → Wavevector
  spinCurrent : State → Wavevector
  RotatedState : Wavevector → Type*
  rotatedEnergy : (q : Wavevector) → RotatedState q → ℝ
  search : ∀ q, IsGLB (Set.range (rotatedEnergy q)) (energy M q)
  rotation : (q : Wavevector) → State ≃ RotatedState q
  rotationLaw : ∀ q s, rotatedEnergy q (rotation q s) =
    stateEnergy s - ⟪q, spinCurrent s⟫_ℝ + ‖q‖ ^ 2 / 4 * (M.trace.re * volume)
  DiagonalState : Type*
  diagonalEnergy : DiagonalState → ℝ
  diagonalSearch : IsGLB (Set.range diagonalEnergy) (energy (diagonalSpin M) 0)
  average : (q : Wavevector) → RotatedState q → DiagonalState
  averageLaw : ∀ q s, diagonalEnergy (average q s) = rotatedEnergy q s
  planarSymmetry : ∀ s, ∃ t, stateEnergy t = stateEnergy s ∧ momentum t = 0 ∧ spinCurrent t = 0
  boost : Wavevector → State ≃ State
  boostEnergy : ∀ k s, stateEnergy (boost k s) =
    stateEnergy s + 2 * ⟪k, momentum s⟫_ℝ + ‖k‖ ^ 2 * (M.trace.re * volume)
  boostMomentum : ∀ k s, momentum (boost k s) = momentum s + (M.trace.re * volume) • k
  boostCurrent : ∀ k s, spinCurrent (boost k s) = spinCurrent s + (thirdMagnetization M * volume) • k
  aligned : ζ = 1 → ∀ s, spinCurrent s = Real.cos θ • momentum s

theorem FiniteSpinLaws.variational {v : ℝ} {energy : SpinMatrix → Wavevector → ℝ}
    (h : FiniteSpinLaws M ζ θ v energy) :
    VariationalFormula h.stateEnergy h.spinCurrent (M.trace.re * v) (energy M) :=
  variationalFormula_of_rotation h.search h.rotation h.rotationLaw

theorem finiteSpinBounds_of_laws {V : ℕ → ℝ} {E : ℕ → SpinMatrix → Wavevector → ℝ}
    (h : SpinParameters M ζ θ) (hV : ∀ n, 0 < V n)
    (laws : ∀ n, FiniteSpinLaws M ζ θ (V n) (E n)) :
    FiniteSpinBounds M ζ θ V E where
  lower n q := diagonalEnergy_le ((laws n).search q) (laws n).diagonalSearch
    ((laws n).average q) ((laws n).averageLaw q)
  upper n q := planar_energy_le (laws n).variational (mul_pos h.charge_pos (hV n))
    (laws n).planarSymmetry (fun k => (laws n).boost k) (laws n).boostEnergy (laws n).boostCurrent q
  full hζ n q := fullyPolarized_energy (laws n).variational ((laws n).aligned hζ)
    (laws n).boost (laws n).boostEnergy (laws n).boostMomentum q

/-- Equation `eq:spiral_UEG`. The uniform gas energy at any matrix is its
spiral gas energy at wavevector zero. -/
structure GasBounds (M : SpinMatrix) (ζ θ : ℝ) (gas : SpinMatrix → Wavevector → ℝ) : Prop where
  lower : ∀ q, gas (populations ((1 + ζ * Real.cos θ) / 2 * M.trace.re)
    ((1 - ζ * Real.cos θ) / 2 * M.trace.re)) 0 ≤ gas M q
  upper : ∀ q, gas M q ≤ gas M 0 + M.trace.re * ‖q‖ ^ 2 / 4 * (1 - ζ ^ 2 * (Real.cos θ) ^ 2)
  full : ζ = 1 → ∀ q, gas M q =
    gas M 0 + M.trace.re * ‖q‖ ^ 2 / 4 * (1 - ζ ^ 2 * (Real.cos θ) ^ 2)

/-- Pass the finite spin-spiral comparisons to the common thermodynamic limit. -/
theorem bounds_of_convergence {V : ℕ → ℝ} {E : ℕ → SpinMatrix → Wavevector → ℝ}
    {gas : SpinMatrix → Wavevector → ℝ} (h : SpinParameters M ζ θ) (hV : ∀ n, 0 < V n)
    (hfinite : FiniteSpinBounds M ζ θ V E)
    (hlim : ∀ q, Tendsto (fun n => E n M q / V n) atTop (𝓝 (gas M q)))
    (hdiag : Tendsto (fun n => E n (diagonalSpin M) 0 / V n) atTop (𝓝 (gas (diagonalSpin M) 0))) :
    GasBounds M ζ θ gas := by
  let correction (q : Wavevector) := M.trace.re * ‖q‖ ^ 2 / 4 * (1 - ζ ^ 2 * (Real.cos θ) ^ 2)
  have hcorrect n (q : Wavevector) :
      ‖q‖ ^ 2 / 4 * (M.trace.re * V n - (thirdMagnetization M * V n) ^ 2 / (M.trace.re * V n)) =
        correction q * V n := by
    rw [h.axial]
    dsimp [correction]
    field_simp [(hV n).ne', h.charge_pos.ne']
  have upper (q : Wavevector) : gas M q ≤ gas M 0 + correction q := by
    apply le_of_tendsto_of_tendsto' (hlim q) ((hlim 0).add tendsto_const_nhds)
    intro n
    have hn := div_le_div_of_nonneg_right (hfinite.upper n q) (hV n).le
    simpa [hcorrect, add_div, (hV n).ne'] using hn
  refine ⟨?_, upper, ?_⟩
  · intro q
    rw [← h.diagonal_eq_populations]
    exact le_of_tendsto_of_tendsto' hdiag (hlim q) fun n =>
      div_le_div_of_nonneg_right (hfinite.lower n q) (hV n).le
  · intro hζ q
    apply le_antisymm (upper q)
    apply le_of_tendsto_of_tendsto' ((hlim 0).add tendsto_const_nhds) (hlim q)
    intro n
    have hshift : ‖q‖ ^ 2 / 4 * (1 - (Real.cos θ) ^ 2) * (M.trace.re * V n) =
        correction q * V n := by simp [correction, hζ]; ring
    change E n M 0 / V n + correction q ≤ E n M q / V n
    rw [hfinite.full hζ n q, hshift, add_div, mul_div_cancel_right₀ _ (hV n).ne']

end TSGA.SSW
