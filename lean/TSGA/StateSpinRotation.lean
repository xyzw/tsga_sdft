import TSGA.LevyLieb
import TSGA.AxialKinetic
import TSGA.SpiralCovariance

/-! # Constant axial spin rotations on the Coulomb constrained search

In each particle-number sector the tensor power of an axial spin rotation
acts by a constant phase for each spin configuration. The one-body marginal
retains exactly the phase of its two free spin indices.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization
open scoped ComplexConjugate

private def spinWeight (j : Fin 2) : ℝ := if j = 0 then -(1/2) else 1/2

private def sectorPhase {n : ℕ} (a : ℝ) (s : Spins n) : ℂ :=
  phaseFactor ((∑ i, spinWeight (s i)) * a)

private theorem sectorPhase_norm {n : ℕ} (a : ℝ) (s : Spins n) : ‖sectorPhase a s‖ = 1 := by
  simp [sectorPhase, phaseFactor, Complex.norm_exp]

private theorem sectorPhase_perm {n : ℕ} (a : ℝ) (s : Spins n) (π : Equiv.Perm (Fin n)) :
    sectorPhase a (s ∘ π) = sectorPhase a s := by
  unfold sectorPhase
  rw [show (∑ i, spinWeight ((s ∘ π) i)) = ∑ i, spinWeight (s i) from
    Equiv.sum_comp π (fun i => spinWeight (s i))]

/-- Tensor power of the rotation on a normalized pure state. -/
def Wave.rotateSpin {n : ℕ} (ψ : Wave n) (a : ℝ) : Wave n where
  value s x := sectorPhase a s * ψ.value s x
  gradient s x i j := sectorPhase a s * ψ.gradient s x i j
  antisymmetric π s := by
    filter_upwards [ψ.antisymmetric π s] with x hx
    rw [sectorPhase_perm, hx]
    ring
  square_integrable s := (ψ.square_integrable s).const_mul _
  normalized := by simpa only [norm_mul, sectorPhase_norm, one_mul] using ψ.normalized
  gradient_L2 s i j := (ψ.gradient_L2 s i j).const_mul _
  weak_gradient s i j f h hc := by
    have hw := ψ.weak_gradient s i j f h hc
    simp_rw [← mul_smul_comm, integral_const_mul, hw, mul_neg]
  interaction_integrable s := by simpa only [norm_mul, sectorPhase_norm, one_mul] using ψ.interaction_integrable s

@[simp] theorem Wave.kinetic_rotate {n : ℕ} (ψ : Wave n) (a : ℝ) :
    (ψ.rotateSpin a).kinetic = ψ.kinetic := by simp [kinetic, rotateSpin, sectorPhase_norm]

@[simp] theorem Wave.interaction_rotate {n : ℕ} (ψ : Wave n) (a : ℝ) :
    (ψ.rotateSpin a).interaction = ψ.interaction := by simp [interaction, rotateSpin, sectorPhase_norm]

private theorem phase_pair {n : ℕ} (a : ℝ) (s : Spins n) (i j : Fin 2) :
    sectorPhase a (Fin.cons i s) * conj (sectorPhase a (Fin.cons j s)) = phaseFactor (axialWeight i j * a) := by
  change phaseFactor _ * star (phaseFactor _) = _
  rw [star_phaseFactor, ← phaseFactor_add]
  congr 1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, axialWeight, spinWeight]
  ring

@[simp] theorem Wave.matrixDensity_rotate {n : ℕ} (ψ : Wave (n+1)) (a : ℝ) (x : Position) :
    (ψ.rotateSpin a).matrixDensity x = rotate a (ψ.matrixDensity x) := by
  ext i j
  rw [rotate_by_entry]
  unfold matrixDensity
  simp only [rotateSpin, map_mul]
  have h (s : Spins n) (y : Space n) :
      sectorPhase a (Fin.cons i s) * ψ.value (Fin.cons i s) (Fin.cons x y) *
        (conj (sectorPhase a (Fin.cons j s)) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))) =
      phaseFactor (axialWeight i j * a) *
        (ψ.value (Fin.cons i s) (Fin.cons x y) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))) := by
    rw [← phase_pair a s i j]
    ring
  simp_rw [h, integral_const_mul, ← Finset.mul_sum]
  ring

def PureState.rotateSpin (s : PureState) (a : ℝ) : PureState := match s with
  | .vacuum => .vacuum
  | .occupied ψ => .occupied (ψ.rotateSpin a)

@[simp] theorem PureState.rotate_kinetic (s : PureState) (a : ℝ) : (s.rotateSpin a).kinetic = s.kinetic := by
  cases s <;> simp [kinetic, rotateSpin]

@[simp] theorem PureState.rotate_interaction (s : PureState) (a : ℝ) : (s.rotateSpin a).interaction = s.interaction := by
  cases s <;> simp [interaction, rotateSpin]

@[simp] theorem PureState.rotate_particles (s : PureState) (a : ℝ) : (s.rotateSpin a).particles = s.particles := by
  cases s <;> rfl

@[simp] theorem PureState.rotate_matrix (s : PureState) (a : ℝ) (x : Position) :
    (s.rotateSpin a).matrixDensity x = rotate a (s.matrixDensity x) := by
  cases s with
  | vacuum => ext i j; simp [rotate_by_entry, rotateSpin, matrixDensity]
  | occupied ψ => exact ψ.matrixDensity_rotate a x

def MixedState.rotateSpin (Γ : MixedState) (a : ℝ) : MixedState where
  component k := (Γ.component k).rotateSpin a
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := by simpa using Γ.particles_summable
  kinetic_summable := by simpa using Γ.kinetic_summable
  interaction_summable := by simpa using Γ.interaction_summable
  density_summable := by
    filter_upwards [Γ.density_summable] with x hx
    intro i j
    simpa only [PureState.rotate_matrix, rotate_by_entry, mul_left_comm (Γ.weight _ : ℂ)] using
      (hx i j).mul_left (phaseFactor (axialWeight i j * a))

@[simp] theorem MixedState.rotate_kinetic (Γ : MixedState) (a : ℝ) : (Γ.rotateSpin a).kinetic = Γ.kinetic := by
  simp [kinetic, rotateSpin]

@[simp] theorem MixedState.rotate_interaction (Γ : MixedState) (a : ℝ) :
    (Γ.rotateSpin a).interaction = Γ.interaction := by simp [interaction, rotateSpin]

@[simp] theorem MixedState.rotate_matrix (Γ : MixedState) (a : ℝ) (x : Position) :
    (Γ.rotateSpin a).matrixDensity x = rotate a (Γ.matrixDensity x) := by
  ext i j
  simp only [matrixDensity, rotateSpin, PureState.rotate_matrix, rotate_by_entry,
    mul_left_comm (Γ.weight _ : ℂ), tsum_mul_left]

/-- Axial spin invariance holds directly for the Coulomb Levy–Lieb energy. -/
theorem energy_axial (M : Position → SpinMatrix) (a : ℝ) : energy (fun x => rotate a (M x)) = energy M := by
  have incl (N : Position → SpinMatrix) (b : ℝ) {t : ℝ}
      (h : ∃ Γ : MixedState, feasible N Γ ∧ t = Γ.kinetic + Γ.interaction) :
      ∃ Γ : MixedState, feasible (fun x => rotate b (N x)) Γ ∧ t = Γ.kinetic + Γ.interaction := by
    obtain ⟨Γ, hd, ht⟩ := h
    refine ⟨Γ.rotateSpin b, ?_, by simpa using ht⟩
    exact hd.mono fun x hx => by simp [hx]
  have hinv (x : Position) : rotate (-a) (rotate a (M x)) = M x := by simp [← SSW.rotate_add]
  have eq : levyLieb (fun x => rotate a (M x)) = levyLieb M := by
    apply congrArg sInf
    ext t
    constructor
    · intro h
      change ∃ Γ : MixedState, feasible M Γ ∧ t = Γ.kinetic + Γ.interaction
      simpa only [hinv] using incl (fun x => rotate a (M x)) (-a) h
    · exact incl M a
  simp [energy, eq]

end TSGA.ManyBody
