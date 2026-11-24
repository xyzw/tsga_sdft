import TSGA.OrderedCoulombFrame
import TSGA.CoulombBoost
import TSGA.PlanarCurrent
import TSGA.RankOneCurrent
import TSGA.MinorityFraction
import Mathlib.Analysis.Convex.Continuous

/-! # Spin spirals in a finite Coulomb system

The axial plane wave identifies the two constrained searches for every
representable density field. Complex conjugation supplies planar trials
and the constant rank-one spin marginal fixes the axial current at full
polarization. The boost calculations then give the sharp quadratic costs.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW
open scoped InnerProductSpace ComplexOrder

abbrev DensityTrial (F : Position → SpinMatrix) := {Γ : MixedState // feasible F Γ}

def DensityTrial.value {F : Position → SpinMatrix} (s : DensityTrial F) : ℝ :=
  s.val.kinetic + s.val.interaction - hartree (fun x => (F x).trace.re)

theorem DensityTrial.total_charge {F : Position → SpinMatrix} (s : DensityTrial F) :
    s.val.spinNumber 0 + s.val.spinNumber 1 = ∫ x, (F x).trace.re := by
  rw [← Fin.sum_univ_two, s.val.sum_spinNumber, ← s.val.particleNumber]
  exact integral_congr_ae (s.property.mono fun x hx => congrArg (fun B : SpinMatrix => B.trace.re) hx)

theorem DensityTrial.axial_magnetization {F : Position → SpinMatrix} (s : DensityTrial F) :
    s.val.spinNumber 0 - s.val.spinNumber 1 = ∫ x, thirdMagnetization (F x) := by
  rw [← (s.val.integral_spinDensity 0).2, ← (s.val.integral_spinDensity 1).2,
    ← integral_sub (s.val.integral_spinDensity 0).1 (s.val.integral_spinDensity 1).1]
  exact integral_congr_ae (s.property.mono fun x hx => congrArg thirdMagnetization hx)

/-- A representable density that is nonzero on a set of positive measure
has strictly positive total charge. -/
theorem total_charge_pos_of_nonzero {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ)
    (hF : ¬ F =ᵐ[volume] 0) : 0 < ∫ x, (F x).trace.re := by
  obtain ⟨Γ,hd⟩ := rep
  have pos : ∀ᵐ x, (F x).PosSemidef :=
    Γ.matrixDensity_posSemidef.mp (hd.mono fun x hx h => hx ▸ h)
  have nn : ∀ᵐ x, 0 ≤ (F x).trace.re := pos.mono fun x hx => (RCLike.nonneg_iff.mp hx.trace_nonneg).1
  have hi : Integrable (fun x => (F x).trace.re) := by
    apply ((Γ.integral_spinDensity 0).1.add (Γ.integral_spinDensity 1).1).congr
    filter_upwards [hd] with x hx
    simp [hx, Matrix.trace_fin_two]
  apply lt_of_le_of_ne (integral_nonneg_of_ae nn)
  intro hz
  have ht := (integral_eq_zero_iff_of_nonneg_ae nn hi).1 hz.symm
  exact hF (by
    filter_upwards [ht,pos] with x ht hp
    exact hp.trace_eq_zero_iff.mp (Complex.ext ht (RCLike.nonneg_iff.mp hp.trace_nonneg).2))

private theorem axial_represented {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ) (q : Position) :
    ∃ Γ, feasible (axialSpiral F q) Γ := by
  obtain ⟨Γ,hΓ⟩ := rep
  exact ⟨_, (MixedState.axialRotationEquiv F q ⟨Γ,hΓ⟩).property⟩

/-- Equation (spiral formula). The constrained energy minus the quadratic
term is the greatest lower bound of the affine trial energies. -/
theorem finiteCoulombSpiral_formula {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ) :
    FiniteSpiral.VariationalFormula (DensityTrial.value (F := F))
      (fun s => s.val.axialCurrent) (∫ x, (F x).trace.re) (fun q => energy (axialSpiral F q)) := by
  apply FiniteSpiral.variationalFormula_of_rotation
    (rotatedEnergy := fun _ s => DensityTrial.value s)
    (fun q => energy_isGLB (axial_represented rep q)) (MixedState.axialRotationEquiv F)
  intro q s
  change (s.val.twist (axialShift q)).kinetic + (s.val.twist (axialShift q)).interaction -
    hartree (fun x => (axialSpiral F q x).trace.re) = _
  rw [s.val.kinetic_axialShift, s.val.interaction_twist, DensityTrial.total_charge s]
  simp only [axialSpiral, trace_rotate, DensityTrial.value]
  ring

theorem finiteCoulombSpiral_concave {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ) :
    ConcaveOn ℝ Set.univ (fun q => energy (axialSpiral F q) - ‖q‖^2/4 * ∫ x, (F x).trace.re) :=
  FiniteSpiral.correctedEnergy_concave (finiteCoulombSpiral_formula rep)

theorem finiteCoulombSpiral_continuous {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ) :
    Continuous (fun q => energy (axialSpiral F q)) := by
  have hc := continuousOn_univ.mp ((finiteCoulombSpiral_concave rep).continuousOn isOpen_univ)
  have hq : Continuous (fun q : Position => ‖q‖^2 / 4 * ∫ x, (F x).trace.re) := by fun_prop
  simpa only [Pi.add_def, sub_add_cancel] using hc.add hq

theorem finiteCoulombSpiral_diagonal_le {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ)
    (q : Position) : energy (fun x => diagonalSpin (F x)) ≤ energy (axialSpiral F q) := by
  have hd (x : Position) : diagonalSpin (axialSpiral F q x) = diagonalSpin (F x) := by
    ext i j
    simp [axialSpiral, diagonalSpin, Matrix.diagonal_apply, Matrix.diag]
  simpa only [hd] using energy_diagonal_le (axial_represented rep q)

private theorem DensityTrial.value_boost {F : Position → SpinMatrix} (s : DensityTrial F) (k : Position) :
    DensityTrial.value (MixedState.boostEquiv F k s) = s.value + 2*⟪k,s.val.momentum⟫_ℝ +
      ‖k‖^2*(∫ x, (F x).trace.re) := by
  change (s.val.boost k).kinetic + (s.val.boost k).interaction - _ = _
  rw [s.val.kinetic_boost, s.val.interaction_boost, DensityTrial.total_charge s, DensityTrial.value]
  ring

/-- The magnetization lies in a fixed plane through the third axis when
complex conjugation of the field is undone by a constant axial rotation. -/
theorem finiteCoulombSpiral_planar_le {F : Position → SpinMatrix} (rep : ∃ Γ, feasible F Γ)
    (hF : ¬ F =ᵐ[volume] 0)
    (planar : ∃ α : ℝ, ∀ᵐ x, rotate α ((F x).map (starRingEnd ℂ)) = F x) (q : Position) :
    energy (axialSpiral F q) ≤ energy F + ‖q‖^2/4 *
      ((∫ x, (F x).trace.re) - (∫ x, thirdMagnetization (F x))^2 / ∫ x, (F x).trace.re) := by
  have h := FiniteSpiral.planar_energy_le (momentum := fun s : DensityTrial F => s.val.momentum)
    (magnetization := ∫ x, thirdMagnetization (F x)) (finiteCoulombSpiral_formula rep)
    (total_charge_pos_of_nonzero rep hF) ?_ (fun k s => MixedState.boostEquiv F k s)
    (fun k s => DensityTrial.value_boost s k) ?_ q
  · simpa only [axialSpiral_zero] using h
  · intro s
    obtain ⟨Λ,hΛ,hk,hw,hj⟩ := s.val.zero_currents_of_planar s.property planar
    refine ⟨⟨Λ,hΛ⟩, ?_, ?_, ?_⟩
    · simp [DensityTrial.value, hk, hw]
    · simp [MixedState.momentum, hj]
    · simp [MixedState.axialCurrent, hj]
  · intro k s
    exact (s.val.axialCurrent_boost k).trans (by rw [DensityTrial.axial_magnetization s])

/-- Full polarization along a fixed spin direction of polar angle θ. -/
theorem finiteCoulombSpiral_polarized {f : Position → ℝ} {M : SpinMatrix} {θ : ℝ}
    (spin : SpinParameters M 1 θ) (rep : ∃ Γ, feasible (fun x => (f x : ℂ) • M) Γ) (q : Position) :
    let F := fun x => (f x : ℂ) • M
    energy (axialSpiral F q) = energy F + ‖q‖^2/4 * (1 - (Real.cos θ)^2) * ∫ x, (F x).trace.re := by
  let F := fun x => (f x : ℂ) • M
  have h := FiniteSpiral.fullyPolarized_energy (momentum := fun s : DensityTrial F => s.val.momentum)
    (c := Real.cos θ) (finiteCoulombSpiral_formula rep)
    (fun s => s.val.spinMomentum_of_full_polarization spin s.property) (MixedState.boostEquiv F)
    (fun k s => DensityTrial.value_boost s k) (fun k s => (s.val.momentum_boost k).trans (by rw [DensityTrial.total_charge s])) q
  simpa only [axialSpiral_zero] using h

/-- The projector form of the full-polarization identity, with correction
determined directly by the third component of the unit spin direction. -/
theorem finiteCoulombSpiral_spinProjector {ρ : Position → ℝ} {n : Fin 3 → ℝ}
    (hn : spinDot n n = 1) (rep : ∃ Γ, feasible (fun x => (ρ x : ℂ) • spinProjector n) Γ)
    (q : Position) :
    let F := fun x => (ρ x : ℂ) • spinProjector n
    energy (axialSpiral F q) = energy F + ‖q‖^2/4 * (1 - (n 2)^2) * ∫ x, ρ x := by
  have hP : spinProjector n ∈ fixedCharge 1 := by simpa using pureSpin_fixedCharge (by norm_num : (0:ℝ) ≤ 1) hn
  obtain ⟨ζ,θ,h⟩ := exists_spinParameters hP.1 (by rw [hP.2]; norm_num)
  have axial : thirdMagnetization (spinProjector n) = n 2 := by
    simp [thirdMagnetization, spinProjector, pauli, Matrix.smul_apply, Complex.real_smul]
    ring
  have transverse : transverseMagnetization (spinProjector n) = (n 0 : ℂ) + Complex.I * (n 1 : ℂ) := by
    simp [transverseMagnetization, spinProjector, pauli, Matrix.smul_apply, Complex.real_smul]
    ring
  have mag : ‖transverseMagnetization (spinProjector n)‖^2 + thirdMagnetization (spinProjector n)^2 = 1 := by
    rw [transverse, axial, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      one_mul, zero_add]
    simpa only [spinDot, sq] using hn
  have hζ := h.magnitude
  rw [mag, Real.sqrt_one, hP.2, mul_one] at hζ
  subst ζ
  have hθ : Real.cos θ = n 2 := by simpa only [axial, hP.2, one_mul] using h.axial.symm
  have mass (x : Position) : (((ρ x : ℂ) • spinProjector n).trace.re) = ρ x := by
    simp [Matrix.trace_smul, hP.2]
  simpa only [hθ,mass] using finiteCoulombSpiral_polarized h rep q

end TSGA.ManyBody
