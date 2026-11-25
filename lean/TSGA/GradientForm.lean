import TSGA.ExtendedEstimate
import TSGA.SSWGas
import TSGA.SpiralCovariance
import TSGA.StateSpinRotation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Fixed-axis spiral and azimuthal gradient form of the TSGA

At a point the reference spiral freezes the density in the rotating frame
and keeps the affine phase about the third spin axis. The density in that
frame may have a spatially varying spin direction. For a signed transverse
amplitude the azimuthal frame is the inverse spin rotation of the physical
density. Constant axial spin invariance of the finite energy gives the
corresponding invariance of the local reference energy.
-/

noncomputable section

namespace TSGA

open MeasureTheory TSGA.Localization
open scoped Matrix ComplexOrder InnerProductSpace

/-- At displacement `h` from `x`, the affine phase on the frozen rotating-frame
matrix gives the cutoff spiral based on the physical spin matrix at `x`. -/
theorem Density.cutoffSpiral_affinePhase (D : Density) (φ : Phase) (x : Position)
    (f : Position → ℝ) (h : Position) :
    SSW.cutoffSpiral f ((rotatedDensity D φ).matrix x) (φ.grad x) h =
      (f h : ℂ) • rotate (φ.value x + ⟪φ.grad x, h⟫_ℝ) (D.matrix x) := by
  rw [add_comm (φ.value x), SSW.rotate_add]
  rfl

/-- Global spin invariance of the finite energy about the chosen third axis. -/
def AxialEnergyInvariant (E : SSW.EnergyFunctional) : Prop :=
  ∀ (M : Position → SpinMatrix) (α : ℝ), E (fun x => rotate α (M x)) = E M

/-- The corresponding symmetry of the energy per unit volume. -/
def AxialGasInvariant (F : GasEnergies) : Prop :=
  ∀ (M : SpinMatrix) (k : Position) (α : ℝ), F.ssw (rotate α M) k = F.ssw M k

theorem axialGasInvariant_reference {E : SSW.EnergyFunctional} (hE : AxialEnergyInvariant E)
    (η : SSW.Mollifier) : AxialGasInvariant (SSW.referenceEnergies E η) := by
  intro M k α
  have hfield (f : Position → ℝ) (q : Position) :
      SSW.cutoffSpiral f (rotate α M) q = fun x => rotate α (SSW.cutoffSpiral f M q x) := by
    funext x
    simp only [SSW.cutoffSpiral, SSW.rotate_smul, ← SSW.rotate_add, add_comm α]
  have htile (ℓ δ : ℝ) :
      SSW.tileEnergy E η (rotate α M) ℓ δ = SSW.tileEnergy E η M ℓ δ := by
    funext q
    simp only [SSW.tileEnergy, hfield, hE _ _]
  change SSW.tileLimit _ = SSW.tileLimit _
  apply congrArg SSW.tileLimit
  funext ℓ δ
  simp only [SSW.averagedTile, htile]

/-- For the Coulomb constrained search the rotation symmetry follows by
rotating each many-body state in its particle-number sector. -/
theorem axialGasInvariant_coulomb (η : SSW.Mollifier) :
    AxialGasInvariant (SSW.referenceEnergies ManyBody.energy η) :=
  axialGasInvariant_reference ManyBody.energy_axial η

/-- The density in the moving frame, constructed for every physical density. -/
def Density.azimuthalFrame (D : Density) (φ : Phase) : Density where
  matrix x := rotate (-φ.value x) (D.matrix x)
  positive x := rotate_posSemidef _ (D.positive x)

@[simp] theorem Density.rotate_azimuthalFrame (D : Density) (φ : Phase) (x : Position) :
    rotate (φ.value x) ((D.azimuthalFrame φ).matrix x) = D.matrix x := by
  simp [Density.azimuthalFrame, ← SSW.rotate_add]

@[simp] theorem Density.charge_azimuthalFrame (D : Density) (φ : Phase) (x : Position) :
    (D.azimuthalFrame φ).charge x = D.charge x := by
  simp [Density.charge, Density.azimuthalFrame]

/-- The fixed-axis reference has the same local energy in either frame for
every phase, even when the spin direction in the rotating frame varies. -/
theorem AxialGasInvariant.localEnergy_azimuthalFrame {F : GasEnergies} (hspin : AxialGasInvariant F)
    (D : Density) (φ : Phase) : localEnergy F (D.azimuthalFrame φ) φ = localEnergy F D φ :=
  funext fun _ => hspin _ _ _

/-- The transverse factorization identifies the inverse rotation with the
real symmetric matrix in the corollary, including negative amplitudes. -/
theorem azimuthalFrame_eq_spinDensity {ρ mx my mz a α : ℝ}
    (hμ : (mx : ℂ) + Complex.I * (my : ℂ) = (a : ℂ) * phaseFactor α) :
    rotate (-α) (spinDensity ρ mx my mz) = spinDensity ρ a 0 mz := by
  have hl : transverseMagnetization (rotate (-α) (spinDensity ρ mx my mz)) =
      transverseMagnetization (spinDensity ρ a 0 mz) := by
    rw [transverseMagnetization_rotate, transverseMagnetization_spinDensity,
      transverseMagnetization_spinDensity, hμ]
    rw [mul_left_comm, ← phaseFactor_add]
    simp
  have h10 : rotate (-α) (spinDensity ρ mx my mz) 1 0 = spinDensity ρ a 0 mz 1 0 := by
    simpa only [transverseMagnetization, mul_right_inj' (by norm_num : (2 : ℂ) ≠ 0)] using hl
  have hrot : (rotate (-α) (spinDensity ρ mx my mz)).IsHermitian := by
    unfold rotate
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (spinDensity_isHermitian ρ mx my mz).eq, Matrix.mul_assoc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [spinDensity]
  · exact (hrot.apply 0 1).symm.trans ((congrArg star h10).trans
      ((spinDensity_isHermitian ρ a 0 mz).apply 0 1))
  · exact h10
  · simp [spinDensity]

private theorem rotate_sub_scalar (α : ℝ) (M : SpinMatrix) (c : ℂ) :
    rotate α (M - c • (1 : SpinMatrix)) = rotate α M - c • (1 : SpinMatrix) := by
  have hunit := (Matrix.mem_specialUnitaryGroup_iff.mp (spinRotation_mem_specialUnitaryGroup α)).1
  have hu := Matrix.mem_unitaryGroup_iff.mp hunit
  simp [rotate, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.star_eq_conjTranspose, hu]

theorem minorityBound_azimuthalFrame_iff (ν : ℝ) (D : Density) (φ : Phase) :
    MinorityBound ν (D.azimuthalFrame φ) ↔ MinorityBound ν D := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    have hr := rotate_posSemidef (φ.value x) hx
    simpa only [rotate_sub_scalar, Density.rotate_azimuthalFrame, Density.charge_azimuthalFrame] using hr
  · intro h
    filter_upwards [h] with x hx
    have hr := rotate_posSemidef (-φ.value x) hx
    rw [Density.charge_azimuthalFrame]
    simpa only [rotate_sub_scalar, Density.azimuthalFrame] using hr

/-- Both expressions for the reference integral and the bound on the error
in the energy of the original, unrotated input field. -/
structure GradientFormBound (F : GasEnergies) (D : Density) (φ : Phase) (rhs : WithTop ℝ) : Prop where
  integrable : Integrable (localEnergy F D φ)
  reference : (∫ x, localEnergy F (D.azimuthalFrame φ) φ x) = ∫ x, localEnergy F D φ x
  error : (↑|F.energy D.matrix - ∫ x, localEnergy F D φ x| : WithTop ℝ) ≤ rhs

private theorem gradientForm_transfer {F : GasEnergies} (hspin : AxialGasInvariant F)
    (D : Density) (φ : Phase) (rhs : WithTop ℝ)
    (h : Integrable (localEnergy F (D.azimuthalFrame φ) φ) ∧
      (↑|rotatedEnergy F (D.azimuthalFrame φ) φ -
        ∫ x, localEnergy F (D.azimuthalFrame φ) φ x| : WithTop ℝ) ≤ rhs) :
    GradientFormBound F D φ rhs := by
  have href := hspin.localEnergy_azimuthalFrame D φ
  have htotal : rotatedEnergy F (D.azimuthalFrame φ) φ = F.energy D.matrix := by
    simp only [rotatedEnergy, Density.rotate_azimuthalFrame]
  rw [href, htotal] at h
  exact ⟨h.1, by rw [href], h.2⟩

theorem ExtendedTSGAEstimate.gradientForm {F : GasEnergies} {classOf : Density → Prop}
    {p θ b C : ℝ} (h : ExtendedTSGAEstimate F classOf p θ b C) (hspin : AxialGasInvariant F)
    (D : Density) (φ : Phase) (S T G : MatrixGradient) (hclass : classOf (D.azimuthalFrame φ))
    (hD : DensityRegular (D.azimuthalFrame φ) p θ S T)
    (hφ : ManuscriptPhase (D.azimuthalFrame φ) p φ G) {ε : ℝ} (hε : 0 < ε) :
    GradientFormBound F D φ (withPhaseRemainders (D.azimuthalFrame φ) p φ G
      (tsgaError (D.azimuthalFrame φ) φ S T G p b C ε)) :=
  gradientForm_transfer hspin _ _ _ (h _ S T hclass hD φ G hφ ε hε)

theorem ExtendedSharpTSGAEstimate.gradientForm {F : GasEnergies} {p θ C : ℝ}
    (h : ExtendedSharpTSGAEstimate F p θ C) (hspin : AxialGasInvariant F) (D : Density)
    (φ : Phase) (S T G : MatrixGradient) (hD : DensityRegular (D.azimuthalFrame φ) p θ S T)
    (hG : IsMatrixGradientOn Set.univ ((D.azimuthalFrame φ).power (1 / p)) G)
    (hLp : MemLp (matrixGradNorm G) (ENNReal.ofReal p))
    (hφ : ManuscriptPhase (D.azimuthalFrame φ) p φ G) {ε : ℝ} (hε : 0 < ε) :
    GradientFormBound F D φ (withPhaseRemainders (D.azimuthalFrame φ) p φ G
      (tsgaError (D.azimuthalFrame φ) φ S T G p (2 * p - 1) C ε +
        C / ε ^ (2 * p - 1) * (∫ x, matrixGradNorm G x ^ p))) :=
  gradientForm_transfer hspin _ _ _ (h _ S T G hD hG hLp φ hφ ε hε)

/-- The class restriction is imposed on the physical field. -/
def GradientFormEstimate (F : GasEnergies) (classOf : Density → Prop) (p θ b C : ℝ) : Prop :=
  ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), classOf D →
    DensityRegular (D.azimuthalFrame φ) p θ S T → ManuscriptPhase (D.azimuthalFrame φ) p φ G →
    ∀ ε > 0, GradientFormBound F D φ (withPhaseRemainders (D.azimuthalFrame φ) p φ G
      (tsgaError (D.azimuthalFrame φ) φ S T G p b C ε))

def SharpGradientFormEstimate (F : GasEnergies) (p θ C : ℝ) : Prop :=
  ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular (D.azimuthalFrame φ) p θ S T →
    IsMatrixGradientOn Set.univ ((D.azimuthalFrame φ).power (1 / p)) G →
    MemLp (matrixGradNorm G) (ENNReal.ofReal p) → ManuscriptPhase (D.azimuthalFrame φ) p φ G →
    ∀ ε > 0, GradientFormBound F D φ (withPhaseRemainders (D.azimuthalFrame φ) p φ G
      (tsgaError (D.azimuthalFrame φ) φ S T G p (2 * p - 1) C ε +
        C / ε ^ (2 * p - 1) * (∫ x, matrixGradNorm G x ^ p)))

/-- All three estimates in the physical azimuthal frame, keeping the original
uniformity of the constants in the sharp case. -/
theorem gradientForm_of_mainTSGA {F : GasEnergies} (h : MainExtendedTSGAEstimate F)
    (hspin : AxialGasInvariant F) {p : ℝ} (hp : 3 < p) :
    (∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ →
      ∃ C > 0, GradientFormEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∀ θ ν : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ → 0 < ν → ν ≤ 1 / 2 →
      ∃ C > 0, GradientFormEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) ∧
    (∃ C > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ → SharpGradientFormEstimate F p θ C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ hθ' hpθ
    obtain ⟨C, hC, hb⟩ := h.general p θ hp hθ hθ' hpθ
    exact ⟨C, hC, fun D φ S T G _ hD hφ ε hε => hb.gradientForm hspin D φ S T G trivial hD hφ hε⟩
  · intro θ ν hθ hθ' hpθ hν hν'
    obtain ⟨C, hC, hb⟩ := h.minority p θ ν hp hθ hθ' hpθ hν hν'
    exact ⟨C, hC, fun D φ S T G hc hD hφ ε hε => hb.gradientForm hspin D φ S T G
      ((minorityBound_azimuthalFrame_iff ν D φ).mpr hc) hD hφ hε⟩
  · obtain ⟨C, hC, hb⟩ := h.sharp p hp
    exact ⟨C, hC, fun θ hθ hθ' hpθ D φ S T G hD hG hLp hφ ε hε =>
      (hb θ hθ hθ' hpθ).gradientForm hspin D φ S T G hD hG hLp hφ hε⟩

/-! ## First derivative identities -/

/-- The scalar product rule for `a exp(iφ)` in a coordinate direction.
Division only uses that the transverse magnetization is nonzero. -/
theorem azimuthal_phase_derivative (a da α v mx my dx dy : ℝ)
    (hx : mx = a * Real.cos α) (hy : my = a * Real.sin α)
    (hdx : dx = da * Real.cos α - a * Real.sin α * v)
    (hdy : dy = da * Real.sin α + a * Real.cos α * v)
    (hn : mx ^ 2 + my ^ 2 ≠ 0) :
    v = (mx * dy - my * dx) / (mx ^ 2 + my ^ 2) := by
  apply (eq_div_iff hn).2
  rw [hx, hy, hdx, hdy]
  ring

/-- Derivatives of the two real components along any differentiable line.
For Sobolev fields these are the same local product and chain rules on ACL
representatives. -/
theorem azimuthal_phase_derivative_on_line {a φ : ℝ → ℝ} {t da v : ℝ}
    (ha : HasDerivAt a da t) (hφ : HasDerivAt φ v t)
    (hn : (a t * Real.cos (φ t)) ^ 2 + (a t * Real.sin (φ t)) ^ 2 ≠ 0) :
    v = (a t * Real.cos (φ t) * deriv (fun s => a s * Real.sin (φ s)) t -
      a t * Real.sin (φ t) * deriv (fun s => a s * Real.cos (φ s)) t) /
        ((a t * Real.cos (φ t)) ^ 2 + (a t * Real.sin (φ t)) ^ 2) := by
  apply azimuthal_phase_derivative (a t) da (φ t) v _ _ _ _ rfl rfl _ _ hn
  · change deriv (a * fun s => Real.cos (φ s)) t = _
    rw [(ha.mul hφ.cos).deriv]
    ring
  · change deriv (a * fun s => Real.sin (φ s)) t = _
    rw [(ha.mul hφ.sin).deriv]
    ring

/-- Off-diagonal entry of the first eigenvector projection. Its absolute value
is independent of the choice of phase of the eigenvector. -/
def spectralProjectorEntry {M : SpinMatrix} (hM : M.IsHermitian) : ℂ :=
  hM.eigenvectorUnitary 1 0 * star (hM.eigenvectorUnitary 0 0)

/-- The squared transverse component of the unit polarization vector, in
spectral coordinates. At a repeated eigenvalue it is multiplied by zero. -/
def transverseTiltSq {M : SpinMatrix} (hM : M.IsHermitian) : ℝ :=
  4 * ‖spectralProjectorEntry hM‖ ^ 2

private theorem cfc_offdiagonal {M : SpinMatrix} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    hM.cfc f 1 0 =
      ((f (hM.eigenvalues 0) - f (hM.eigenvalues 1) : ℝ) : ℂ) * spectralProjectorEntry hM := by
  let U := hM.eigenvectorUnitary
  have hu := congrArg (fun A : SpinMatrix => A 1 0) (Unitary.coe_mul_star_self U)
  change ((U : SpinMatrix) * star (U : SpinMatrix)) 1 0 = (1 : SpinMatrix) 1 0 at hu
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_ne
    (by decide : (1 : Fin 2) ≠ 0)] at hu
  change (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal _)) 1 0 = _
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_sub, spectralProjectorEntry]
  simp [Function.comp_apply]
  change _ = _ * ((U : SpinMatrix) 1 0 * star ((U : SpinMatrix) 0 0))
  change ((U : SpinMatrix) 1 0 * (f (hM.eigenvalues 0) : ℂ) * star ((U : SpinMatrix) 0 0) +
    (U : SpinMatrix) 1 1 * (f (hM.eigenvalues 1) : ℂ) * star ((U : SpinMatrix) 0 1)) = _
  linear_combination (f (hM.eigenvalues 1) : ℂ) * hu

/-- Identification of the spectral tilt with `sin² ϑ` from the magnetization.
This identity also holds for zero magnetization. -/
theorem transverseMagnetization_norm_sq {M : SpinMatrix} (hM : M.IsHermitian) :
    ‖transverseMagnetization M‖ ^ 2 =
      (hM.eigenvalues 0 - hM.eigenvalues 1) ^ 2 * transverseTiltSq hM := by
  have h := cfc_offdiagonal hM id
  have hid : hM.cfc id = M := by
    rw [← hM.cfc_eq, cfc_id ℝ M hM.isSelfAdjoint]
  rw [hid] at h
  simp only [transverseMagnetization, h, id_eq, transverseTiltSq, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Real spectral functions preserve the reality of the lower entry of a
Hermitian two-by-two matrix. The proof also covers repeated eigenvalues. -/
theorem cfc_lower_im_zero {M : SpinMatrix} (hM : M.IsHermitian) (hm : (M 1 0).im = 0)
    (f : ℝ → ℝ) : (hM.cfc f 1 0).im = 0 := by
  have hid : hM.cfc id = M := by rw [← hM.cfc_eq, cfc_id ℝ M hM.isSelfAdjoint]
  have h := congrArg Complex.im (cfc_offdiagonal hM id)
  rw [hid] at h
  simp only [hm, id_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h
  rw [cfc_offdiagonal]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rcases mul_eq_zero.mp h.symm with hgap | hproj
  · rw [sub_eq_zero.mp hgap, sub_self, zero_mul]
  · rw [hproj, mul_zero]

theorem Density.azimuthalFrame_power_lower_real (D : Density) (φ : Phase) (s : ℝ)
    (a : Position → ℝ) (hμ : ∀ x, transverseMagnetization (D.matrix x) =
      (a x : ℂ) * phaseFactor (φ.value x)) (x : Position) :
    (D.azimuthalFrame φ).power s x 1 0 = (((D.azimuthalFrame φ).power s x 1 0).re : ℂ) := by
  have hf : transverseMagnetization ((D.azimuthalFrame φ).matrix x) = (a x : ℂ) := by
    change transverseMagnetization (rotate _ _) = _
    rw [transverseMagnetization_rotate, hμ, mul_left_comm, ← phaseFactor_add]
    simp
  have hi := congrArg Complex.im hf
  simp [transverseMagnetization, Complex.mul_im] at hi
  have hz := cfc_lower_im_zero ((D.azimuthalFrame φ).positive x).isHermitian hi (fun t => t ^ s)
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im, Density.power]
    exact hz

theorem sqrt_offdiagonal_norm_sq (D : Density) (x : Position) :
    2 * ‖D.power (1 / 2) x 1 0‖ ^ 2 =
      (1 / 2 : ℝ) * (Real.sqrt ((D.positive x).isHermitian.eigenvalues 0) -
        Real.sqrt ((D.positive x).isHermitian.eigenvalues 1)) ^ 2 *
          transverseTiltSq (D.positive x).isHermitian := by
  rw [Density.power, cfc_offdiagonal]
  simp only [← Real.sqrt_eq_rpow, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, transverseTiltSq]
  ring

private theorem phaseFactor_norm (α : ℝ) : ‖phaseFactor α‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Entrywise derivative of a rotating real symmetric matrix. The real
off-diagonal entry is `b` and its directional derivative is `db`. -/
def rotatingDerivative (α b v du db dw : ℝ) : SpinMatrix :=
  let off := phaseFactor α * ((db : ℂ) + Complex.I * (b * v : ℝ))
  !![(du : ℂ), star off; off, (dw : ℂ)]

private theorem rotatingDerivative_diag (α b v du db dw : ℝ) (j : Fin 2) :
    rotatingDerivative α b v du db dw j j = if j = 0 then (du : ℂ) else (dw : ℂ) := by
  fin_cases j <;> simp [rotatingDerivative]

private theorem rotatingDerivative_sq (α b v du db dw : ℝ) :
    (∑ j, ∑ k, ‖rotatingDerivative α b v du db dw j k‖ ^ 2) =
      (∑ j, ∑ k, ‖rotatingDerivative 0 b 0 du db dw j k‖ ^ 2) + 2 * b ^ 2 * v ^ 2 := by
  have hoff : ‖phaseFactor α * ((db : ℂ) + Complex.I * (b * v : ℝ))‖ ^ 2 =
      db ^ 2 + b ^ 2 * v ^ 2 := by
    rw [norm_mul, phaseFactor_norm, one_mul, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  let z := phaseFactor α * ((db : ℂ) + Complex.I * (b * v : ℝ))
  let z₀ := phaseFactor 0 * ((db : ℂ) + Complex.I * (b * 0 : ℝ))
  have hz₀ : z₀ = (db : ℂ) := by simp [z₀]
  simp only [Fin.sum_univ_two]
  change (‖(du : ℂ)‖ ^ 2 + ‖star z‖ ^ 2) + (‖z‖ ^ 2 + ‖(dw : ℂ)‖ ^ 2) =
    (‖(du : ℂ)‖ ^ 2 + ‖star z₀‖ ^ 2 + (‖z₀‖ ^ 2 + ‖(dw : ℂ)‖ ^ 2)) + _
  simp only [norm_star, hz₀, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show ‖z‖ ^ 2 = db ^ 2 + b ^ 2 * v ^ 2 from hoff]
  ring

/-- Hilbert–Schmidt identity for the two gradient representatives obtained
by the local weak product rule. The diagonal entry derivatives cancel. -/
theorem rotating_sqrt_gradient_sq {S L : MatrixGradient} {x : Position} (α b : ℝ)
    (v : Position) (du db dw : Fin 3 → ℝ)
    (hs : ∀ i, S x i = rotatingDerivative 0 b 0 (du i) (db i) (dw i))
    (hl : ∀ i, L x i = rotatingDerivative α b (v i) (du i) (db i) (dw i)) :
    matrixGradNorm S x ^ 2 = matrixGradNorm L x ^ 2 - 2 * b ^ 2 * ‖v‖ ^ 2 := by
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    rotatingDerivative_sq α b (v i) (du i) (db i) (dw i))
  simp only [matrixGradNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _), hs, hl]
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  ring

/-- Distributional partial derivatives commute with complex conjugation. -/
theorem WeakPartialOn.conjugate {U : Set Position} {i : Fin 3} {u du : Position → ℂ}
    (h : WeakPartialOn U i u du) :
    WeakPartialOn U i (fun x => star (u x)) (fun x => star (du x)) := by
  let L := Complex.conjCLE
  have hloc {f : Position → ℂ} (hf : LocallyIntegrableOn f U) :
      LocallyIntegrableOn (fun x => L (f x)) U := by
    intro x hx
    obtain ⟨s, hs, hi⟩ := hf x hx
    exact ⟨s, hs, L.toContinuousLinearMap.integrable_comp hi⟩
  refine ⟨hloc h.1, hloc h.2.1, ?_⟩
  intro ψ hψ hc hU
  have heq := congrArg L (h.2.2 ψ hψ hc hU)
  rw [← L.integral_comp_comm, map_neg, ← L.integral_comp_comm] at heq
  simp only [map_smul] at heq
  exact heq

private theorem WeakPartialOn.unique {i : Fin 3} {u d₁ d₂ : Position → ℂ}
    (h₁ : WeakPartialOn Set.univ i u d₁) (h₂ : WeakPartialOn Set.univ i u d₂) :
    d₁ =ᵐ[volume] d₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq (locallyIntegrableOn_univ.mp h₁.2.1)
    (locallyIntegrableOn_univ.mp h₂.2.1)
  intro ψ hψ hcompact
  have ht := (h₁.2.2 ψ hψ hcompact (Set.subset_univ _)).symm.trans
    (h₂.2.2 ψ hψ hcompact (Set.subset_univ _))
  simpa only [Measure.restrict_univ, neg_inj] using ht

private theorem WeakPartialOn.congr_derivative {i : Fin 3} {u d₁ d₂ : Position → ℂ}
    (h : WeakPartialOn Set.univ i u d₁) (he : d₁ =ᵐ[volume] d₂) :
    WeakPartialOn Set.univ i u d₂ := by
  have he' : d₁ =ᵐ[volume.restrict Set.univ] d₂ := by simpa using he
  refine ⟨h.1, h.2.1.congr he', ?_⟩
  intro ψ hψ hc hU
  rw [h.2.2 ψ hψ hc hU]
  congr 1
  exact integral_congr_ae (he'.mono fun x hx => congrArg (fun z : ℂ => ψ x • z) hx)

private theorem WeakPartialOn.real_derivative {i : Fin 3} {u du : Position → ℂ}
    (h : WeakPartialOn Set.univ i u du) (hr : ∀ x, star (u x) = u x) :
    ∀ᵐ x, ((du x).re : ℂ) = du x := by
  have hc := h.conjugate
  simp only [hr] at hc
  exact (hc.unique h).mono fun x hx => Complex.conj_eq_iff_re.mp hx

/-- Scalar Sobolev product rule for multiplication by the phase factor. -/
structure AzimuthalWeakRules (φ : Phase) : Prop where
  phase_product : ∀ (i : Fin 3) (u du : Position → ℂ), WeakPartialOn Set.univ i u du →
    WeakPartialOn Set.univ i (fun x => phaseFactor (φ.value x) * u x)
      (fun x => phaseFactor (φ.value x) * (du x + Complex.I * (u x * (φ.grad x i : ℂ))))

/-- The same scalar Sobolev law used for axial kinetic localization gives
the signed-amplitude rule for every regular phase. -/
theorem azimuthalWeakRules_of_phaseProduct (chain : WeakPhaseProduct) {p : ℝ} {φ : Phase}
    (hφ : φ.Regular p) : AzimuthalWeakRules φ where
  phase_product i u du hu := by
    have h := chain φ hφ 1 i u du hu
    have he (x : Position) : Complex.I * (φ.grad x i : ℂ) * u x =
        Complex.I * (u x * (φ.grad x i : ℂ)) := by ring
    simpa only [one_mul, Complex.ofReal_one, mul_one, he] using h

/-- Obtain the phase formula for an actual weak gradient representative of
the transverse magnetization from the scalar Sobolev product rule. -/
theorem weak_azimuthal_phase_derivative {φ : Phase} (rules : AzimuthalWeakRules φ)
    (a : Position → ℝ) (i : Fin 3) (da : Position → ℝ)
    (ha : WeakPartialOn Set.univ i (fun x => (a x : ℂ)) (fun x => (da x : ℂ))) :
    ∃ dμ : Position → ℂ,
      WeakPartialOn Set.univ i (fun x => phaseFactor (φ.value x) * (a x : ℂ)) dμ ∧
      ∀ x, let μ := phaseFactor (φ.value x) * (a x : ℂ)
           μ.re ^ 2 + μ.im ^ 2 ≠ 0 →
             φ.grad x i = (μ.re * (dμ x).im - μ.im * (dμ x).re) / (μ.re ^ 2 + μ.im ^ 2) := by
  refine ⟨_, rules.phase_product i _ _ ha, ?_⟩
  intro x
  dsimp only
  intro hn
  apply azimuthal_phase_derivative (a x) (da x) (φ.value x) _ _ _ _ _ _ _ _ _ hn
  all_goals
    simp [phaseFactor, Complex.mul_re, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

/-- Functional calculus commutes with the pointwise spin rotation. -/
theorem rotate_cfc {M : SpinMatrix} (hM : M.PosSemidef) (α : ℝ) (f : ℝ → ℝ) :
    rotate α (hM.isHermitian.cfc f) = (rotate_posSemidef α hM).isHermitian.cfc f := by
  let U : unitary SpinMatrix := ⟨spinRotation α,
    (Matrix.mem_specialUnitaryGroup_iff.mp (spinRotation_mem_specialUnitaryGroup α)).1⟩
  let e := Unitary.conjStarAlgAut ℂ SpinMatrix U
  have hec : Continuous e := e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  rw [← hM.isHermitian.cfc_eq, ← (rotate_posSemidef α hM).isHermitian.cfc_eq]
  exact StarAlgHomClass.map_cfc (S := ℂ) e f M
    (by rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues]
        exact (Set.finite_range _).continuousOn _) hec hM.isHermitian.isSelfAdjoint
    (rotate_posSemidef α hM).isHermitian.isSelfAdjoint

theorem Density.rotate_power_azimuthalFrame (D : Density) (φ : Phase) (s : ℝ) (x : Position) :
    rotate (φ.value x) ((D.azimuthalFrame φ).power s x) = D.power s x := by
  rw [Density.power, rotate_cfc ((D.azimuthalFrame φ).positive x), Density.power,
    ← (rotate_posSemidef _ ((D.azimuthalFrame φ).positive x)).isHermitian.cfc_eq,
    D.rotate_azimuthalFrame, (D.positive x).isHermitian.cfc_eq]

private theorem Density.power_hermitian (D : Density) (s : ℝ) (x : Position) :
    (D.power s x).IsHermitian := by
  rw [Density.power, ← (D.positive x).isHermitian.cfc_eq]
  exact (cfc_predicate (fun t : ℝ => t ^ s) (D.matrix x)).isHermitian

private theorem rotate_lower (α : ℝ) (M : SpinMatrix) :
    rotate α M 1 0 = phaseFactor α * M 1 0 := by
  have h := transverseMagnetization_rotate α M
  unfold transverseMagnetization at h
  linear_combination h / 2

/-- Entrywise real symmetric gradient of the root in the moving frame. -/
def frameRootGradient (du db dw : Position → Fin 3 → ℝ) : MatrixGradient :=
  fun x i => rotatingDerivative 0 0 0 (du x i) (db x i) (dw x i)

/-- The laboratory gradient, including the phase derivative of the lower
off-diagonal entry. -/
def rotatingRootGradient (φ : Phase) (b : Position → ℝ) (du db dw : Position → Fin 3 → ℝ) :
    MatrixGradient := fun x i =>
  rotatingDerivative (φ.value x) (b x) (φ.grad x i) (du x i) (db x i) (dw x i)

/-- The weak product rule constructs the physical matrix-root gradient.
Its Hilbert–Schmidt norm satisfies the exact polar-angle formula, including
at coincident eigenvalues and at zero transverse magnetization. -/
theorem weak_sqrt_gradient_identity (D : Density) (φ : Phase) (rules : AzimuthalWeakRules φ)
    (b : Position → ℝ) (du db dw : Position → Fin 3 → ℝ)
    (hb : ∀ x, (D.azimuthalFrame φ).power (1 / 2) x 1 0 = (b x : ℂ))
    (hs : IsMatrixGradientOn Set.univ ((D.azimuthalFrame φ).power (1 / 2))
      (frameRootGradient du db dw)) :
    IsMatrixGradientOn Set.univ (D.power (1 / 2)) (rotatingRootGradient φ b du db dw) ∧
      ∀ x, let hM := ((D.azimuthalFrame φ).positive x).isHermitian
           matrixGradNorm (frameRootGradient du db dw) x ^ 2 =
             matrixGradNorm (rotatingRootGradient φ b du db dw) x ^ 2 -
             (1 / 2 : ℝ) * (Real.sqrt (hM.eigenvalues 0) - Real.sqrt (hM.eigenvalues 1)) ^ 2 *
             transverseTiltSq hM * ‖φ.grad x‖ ^ 2 := by
  have hlow (x : Position) : D.power (1 / 2) x 1 0 = phaseFactor (φ.value x) * (b x : ℂ) := by
    rw [← D.rotate_power_azimuthalFrame φ, rotate_lower, hb]
  have hdiag (x : Position) (j : Fin 2) :
      D.power (1 / 2) x j j = (D.azimuthalFrame φ).power (1 / 2) x j j := by
    rw [← D.rotate_power_azimuthalFrame φ, rotate_diag]
  have hlowD (i : Fin 3) : WeakPartialOn Set.univ i (fun x => D.power (1 / 2) x 1 0)
      (fun x => rotatingRootGradient φ b du db dw x i 1 0) := by
    have hbD := hs i 1 0
    simp only [hb] at hbD
    change WeakPartialOn Set.univ i (fun x => (b x : ℂ)) (fun x =>
      phaseFactor 0 * ((db x i : ℂ) + Complex.I * (((0 : ℝ) * 0 : ℝ) : ℂ))) at hbD
    simp only [phaseFactor_zero, mul_zero, Complex.ofReal_zero, add_zero, one_mul] at hbD
    have h := rules.phase_product i _ _ hbD
    simp only [hlow]
    change WeakPartialOn _ _ _ (fun x => phaseFactor (φ.value x) * ((db x i : ℂ) +
      Complex.I * ((b x * φ.grad x i : ℝ) : ℂ)))
    simpa only [Complex.ofReal_mul] using h
  have diagonal (i : Fin 3) (j : Fin 2) :
      WeakPartialOn Set.univ i (fun x => D.power (1 / 2) x j j)
        (fun x => rotatingRootGradient φ b du db dw x i j j) := by
    have hd (x : Position) : rotatingRootGradient φ b du db dw x i j j = frameRootGradient du db dw x i j j := by
      simp only [rotatingRootGradient, frameRootGradient, rotatingDerivative_diag]
    exact (congrArg₂ (WeakPartialOn Set.univ i) (funext (fun x => hdiag x j)) (funext hd)).mpr (hs i j j)
  constructor
  · intro i j k
    have cases (a : Fin 2) : a = 0 ∨ a = 1 := by omega
    rcases cases j with rfl | rfl <;> rcases cases k with rfl | rfl
    · exact diagonal i 0
    · have hu (x : Position) : star (D.power (1 / 2) x 1 0) = D.power (1 / 2) x 0 1 :=
        (D.power_hermitian _ x).apply 0 1
      have hd (x : Position) : star (rotatingRootGradient φ b du db dw x i 1 0) =
          rotatingRootGradient φ b du db dw x i 0 1 := by simp [rotatingRootGradient, rotatingDerivative]
      have hg := (hlowD i).conjugate
      simp only [hu, hd] at hg
      exact hg
    · exact hlowD i
    · exact diagonal i 1
  · intro x
    dsimp only
    have he := sqrt_offdiagonal_norm_sq (D.azimuthalFrame φ) x
    rw [hb] at he
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at he
    rw [← he]
    exact rotating_sqrt_gradient_sq (φ.value x) (b x) (φ.grad x) (du x) (db x) (dw x)
      (fun i => by simp [frameRootGradient, rotatingDerivative]) (fun _ => rfl)

/-- The square-root gradient identity for any given weak gradient of the
moving frame, with the canonical signed-amplitude factorization as input. -/
theorem azimuthal_sqrt_gradient (D : Density) (φ : Phase) (rules : AzimuthalWeakRules φ)
    (a : Position → ℝ) (hμ : ∀ x, transverseMagnetization (D.matrix x) =
      (a x : ℂ) * phaseFactor (φ.value x)) (S : MatrixGradient)
    (hS : IsMatrixGradientOn Set.univ ((D.azimuthalFrame φ).power (1 / 2)) S) :
    ∃ L : MatrixGradient, IsMatrixGradientOn Set.univ (D.power (1 / 2)) L ∧
      ∀ᵐ x, let hM := ((D.azimuthalFrame φ).positive x).isHermitian
            matrixGradNorm S x ^ 2 = matrixGradNorm L x ^ 2 -
              (1 / 2 : ℝ) * (Real.sqrt (hM.eigenvalues 0) - Real.sqrt (hM.eigenvalues 1)) ^ 2 *
                transverseTiltSq hM * ‖φ.grad x‖ ^ 2 := by
  let B := (D.azimuthalFrame φ).power (1 / 2)
  let b (x : Position) := (B x 1 0).re
  let du (x : Position) (i : Fin 3) := (S x i 0 0).re
  let db (x : Position) (i : Fin 3) := (S x i 1 0).re
  let dw (x : Position) (i : Fin 3) := (S x i 1 1).re
  have hr (x : Position) : B x 1 0 = (b x : ℂ) := D.azimuthalFrame_power_lower_real φ _ a hμ x
  have hHerm (x : Position) : (B x).IsHermitian := (D.azimuthalFrame φ).power_hermitian _ x
  have hrep (i : Fin 3) : ∀ᵐ x, S x i = frameRootGradient du db dw x i := by
    have hd (j : Fin 2) := (hS i j j).real_derivative (fun x => (hHerm x).apply j j)
    have hlow := (hS i 1 0).real_derivative (fun x => by
      change star (B x 1 0) = B x 1 0
      rw [hr]
      exact Complex.conj_ofReal _)
    have hstar : (fun x => star (S x i 1 0)) =ᵐ[volume] (fun x => S x i 0 1) := by
      have hu := (hS i 1 0).conjugate
      have he (x : Position) : star (B x 1 0) = B x 0 1 := (hHerm x).apply 0 1
      change WeakPartialOn _ _ (fun x => star (B x 1 0)) _ at hu
      simp only [he] at hu
      exact hu.unique (hS i 0 1)
    filter_upwards [hd 0, hd 1, hlow, hstar] with x h₀ h₁ hₗ hᵤ
    apply Matrix.ext
    intro j k
    fin_cases j <;> fin_cases k
    · exact h₀.symm
    · change star (S x i 1 0) = S x i 0 1 at hᵤ
      change S x i 0 1 = star (phaseFactor 0 * ((db x i : ℂ) + Complex.I * ((0 : ℝ) * 0 : ℝ)))
      simp only [phaseFactor_zero, mul_zero, Complex.ofReal_zero, add_zero, one_mul]
      exact hᵤ.symm.trans (congrArg star hₗ.symm)
    · change S x i 1 0 = phaseFactor 0 * ((db x i : ℂ) + Complex.I * ((0 : ℝ) * 0 : ℝ))
      simpa only [phaseFactor_zero, mul_zero, Complex.ofReal_zero, add_zero, one_mul] using hₗ.symm
    · exact h₁.symm
  have hs : IsMatrixGradientOn Set.univ B (frameRootGradient du db dw) := by
    intro i j k
    exact (hS i j k).congr_derivative ((hrep i).mono fun x hx => congrArg (fun M : SpinMatrix => M j k) hx)
  obtain ⟨hL, hnorm⟩ := weak_sqrt_gradient_identity D φ rules b du db dw hr hs
  refine ⟨_, hL, ?_⟩
  filter_upwards [ae_all_iff.mpr hrep] with x hx
  have he : S x = frameRootGradient du db dw x := funext hx
  simpa only [matrixGradNorm, he] using hnorm x

/-- The part of the physical square-root kinetic density due to rotation
around the chosen axis. -/
def azimuthalKineticDensity (D : Density) (φ : Phase) (x : Position) : ℝ :=
  let hM := ((D.azimuthalFrame φ).positive x).isHermitian
  (1 / 2 : ℝ) * (Real.sqrt (hM.eigenvalues 0) - Real.sqrt (hM.eigenvalues 1)) ^ 2 *
    transverseTiltSq hM * ‖φ.grad x‖ ^ 2

/-- Integrated gradient formula for the square-root term in the TSGA
error. Integrability of the subtracted angular term follows from the two
square-root kinetic energies and the pointwise identity. -/
theorem integral_azimuthal_sqrt_gradient (D : Density) (φ : Phase) (chain : WeakPhaseProduct)
    {p : ℝ} (hφ : φ.Regular p) (a : Position → ℝ) (hμ : ∀ x, transverseMagnetization (D.matrix x) =
      (a x : ℂ) * phaseFactor (φ.value x)) (S : MatrixGradient)
    (hS : IsMatrixGradientOn Set.univ ((D.azimuthalFrame φ).power (1 / 2)) S)
    (hsLp : MemLp (matrixGradNorm S) 2) (hkin : Integrable (fun x => D.charge x * ‖φ.grad x‖ ^ 2)) :
    ∃ L : MatrixGradient, IsMatrixGradientOn Set.univ (D.power (1 / 2)) L ∧
      MemLp (matrixGradNorm L) 2 ∧ Integrable (azimuthalKineticDensity D φ) ∧
      (∫ x, matrixGradNorm S x ^ 2) =
        (∫ x, matrixGradNorm L x ^ 2) - ∫ x, azimuthalKineticDensity D φ x := by
  obtain ⟨W, hw, hpt⟩ := azimuthal_sqrt_gradient D φ (azimuthalWeakRules_of_phaseProduct chain hφ)
    a hμ S hS
  obtain ⟨L, hl, hLp, _⟩ := rotated_sqrt_kinetic_of_weak chain hS hsLp hφ
    (by simpa only [Density.charge_azimuthalFrame] using hkin)
  have hroot : (rotatedDensity (D.azimuthalFrame φ) φ).power (1 / 2) = D.power (1 / 2) :=
    funext fun x => (rotated_power _ _ (by norm_num) x).trans (D.rotate_power_azimuthalFrame φ _ x)
  rw [hroot] at hl
  have hwl : ∀ᵐ x, ∀ i j k, W x i j k = L x i j k :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      (hw i j k).unique (hl i j k)
  have heq : (fun x => matrixGradNorm S x ^ 2) =ᵐ[volume]
      (fun x => matrixGradNorm L x ^ 2 - azimuthalKineticDensity D φ x) := by
    filter_upwards [hwl, hpt] with x he h
    have hmatrix : W x = L x := funext fun i => Matrix.ext (he i)
    simpa only [matrixGradNorm, hmatrix, azimuthalKineticDensity] using h
  have hiL : Integrable (fun x => matrixGradNorm L x ^ 2) := hLp.integrable_sq
  have hiS : Integrable (fun x => matrixGradNorm S x ^ 2) := hsLp.integrable_sq
  have hiA : Integrable (azimuthalKineticDensity D φ) := (hiL.sub hiS).congr (heq.mono fun x hx => by
    change matrixGradNorm L x ^ 2 - matrixGradNorm S x ^ 2 = azimuthalKineticDensity D φ x
    dsimp only at hx
    linarith)
  exact ⟨L, hl, hLp, hiA, (integral_congr_ae heq).trans (integral_sub hiL hiA)⟩

end TSGA
