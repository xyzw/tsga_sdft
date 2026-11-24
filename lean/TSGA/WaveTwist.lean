import TSGA.StateSpinRotation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Spin-dependent plane waves on a fermionic sector

Multiplication by the product of the one-electron phases implements a spin
spiral or a common Galilean boost. The product rule below follows from the
distributional derivatives in the definition of an admissible wave.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff

/-- Product of the plane waves associated with the occupied spin indices. -/
def spinWavePhase {n : ℕ} (v : Fin 2 → Position) (s : Spins n) (x : Space n) : ℂ :=
  phaseFactor (∑ i, ⟪v (s i), x i⟫_ℝ)

@[simp] theorem spinWavePhase_norm {n : ℕ} (v : Fin 2 → Position) (s : Spins n) (x : Space n) :
    ‖spinWavePhase v s x‖ = 1 := by simp [spinWavePhase, phaseFactor, Complex.norm_exp]

private def phaseLinear {n : ℕ} (v : Fin 2 → Position) (s : Spins n) : Space n →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (v (s i))).comp (ContinuousLinearMap.proj i)

private theorem phaseLinear_apply {n : ℕ} (v : Fin 2 → Position) (s : Spins n) (x : Space n) :
    phaseLinear v s x = ∑ i, ⟪v (s i),x i⟫_ℝ := by
  simp [phaseLinear, innerSL_apply_apply]

private theorem phase_as_exp {n : ℕ} (v : Fin 2 → Position) (s : Spins n) :
    spinWavePhase v s = fun x => Complex.exp (((phaseLinear v s x : ℝ) : ℂ) * Complex.I) := by
  funext x
  rw [phaseLinear_apply]
  rfl

theorem spinWavePhase_smooth {n : ℕ} (v : Fin 2 → Position) (s : Spins n) :
    ContDiff ℝ ∞ (spinWavePhase v s) := by
  rw [phase_as_exp]
  exact ((Complex.ofRealCLM.contDiff.comp (phaseLinear v s).contDiff).mul contDiff_const).cexp

private theorem phase_derivative {n : ℕ} (v : Fin 2 → Position) (s : Spins n)
    (x : Space n) (i : Fin n) (j : Fin 3) :
    fderiv ℝ (spinWavePhase v s) x (particleDirection i j) =
      spinWavePhase v s x * (Complex.I * (v (s i) j : ℂ)) := by
  let L := phaseLinear v s
  have he : L (particleDirection i j) = v (s i) j := by
    rw [phaseLinear_apply]
    rw [Finset.sum_eq_single i]
    · simp [particleDirection, EuclideanSpace.inner_single_right]
    · intro k _ hk
      simp [particleDirection, Pi.single_eq_of_ne hk]
    · simp
  have h := (((Complex.ofRealCLM.hasFDerivAt.comp x L.hasFDerivAt).mul_const Complex.I).cexp).fderiv
  rw [phase_as_exp]
  change fderiv ℝ (fun x => Complex.exp (((Complex.ofRealCLM ∘ L) x) * Complex.I)) x _ = _
  rw [h]
  change Complex.exp ((L x : ℂ)*Complex.I)*(Complex.I*(L (particleDirection i j) : ℂ)) = _
  rw [he]

@[simp] theorem spinWavePhase_zero {n : ℕ} (s : Spins n) (x : Space n) :
    spinWavePhase 0 s x = 1 := by simp [spinWavePhase]

theorem spinWavePhase_add {n : ℕ} (v w : Fin 2 → Position) (s : Spins n) (x : Space n) :
    spinWavePhase (v+w) s x = spinWavePhase v s x * spinWavePhase w s x := by
  simp [spinWavePhase, inner_add_left, Finset.sum_add_distrib, phaseFactor_add]

theorem spinWavePhase_perm {n : ℕ} (v : Fin 2 → Position) (s : Spins n) (x : Space n)
    (π : Equiv.Perm (Fin n)) : spinWavePhase v (s ∘ π) (x ∘ π) = spinWavePhase v s x :=
  congrArg phaseFactor (Equiv.sum_comp π (fun i => ⟪v (s i), x i⟫_ℝ))

private theorem memLp_phase_mul {n : ℕ} (v : Fin 2 → Position) (s : Spins n)
    {f : Space n → ℂ} (hf : MemLp f 2) : MemLp (fun x => spinWavePhase v s x * f x) 2 :=
  hf.mono ((spinWavePhase_smooth v s).continuous.aestronglyMeasurable.mul hf.1)
    (ae_of_all _ fun x => by simp)

private theorem test_integrable {n : ℕ} {f : Space n → ℂ} (hf : MemLp f 2)
    {g : Space n → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun x => g x * f x) :=
  (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hg hc

private theorem weak_complex_test {n : ℕ} (ψ : Wave n) (s : Spins n) (i : Fin n) (j : Fin 3)
    (g : Space n → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ x, fderiv ℝ g x (particleDirection i j) * ψ.value s x) = -(∫ x, g x * ψ.gradient s x i j) := by
  let d := particleDirection i j
  let dg := fun x => fderiv ℝ g x d
  have hdc : Continuous dg := (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport dg := hc.fderiv_apply ℝ d
  have split {f w : Space n → ℂ} (hf : MemLp f 2) (hw : Continuous w) (hs : HasCompactSupport w) :
      (∫ x, w x * f x) = (∫ x, (w x).re • f x) + Complex.I * (∫ x, (w x).im • f x) := by
    have hi (l : ℂ →L[ℝ] ℝ) : Integrable (fun x => l (w x) • f x) :=
      (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        (l.continuous.comp hw) (hs.comp_left (map_zero l))
    have ir : Integrable (fun x => (w x).re • f x) := hi Complex.reCLM
    have ii : Integrable (fun x => Complex.I * ((w x).im • f x)) := (hi Complex.imCLM).const_mul _
    rw [← integral_const_mul, ← integral_add ir ii]
    apply integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [Complex.real_smul, Complex.real_smul, ← mul_assoc, mul_comm Complex.I, ← add_mul, Complex.re_add_im]
  have w (l : ℂ →L[ℝ] ℝ) :
      (∫ x, l (dg x) • ψ.value s x) = -(∫ x, l (g x) • ψ.gradient s x i j) := by
    have h := ψ.weak_gradient s i j (l ∘ g) (l.contDiff.comp hg) (hc.comp_left (map_zero l))
    have deriv (x : Space n) : fderiv ℝ (l ∘ g) x d = l (dg x) := by
      rw [(l.hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)).fderiv]
      rfl
    simpa only [← deriv, Function.comp_apply] using h
  change (∫ x, dg x * ψ.value s x) = _
  rw [split (ψ.square_integrable s) hdc hds, split (ψ.gradient_L2 s i j) hg.continuous hc]
  change (∫ x, Complex.reCLM (dg x) • ψ.value s x) + Complex.I * (∫ x, Complex.imCLM (dg x) • ψ.value s x) = _
  rw [w Complex.reCLM, w Complex.imCLM]
  simp [add_comm]

private theorem twisted_weak {n : ℕ} (ψ : Wave n) (v : Fin 2 → Position) (s : Spins n)
    (i : Fin n) (j : Fin 3) (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, fderiv ℝ f x (particleDirection i j) • (spinWavePhase v s x * ψ.value s x)) =
      -(∫ x, f x • (spinWavePhase v s x *
        (ψ.gradient s x i j + Complex.I * (v (s i) j : ℂ) * ψ.value s x))) := by
  let p := spinWavePhase v s
  let a := Complex.I * (v (s i) j : ℂ)
  let d := particleDirection i j
  let df := fun x => fderiv ℝ f x d
  let g := fun x => (f x : ℂ) * p x
  have hp := spinWavePhase_smooth v s
  have hf' : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hfc : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hgc : HasCompactSupport g := hfc.mul_right
  have hdf : Continuous df := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdfc : HasCompactSupport (fun x => (df x : ℂ)) := (hc.fderiv_apply ℝ d).comp_left Complex.ofReal_zero
  have hw := weak_complex_test ψ s i j g (hf'.mul hp) hgc
  have deriv (x : Space n) : fderiv ℝ g x d = (df x : ℂ) * p x + g x * a := by
    have h := ((Complex.ofRealCLM.hasFDerivAt.comp x ((hf.differentiable (by simp) x).hasFDerivAt)).mul
      ((hp.differentiable (by simp) x).hasFDerivAt)).fderiv
    change fderiv ℝ ((Complex.ofRealCLM ∘ f) * spinWavePhase v s) x d = _
    rw [h]
    simp only [Function.comp_apply, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, g, df, p, a, d, phase_derivative]
    ring
  let A := fun x => (df x : ℂ)*p x*ψ.value s x
  let B := fun x => (g x*a)*ψ.value s x
  let C := fun x => g x*ψ.gradient s x i j
  have hA : Integrable A := test_integrable (ψ.square_integrable s)
    ((Complex.continuous_ofReal.comp hdf).mul hp.continuous) hdfc.mul_right
  have hB : Integrable B := test_integrable (ψ.square_integrable s)
    (((hf'.mul hp).continuous).mul continuous_const) hgc.mul_right
  have hC : Integrable C := test_integrable (ψ.gradient_L2 s i j) (hf'.mul hp).continuous hgc
  have hsum : (∫ x, A x) + (∫ x, B x) = -(∫ x, C x) := by
    change (∫ x, fderiv ℝ g x d * ψ.value s x) = -(∫ x, C x) at hw
    rw [← integral_add hA hB]
    simpa only [A, B, deriv, add_mul] using hw
  have e₁ (x) : df x • (p x * ψ.value s x) = A x := by simp [A, Complex.real_smul, mul_assoc]
  have e₂ (x) : f x • (p x * (ψ.gradient s x i j + a * ψ.value s x)) = C x + B x := by
    simp only [Complex.real_smul, C, B, g]; ring
  change (∫ x, df x • (p x * ψ.value s x)) = -(∫ x, f x • (p x * (ψ.gradient s x i j + a * ψ.value s x)))
  simp_rw [e₁,e₂]
  rw [integral_add hC hB]
  linear_combination hsum

/-- Spin-dependent uniform velocity added to each electron. -/
def Wave.twist {n : ℕ} (ψ : Wave n) (v : Fin 2 → Position) : Wave n where
  value s x := spinWavePhase v s x * ψ.value s x
  gradient s x i j := spinWavePhase v s x *
    (ψ.gradient s x i j + Complex.I * (v (s i) j : ℂ) * ψ.value s x)
  antisymmetric π s := by
    filter_upwards [ψ.antisymmetric π s] with x hx
    rw [spinWavePhase_perm, hx]
    ring
  square_integrable s := memLp_phase_mul v s (ψ.square_integrable s)
  normalized := by simpa only [norm_mul, spinWavePhase_norm, one_mul] using ψ.normalized
  gradient_L2 s i j := memLp_phase_mul v s ((ψ.gradient_L2 s i j).add ((ψ.square_integrable s).const_mul _))
  weak_gradient := twisted_weak ψ v
  interaction_integrable s := by simpa only [norm_mul, spinWavePhase_norm, one_mul] using ψ.interaction_integrable s

@[simp] theorem Wave.interaction_twist {n : ℕ} (ψ : Wave n) (v : Fin 2 → Position) :
    (ψ.twist v).interaction = ψ.interaction := by simp [Wave.interaction, Wave.twist]

@[simp] theorem Wave.twist_zero {n : ℕ} (ψ : Wave n) : ψ.twist 0 = ψ := by
  cases ψ
  simp [Wave.twist]

theorem Wave.twist_add {n : ℕ} (ψ : Wave n) (v w : Fin 2 → Position) :
    (ψ.twist v).twist w = ψ.twist (v+w) := by
  have eq {φ χ : Wave n} (h : φ.value = χ.value) (d : φ.gradient = χ.gradient) : φ = χ := by
    cases φ
    cases χ
    cases h
    cases d
    rfl
  apply eq
  · funext s x
    simp only [Wave.twist, spinWavePhase_add]
    ring
  · funext s x i j
    simp only [Wave.twist, spinWavePhase_add, Pi.add_apply, PiLp.add_apply, Complex.ofReal_add]
    ring

private theorem spinWavePhase_pair {n : ℕ} (v : Fin 2 → Position) (s : Spins n)
    (i j : Fin 2) (x : Position) (y : Space n) :
    spinWavePhase v (Fin.cons i s) (Fin.cons x y) * conj (spinWavePhase v (Fin.cons j s) (Fin.cons x y)) =
      phaseFactor (⟪v i,x⟫_ℝ - ⟪v j,x⟫_ℝ) := by
  change phaseFactor _ * star (phaseFactor _) = _
  rw [star_phaseFactor, ← phaseFactor_add]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  ring

/-- Only the two exposed spin indices contribute a relative phase to the marginal. -/
theorem Wave.matrixDensity_twist {n : ℕ} (ψ : Wave (n+1)) (v : Fin 2 → Position) (x : Position) (i j : Fin 2) :
    (ψ.twist v).matrixDensity x i j =
      phaseFactor (⟪v i,x⟫_ℝ - ⟪v j,x⟫_ℝ) * ψ.matrixDensity x i j := by
  unfold Wave.matrixDensity
  simp only [Wave.twist, map_mul]
  have h (s : Spins n) (y : Space n) :
      spinWavePhase v (Fin.cons i s) (Fin.cons x y) * ψ.value (Fin.cons i s) (Fin.cons x y) *
        (conj (spinWavePhase v (Fin.cons j s) (Fin.cons x y)) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))) =
      phaseFactor (⟪v i,x⟫_ℝ - ⟪v j,x⟫_ℝ) *
        (ψ.value (Fin.cons i s) (Fin.cons x y) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))) := by
    rw [← spinWavePhase_pair v s i j x y]; ring
  simp_rw [h, integral_const_mul, ← Finset.mul_sum]
  ring

end TSGA.ManyBody
