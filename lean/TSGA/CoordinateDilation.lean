import TSGA.CoulombSpiral
import TSGA.BallSequence

/-! # Coordinate dilation of the Coulomb constrained search

Dilating an n-electron amplitude by b rescales its normalization by the
square root of the 3n-dimensional Jacobian. The same map on each sector
of a mixture rescales the kinetic, interaction, and direct energies.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory MeasureTheory.Measure
open scoped ContDiff ComplexConjugate

def coordinateDensity (b : ℝ) (M : Position → SpinMatrix) : Position → SpinMatrix :=
  fun x => b^3 • M (b • x)

def indirectAt (M : Position → SpinMatrix) (Γ : MixedState) : ℝ :=
  Γ.interaction - hartree (fun x => (M x).trace.re)

/-- Change of variables for the normalized many-body wave functions in each
particle sector. It identifies the feasible states in both directions. -/
structure StateDilation (b : ℝ) (M : Position → SpinMatrix) where
  states : {Γ // feasible M Γ} ≃ {Γ // feasible (coordinateDensity b M) Γ}
  kinetic : ∀ s, (states s).val.kinetic = b^2 * s.val.kinetic
  indirect : ∀ s, indirectAt (coordinateDensity b M) (states s).val = b * indirectAt M s.val

def CoordinateDilationLaw : Prop :=
  ∀ b : ℝ, 0 < b → ∀ M : Position → SpinMatrix, Nonempty (StateDilation b M)

private def jac (n : ℕ) (b : ℝ) : ℝ := (b^3)^n
private def amp (n : ℕ) (b : ℝ) : ℝ := √(jac n b)

private theorem jac_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < jac n b := pow_pos (pow_pos hb 3) n

private theorem amp_sq (n : ℕ) {b : ℝ} (hb : 0 < b) : amp n b ^ 2 = jac n b :=
  Real.sq_sqrt (jac_pos n hb).le

private theorem amp_inv (n : ℕ) (b : ℝ) : amp n b⁻¹ = (amp n b)⁻¹ := by
  simp [amp, jac, Real.sqrt_inv]

private theorem sector_change {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) {b : ℝ} (hb : 0 < b) :
    (∫ x, f (b • x)) = (jac n b)⁻¹ • ∫ y, f y := by
  have dim : Module.finrank ℝ (Space n) = 3*n := by
    simp [Space, Module.finrank_pi_fintype, finrank_euclideanSpace, Nat.mul_comm]
  simpa only [dim, jac, pow_mul] using integral_comp_smul_of_nonneg volume f b (hR := hb.le)

private theorem dilate_memLp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] {p : ENNReal} {f : E → F} (hf : MemLp f p) {b : ℝ} (hb : 0 < b) :
    MemLp (fun x => f (b • x)) p := by
  let e := (Homeomorph.smul ((isUnit_iff_ne_zero.mpr hb.ne').unit : ℝˣ) : E ≃ₜ E).toMeasurableEquiv
  apply e.memLp_map_measure_iff.mp
  change MemLp f p (Measure.map (fun x : E => b • x) volume)
  rw [map_addHaar_smul _ hb.ne']
  exact hf.smul_measure ENNReal.ofReal_ne_top

private theorem dilate_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {P : E → Prop} (h : ∀ᵐ x, P x) {b : ℝ} (hb : 0 < b) : ∀ᵐ x, P (b • x) := by
  exact (quasiMeasurePreserving_smul volume hb.ne').tendsto_ae h

private theorem coulomb_smul {n : ℕ} (x : Space n) {b : ℝ} (hb : 0 < b) :
    coulomb (b • x) = b⁻¹ * coulomb x := by
  simp only [coulomb, Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_of_nonneg hb.le,
    mul_inv_rev, Finset.mul_sum]
  simp only [mul_comm b⁻¹]

private theorem weak_dilate {n : ℕ} (ψ : Wave n) (s : Spins n) (i : Fin n) (j : Fin 3)
    {b : ℝ} (hb : 0 < b) (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, (fderiv ℝ f x (particleDirection i j)) • ψ.value s (b • x)) =
      -(∫ x, f x • (b • ψ.gradient s (b • x) i j)) := by
  let L : Space n →L[ℝ] Space n := b⁻¹ • ContinuousLinearMap.id ℝ _
  let g (y : Space n) := f (L y)
  let v := particleDirection i j
  have hg : ContDiff ℝ ∞ g := hf.comp L.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph
    (Homeomorph.smul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hb.ne')).unit : ℝˣ))
  have hg' (y : Space n) : fderiv ℝ g y v = b⁻¹ * fderiv ℝ f (b⁻¹ • y) v := by
    change (fderiv ℝ (f ∘ L) y) v = _
    rw [((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply]
    exact map_smul (fderiv ℝ f (L y)) b⁻¹ v
  have h₁ (x : Space n) : fderiv ℝ f x v • ψ.value s (b • x) =
      b • (fderiv ℝ g (b • x) v • ψ.value s (b • x)) := by
    rw [hg', inv_smul_smul₀ hb.ne', smul_smul, mul_inv_cancel_left₀ hb.ne']
  have h₂ (x : Space n) : f x • (b • ψ.gradient s (b • x) i j) =
      b • (g (b • x) • ψ.gradient s (b • x) i j) := by
    change _ = b • (f (b⁻¹ • b • x) • _)
    rw [inv_smul_smul₀ hb.ne', smul_comm]
  change (∫ x, fderiv ℝ f x v • ψ.value s (b • x)) = _
  have hw : (∫ y, fderiv ℝ g y v • ψ.value s y) = -(∫ y, g y • ψ.gradient s y i j) :=
    ψ.weak_gradient s i j g hg hgc
  simp only [h₁, h₂, integral_smul, sector_change (fun y => fderiv ℝ g y v • ψ.value s y) hb,
    sector_change (fun y => g y • ψ.gradient s y i j) hb, hw, smul_neg]

private theorem normalized_square {n : ℕ} (ψ : Wave n) (s : Spins n) {b : ℝ} (hb : 0 < b)
    (x : Space n) : ‖amp n b • ψ.value s (b • x)‖ ^ 2 = jac n b * ‖ψ.value s (b • x)‖^2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, amp_sq n hb]

private theorem pair_weight {n : ℕ} (ψ : Wave n) (s : Spins n) {b : ℝ} (hb : 0 < b) (x : Space n) :
    coulomb x * ‖amp n b • ψ.value s (b • x)‖^2 =
      (b * jac n b) * (coulomb (b • x) * ‖ψ.value s (b • x)‖^2) := by
  rw [coulomb_smul x hb, normalized_square ψ s hb]
  field_simp

def Wave.dilate {n : ℕ} (ψ : Wave n) (b : ℝ) (hb : 0 < b) : Wave n where
  value s x := amp n b • ψ.value s (b • x)
  gradient s x i j := amp n b • (b • ψ.gradient s (b • x) i j)
  antisymmetric π s := (dilate_ae (ψ.antisymmetric π s) hb).mono fun x hx => by
    change amp n b • ψ.value (s ∘ π) ((b • x) ∘ π) = _
    rw [hx, mul_smul_comm]
  square_integrable s := (dilate_memLp (ψ.square_integrable s) hb).const_smul (amp n b)
  normalized := by
    unfold sectorIntegral
    simp_rw [normalized_square ψ _ hb, integral_const_mul]
    have he (s : Spins n) := sector_change (fun x => ‖ψ.value s x‖^2) hb
    simp only [he, smul_eq_mul, mul_inv_cancel_left₀ (jac_pos n hb).ne']
    exact ψ.normalized
  gradient_L2 s i j := ((dilate_memLp (ψ.gradient_L2 s i j) hb).const_smul b).const_smul (amp n b)
  weak_gradient s i j f hf hc := by
    simp_rw [smul_comm _ (amp n b), integral_smul, weak_dilate ψ s i j hb f hf hc, smul_neg]
  interaction_integrable s := by
    simp_rw [pair_weight ψ s hb]
    exact ((ψ.interaction_integrable s).comp_smul hb.ne').const_mul _

@[simp] theorem Wave.kinetic_dilate {n : ℕ} (ψ : Wave n) {b : ℝ} (hb : 0 < b) :
    (ψ.dilate b hb).kinetic = b^2 * ψ.kinetic := by
  have h (s : Spins n) (x : Space n) (i : Fin n) (j : Fin 3) :
      ‖(ψ.dilate b hb).gradient s x i j‖^2 = (jac n b * b^2) * ‖ψ.gradient s (b • x) i j‖^2 := by
    simp only [dilate, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, amp_sq n hb, mul_assoc]
  unfold kinetic sectorIntegral
  simp only [h, ← Finset.mul_sum, integral_const_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [sector_change (fun x => ∑ i, ∑ j, ‖ψ.gradient s x i j‖^2) hb, smul_eq_mul]
  field_simp [(jac_pos n hb).ne']

@[simp] theorem Wave.interaction_dilate {n : ℕ} (ψ : Wave n) {b : ℝ} (hb : 0 < b) :
    (ψ.dilate b hb).interaction = b * ψ.interaction := by
  unfold interaction sectorIntegral
  simp only [dilate, pair_weight ψ _ hb, integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [sector_change (fun x => coulomb x * ‖ψ.value s x‖^2) hb, smul_eq_mul]
  field_simp [(jac_pos n hb).ne']

@[simp] theorem Wave.density_dilate {n : ℕ} (ψ : Wave (n+1)) {b : ℝ} (hb : 0 < b) (x : Position) :
    (ψ.dilate b hb).matrixDensity x = coordinateDensity b ψ.matrixDensity x := by
  have hcons (y : Space n) : b • (Fin.cons x y : Space (n+1)) = Fin.cons (α := fun _ => Position) (b • x) (b • y) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> rfl
  have h (s : Spins n) (i j : Fin 2) (y : Space n) :
      (ψ.dilate b hb).value (Fin.cons i s) (Fin.cons x y) *
        conj ((ψ.dilate b hb).value (Fin.cons j s) (Fin.cons x y)) =
      (jac (n+1) b : ℂ) * (ψ.value (Fin.cons i s) (Fin.cons (b • x) (b • y)) *
        conj (ψ.value (Fin.cons j s) (Fin.cons (b • x) (b • y)))) := by
    simp only [dilate, hcons, Complex.real_smul, map_mul, Complex.conj_ofReal]
    rw [← amp_sq (n+1) hb, Complex.ofReal_pow]
    ring
  ext i j
  change (ψ.dilate b hb).matrixDensity x i j = ((b^3 : ℝ) : ℂ) * ψ.matrixDensity (b • x) i j
  unfold Wave.matrixDensity
  simp only [h, integral_const_mul, Complex.ofReal_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [sector_change (fun y => ψ.value (Fin.cons i s) (Fin.cons (b • x) y) *
      conj (ψ.value (Fin.cons j s) (Fin.cons (b • x) y))) hb, Complex.real_smul]
  simp only [jac, pow_succ, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp [hb.ne']

private theorem wave_ext {n : ℕ} {u v : Wave n} (hv : u.value = v.value) (hg : u.gradient = v.gradient) : u = v := by
  cases u
  cases v
  congr

@[simp] theorem Wave.dilate_inverse {n : ℕ} (ψ : Wave n) {b : ℝ} (hb : 0 < b) :
    (ψ.dilate b hb).dilate b⁻¹ (inv_pos.mpr hb) = ψ := by
  have hA : amp n b ≠ 0 := (Real.sqrt_pos.mpr (jac_pos n hb)).ne'
  have hv : ((ψ.dilate b hb).dilate b⁻¹ (inv_pos.mpr hb)).value = ψ.value := by
    funext s x
    simp [dilate, amp_inv, hA, hb.ne']
  have hg : ((ψ.dilate b hb).dilate b⁻¹ (inv_pos.mpr hb)).gradient = ψ.gradient := by
    funext s x i j
    simp only [dilate, amp_inv, smul_inv_smul₀ hb.ne']
    rw [smul_comm b⁻¹ (amp n b), inv_smul_smul₀ hb.ne', inv_smul_smul₀ hA]
  exact wave_ext hv hg

def PureState.dilate (s : PureState) (b : ℝ) (hb : 0 < b) : PureState := match s with
  | .vacuum => .vacuum
  | .occupied ψ => .occupied (ψ.dilate b hb)

@[simp] theorem PureState.particles_dilate (s : PureState) {b : ℝ} (hb : 0 < b) :
    (s.dilate b hb).particles = s.particles := by cases s <;> rfl
@[simp] theorem PureState.kinetic_dilate (s : PureState) {b : ℝ} (hb : 0 < b) :
    (s.dilate b hb).kinetic = b^2 * s.kinetic := by cases s <;> simp [dilate, kinetic]
@[simp] theorem PureState.interaction_dilate (s : PureState) {b : ℝ} (hb : 0 < b) :
    (s.dilate b hb).interaction = b * s.interaction := by cases s <;> simp [dilate, interaction]
@[simp] theorem PureState.density_dilate (s : PureState) {b : ℝ} (hb : 0 < b) (x : Position) :
    (s.dilate b hb).matrixDensity x = coordinateDensity b s.matrixDensity x := by
  cases s with
  | vacuum => simp [dilate, matrixDensity, coordinateDensity]
  | occupied ψ => exact ψ.density_dilate hb x
@[simp] theorem PureState.dilate_inverse (s : PureState) {b : ℝ} (hb : 0 < b) :
    (s.dilate b hb).dilate b⁻¹ (inv_pos.mpr hb) = s := by cases s <;> simp [dilate]

def MixedState.dilate (Γ : MixedState) (b : ℝ) (hb : 0 < b) : MixedState where
  component k := (Γ.component k).dilate b hb
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := by simpa using Γ.particles_summable
  kinetic_summable := by simpa [mul_left_comm (Γ.weight _)] using Γ.kinetic_summable.mul_left (b^2)
  interaction_summable := by simpa [mul_left_comm (Γ.weight _)] using Γ.interaction_summable.mul_left b
  density_summable := by
    filter_upwards [dilate_ae Γ.density_summable hb] with x hx
    intro i j
    simpa only [PureState.density_dilate, coordinateDensity, Matrix.smul_apply, Complex.real_smul,
      mul_left_comm (Γ.weight _ : ℂ)] using (hx i j).mul_left ((b^3 : ℝ) : ℂ)

@[simp] theorem MixedState.kinetic_dilate (Γ : MixedState) {b : ℝ} (hb : 0 < b) :
    (Γ.dilate b hb).kinetic = b^2 * Γ.kinetic := by
  simp [kinetic, dilate, mul_left_comm (Γ.weight _), tsum_mul_left]
@[simp] theorem MixedState.interaction_dilate (Γ : MixedState) {b : ℝ} (hb : 0 < b) :
    (Γ.dilate b hb).interaction = b * Γ.interaction := by
  simp [interaction, dilate, mul_left_comm (Γ.weight _), tsum_mul_left]
@[simp] theorem MixedState.density_dilate (Γ : MixedState) {b : ℝ} (hb : 0 < b) (x : Position) :
    (Γ.dilate b hb).matrixDensity x = coordinateDensity b Γ.matrixDensity x := by
  ext i j
  simp only [matrixDensity, dilate, PureState.density_dilate, coordinateDensity, Matrix.smul_apply,
    Complex.real_smul, mul_left_comm (Γ.weight _ : ℂ), tsum_mul_left]

@[simp] theorem MixedState.dilate_inverse (Γ : MixedState) {b : ℝ} (hb : 0 < b) :
    (Γ.dilate b hb).dilate b⁻¹ (inv_pos.mpr hb) = Γ := by
  cases Γ
  simp [dilate]

private theorem hartree_dilate (ρ : Position → ℝ) {b : ℝ} (hb : 0 < b) :
    hartree (fun x => b^3 * ρ (b • x)) = b * hartree ρ := by
  let K (x y : Position) := ρ x * ρ y / ‖x-y‖
  have he (x y : Position) : b^3 * ρ (b • x) * (b^3 * ρ (b • y)) / ‖x-y‖ = b^7 * K (b • x) (b • y) := by
    dsimp [K]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hb.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp [hb.ne']
  unfold hartree
  simp_rw [he, integral_const_mul]
  have change_pos (f : Position → ℝ) : (∫ x, f (b • x)) = (b^3)⁻¹ * ∫ y, f y := by
    simpa only [smul_eq_mul, finrank_euclideanSpace, Fintype.card_fin] using
      integral_comp_smul_of_nonneg volume f b (hR := hb.le)
  simp_rw [change_pos (K (b • _)), integral_const_mul, change_pos (fun x => ∫ y, K x y)]
  dsimp only [K]
  field_simp

private theorem feasible_dilate {M : Position → SpinMatrix} {Γ : MixedState} (h : feasible M Γ)
    {b : ℝ} (hb : 0 < b) : feasible (coordinateDensity b M) (Γ.dilate b hb) :=
  (dilate_ae h hb).mono fun x hx => by simp [coordinateDensity, hx]

private theorem coordinate_inverse (M : Position → SpinMatrix) {b : ℝ} (hb : 0 < b) :
    coordinateDensity b⁻¹ (coordinateDensity b M) = M := by
  funext x
  simp [coordinateDensity, hb.ne', smul_smul]

/-- Coordinate dilation is an invertible map of the actual constrained
ensembles. The inverse dilates by the reciprocal factor. -/
def coulombStateDilation (M : Position → SpinMatrix) (b : ℝ) (hb : 0 < b) : StateDilation b M where
  states := {
    toFun := fun s => ⟨s.val.dilate b hb, feasible_dilate s.property hb⟩
    invFun := fun s => ⟨s.val.dilate b⁻¹ (inv_pos.mpr hb), by
      simpa only [coordinate_inverse M hb] using feasible_dilate s.property (inv_pos.mpr hb)⟩
    left_inv := fun s => Subtype.ext (s.val.dilate_inverse hb)
    right_inv := fun s => Subtype.ext (by simpa only [inv_inv] using s.val.dilate_inverse (inv_pos.mpr hb)) }
  kinetic s := s.val.kinetic_dilate hb
  indirect s := by
    change indirectAt (coordinateDensity b M) (s.val.dilate b hb) = b * indirectAt M s.val
    simp only [indirectAt, coordinateDensity, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul,
      hartree_dilate (fun x => (M x).trace.re) hb, MixedState.interaction_dilate]
    ring

theorem coulomb_coordinate_dilation : CoordinateDilationLaw :=
  fun b hb M => ⟨coulombStateDilation M b hb⟩

end TSGA.ManyBody
