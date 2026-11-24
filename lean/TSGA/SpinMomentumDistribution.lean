import TSGA.EnsembleTwist
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integrated kinetic and axial-current tests of spin momentum distributions -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Weight a spin density in momentum space by a real multiplier. -/
def momentumMoment (w : Position → ℝ) (P : Position → SpinMatrix) : SpinMatrix :=
  ∫ p, w p • P p

def momentumKinetic (P : Position → SpinMatrix) : SpinMatrix :=
  momentumMoment (fun p => ‖p‖^2) P

/-- The integrated momentum tested by the third Pauli matrix. -/
def axialTest (M : SpinMatrix) : ℝ := (M 0 0).re - (M 1 1).re

def momentumAxial (q : Position) (P : Position → SpinMatrix) : ℝ :=
  axialTest (momentumMoment (fun p => ⟪q,p⟫_ℝ) P)

/-- Position and momentum marginals of the one-body reduced density matrix,
in the physical momentum convention. -/
structure SpinMomentumDistribution (Γ : MixedState) where
  profile : Position → SpinMatrix
  positive : ∀ᵐ p, (profile p).PosSemidef
  integrable : Integrable profile
  second_integrable : Integrable (fun p => ‖p‖^2 • profile p)
  spatial_integrable : Integrable Γ.matrixDensity
  mass : (∫ p, profile p) = ∫ x, Γ.matrixDensity x
  kinetic : (momentumKinetic profile).trace.re = Γ.kinetic
  current : ∀ q, ⟪q,Γ.axialCurrent⟫_ℝ = momentumAxial q profile

private def sand (X Y : SpinMatrix) : SpinMatrix →L[ℝ] SpinMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => X*M*star Y
    map_add' := fun a b => by simp [mul_add,add_mul]
    map_smul' := fun r a => by simp }

def spinRealTrace : SpinMatrix →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun := fun M => M.trace.re
  map_add' := fun a b => by simp [Matrix.trace_add]
  map_smul' := fun r a => by simp [Matrix.trace_smul,Complex.real_smul] }

def spinAxialCLM : SpinMatrix →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun := axialTest
  map_add' := fun a b => by simp [axialTest]; ring
  map_smul' := fun r a => by simp [axialTest,Complex.real_smul]; ring }

private theorem axialTest_star (M : SpinMatrix) : axialTest (star M) = axialTest M := by
  simp [axialTest,Matrix.star_apply]

private theorem sandwich_symm {P : SpinMatrix} (h : P.IsHermitian) (X Y : SpinMatrix) :
    axialTest (X*P*star Y) = axialTest (Y*P*star X) := by
  rw [← axialTest_star (Y*P*star X)]
  simp [star_mul,show star P = P from h.eq, mul_assoc]

private def polarized (P : SpinMatrix) : SpinMatrix →ₗ[ℝ] SpinMatrix →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => axialTest (X*P*star Y))
    (fun a b y => by simp only [add_mul]; exact spinAxialCLM.map_add _ _)
    (fun r a y => by simp only [Matrix.smul_mul]; exact spinAxialCLM.map_smul _ _)
    (fun x a b => by simp only [star_add,mul_add]; exact spinAxialCLM.map_add _ _)
    (fun r x y => by simp only [star_smul,star_trivial,Matrix.mul_smul]; exact spinAxialCLM.map_smul _ _)

theorem spinFirst_norm_bound (P : Position → SpinMatrix) (q p : Position) :
    ‖⟪q,p⟫_ℝ • P p‖ ≤ ‖q‖ * (‖P p‖ + ‖‖p‖^2 • P p‖) := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖p‖)]
  have hp : ‖p‖ ≤ 1+‖p‖^2 := by nlinarith [sq_nonneg (‖p‖-1)]
  have h₀ := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm q p) (norm_nonneg (P p))
  have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (norm_nonneg q)) (norm_nonneg (P p))
  linarith only [h₀,h₁]

theorem spinFirst_integrable {P : Position → SpinMatrix} (h : Integrable P)
    (h₂ : Integrable (fun p => ‖p‖^2 • P p)) (q : Position) :
    Integrable (fun p => ⟪q,p⟫_ℝ • P p) :=
  ((h.norm.add h₂.norm).const_mul ‖q‖).mono'
    ((by fun_prop : Continuous (fun p : Position => ⟪q,p⟫_ℝ)).aestronglyMeasurable.smul h.1)
    (ae_of_all _ (spinFirst_norm_bound P q))

namespace SpinMomentumDistribution
variable {Γ : MixedState} (D : SpinMomentumDistribution Γ)

def form (q : Position) : SpinMatrix →ₗ[ℝ] SpinMatrix →ₗ[ℝ] ℝ :=
  polarized (momentumMoment (fun p => ⟪q,p⟫_ℝ) D.profile)

theorem first_integrable (q : Position) : Integrable (fun p => ⟪q,p⟫_ℝ • D.profile p) :=
  spinFirst_integrable D.integrable D.second_integrable q

theorem kinetic_pos : (momentumKinetic D.profile).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg_of_ae
  filter_upwards [D.positive] with p hp
  exact smul_nonneg (sq_nonneg _) hp.nonneg

private def spinAdjoint : SpinMatrix →L[ℝ] SpinMatrix := LinearMap.toContinuousLinearMap {
  toFun := star
  map_add' := star_add
  map_smul' := fun r a => by simp }

private theorem hermitian_first (q : Position) :
    (momentumMoment (fun p => ⟪q,p⟫_ℝ) D.profile).IsHermitian := by
  change spinAdjoint (∫ p, ⟪q,p⟫_ℝ • D.profile p) = _
  rw [← spinAdjoint.integral_comp_comm (D.first_integrable q)]
  apply integral_congr_ae
  filter_upwards [D.positive] with p hp
  change star (⟪q,p⟫_ℝ • D.profile p) = _
  simp [star_smul,show star (D.profile p) = _ from hp.isHermitian.eq]

theorem form_symm (q : Position) (X Y : SpinMatrix) : D.form q X Y = D.form q Y X :=
  sandwich_symm (D.hermitian_first q) X Y

theorem axial_identity (q : Position) : ⟪q,Γ.axialCurrent⟫_ℝ = D.form q 1 1 := by
  rw [D.current]
  change axialTest _ = axialTest (1 * _ * star (1 : SpinMatrix))
  simp

private theorem tr_sand (X P : SpinMatrix) : (X*P*star X).trace.re = ((star X*X)*P).trace.re := by
  rw [Matrix.trace_mul_cycle]

/-- Localization of the one-particle Fourier density identifies the
full kinetic energy of the localized mixed state. -/
theorem kinetic_localize {Λ : MixedState} (E : SpinMomentumDistribution Λ) (S : SpinMatrix)
    (hp : E.profile =ᵐ[volume] fun p => S * D.profile p * star S) :
    Λ.kinetic = ((star S*S)*momentumKinetic D.profile).trace.re := by
  rw [← E.kinetic, ← tr_sand]
  apply congrArg (fun M : SpinMatrix => M.trace.re)
  change (∫ p, ‖p‖^2 • E.profile p) = sand S S (∫ p, ‖p‖^2 • D.profile p)
  rw [← (sand S S).integral_comp_comm D.second_integrable]
  apply integral_congr_ae
  filter_upwards [hp] with p h
  rw [map_smul,h]
  rfl

theorem current_localize {Λ : MixedState} (E : SpinMomentumDistribution Λ) (S : SpinMatrix)
    (hp : E.profile =ᵐ[volume] fun p => S * D.profile p * star S) (q : Position) :
    ⟪q,Λ.axialCurrent⟫_ℝ = D.form q S S := by
  rw [E.current]
  change axialTest (∫ p, ⟪q,p⟫_ℝ • E.profile p) = axialTest (sand S S (∫ p, ⟪q,p⟫_ℝ • D.profile p))
  congr 1
  rw [← (sand S S).integral_comp_comm (D.first_integrable q)]
  apply integral_congr_ae
  filter_upwards [hp] with p h
  rw [map_smul,h]
  rfl

private theorem row_symm {P : SpinMatrix} (h : P.IsHermitian) (X Y : SpinMatrix) (i : Fin 2) :
    ((X*P*star Y) i i).re = ((Y*P*star X) i i).re := by
  have eqn : star (Y*P*star X) = X*P*star Y := by
    simp [star_mul,show star P = P from h.eq,mul_assoc]
  rw [← eqn]
  simp [Matrix.star_apply]

private theorem row_square {P : SpinMatrix} (hp : P.PosSemidef) (X Y : SpinMatrix)
    (i : Fin 2) (t b : ℝ) :
    0 ≤ ((X*P*star X) i i).re*t^2 + 2*((X*P*star Y) i i).re*(t*b) +
      ((Y*P*star Y) i i).re*b^2 := by
  have h := (RCLike.nonneg_iff.mp ((hp.mul_mul_conjTranspose_same (t • X+b • Y)).diag_nonneg (i := i))).1
  change 0 ≤ (((t • X+b • Y)*P*star (t • X+b • Y)) i i).re at h
  simp only [star_add,star_smul,star_trivial,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,Complex.re_ofReal_mul,Complex.add_re] at h
  rw [row_symm hp.isHermitian Y X i] at h
  nlinarith only [h]

private theorem momentum_gram_point {P : SpinMatrix} (hp : P.PosSemidef) (q p : Position)
    (X Y : SpinMatrix) (t : ℝ) :
    0 ≤ (X*P*star X).trace.re*(t*t) + (2*(⟪q,p⟫_ℝ*axialTest (X*P*star Y)))*t +
      ‖q‖^2 * (‖p‖^2 * (Y*P*star Y).trace.re) := by
  have a := row_square hp X Y 0 t ⟪q,p⟫_ℝ
  have b := row_square hp X Y 1 t (-⟪q,p⟫_ℝ)
  have c : ⟪q,p⟫_ℝ^2 ≤ ‖q‖^2*‖p‖^2 := by
    simpa [sq_abs,mul_pow] using
      (pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm q p) 2)
  have d := (RCLike.nonneg_iff.mp (hp.mul_mul_conjTranspose_same Y).trace_nonneg).1
  change 0 ≤ (Y*P*star Y).trace.re at d
  have e := mul_nonneg (sub_nonneg.mpr c) d
  simp only [axialTest,Matrix.trace_fin_two,Complex.add_re] at e ⊢
  linarith only [a,b,e]

/-- The polarized current estimate for distinct spin tests of the
wavefunction and of its derivative. -/
theorem gram (q : Position) (X Y : SpinMatrix) (t : ℝ) : 0 ≤
    (∫ x, (X * Γ.matrixDensity x * star X).trace.re) * (t*t) +
    (2 * D.form q X Y)*t + ‖q‖^2 * ((star Y * Y) * momentumKinetic D.profile).trace.re := by
  let U := spinRealTrace.comp (sand X X)
  let V := spinAxialCLM.comp (sand X Y)
  let W := spinRealTrace.comp (sand Y Y)
  let a (p : Position) := U (D.profile p)
  let b (p : Position) := V (⟪q,p⟫_ℝ • D.profile p)
  let c (p : Position) := W (‖p‖^2 • D.profile p)
  have ha : Integrable a := U.integrable_comp D.integrable
  have hb : Integrable b := V.integrable_comp (D.first_integrable q)
  have hc : Integrable c := W.integrable_comp D.second_integrable
  have hp : 0 ≤ ∫ p, a p*(t*t)+(2*b p)*t+‖q‖^2*c p := by
    apply integral_nonneg_of_ae
    filter_upwards [D.positive] with p h
    dsimp only [a,b,c]
    rw [V.map_smul,W.map_smul]
    exact momentum_gram_point h q p X Y t
  have hab : Integrable (fun p => a p*(t*t)+(2*b p)*t) := (ha.mul_const _).add ((hb.const_mul _).mul_const _)
  rw [integral_add hab (hc.const_mul (‖q‖^2)),
    integral_add (ha.mul_const (t*t)) ((hb.const_mul 2).mul_const t),integral_mul_const,
    integral_mul_const,integral_const_mul,integral_const_mul] at hp
  have mass_eq : (∫ x, (X*Γ.matrixDensity x*star X).trace.re) = ∫ p, a p := by
    change (∫ x, U (Γ.matrixDensity x)) = ∫ p, U (D.profile p)
    rw [U.integral_comp_comm D.spatial_integrable,U.integral_comp_comm D.integrable,D.mass]
  have b_eq : (∫ p, b p) = D.form q X Y := V.integral_comp_comm (D.first_integrable q)
  have c_eq : (∫ p, c p) = ((star Y*Y)*momentumKinetic D.profile).trace.re :=
    (W.integral_comp_comm D.second_integrable).trans (tr_sand Y _)
  rwa [mass_eq,← b_eq,← c_eq]

end SpinMomentumDistribution
end TSGA.ManyBody
