import TSGA.EnsembleTwist
import TSGA.OrderedGas
import TSGA.CoulombGas
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Axial rotations and spin localization for Coulomb ensembles

Opposite plane waves on the two spins give the density rotation and kinetic
identity for each mixed state. Geometric localization of the reduced spin
observables then yields the ordered frame for any cutoff of positive mass.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization
open scoped InnerProductSpace MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

/-- The spin-dependent momenta of the axial SU(2) rotation. -/
def axialShift (q : Position) (a : Fin 2) : Position :=
  (if a = 0 then -(1/2 : ℝ) else 1/2) • q

theorem axialShift_neg (q : Position) : axialShift (-q) = -axialShift q := by
  funext a
  simp [axialShift]

theorem MixedState.density_axialShift (Γ : MixedState) (q x : Position) :
    (Γ.twist (axialShift q)).matrixDensity x = rotate ⟪q,x⟫_ℝ (Γ.matrixDensity x) := by
  ext i j
  rw [Γ.density_twist, rotate_by_entry]
  simp only [axialShift, real_inner_smul_left, axialWeight, sub_mul]

theorem MixedState.kinetic_axialShift (Γ : MixedState) (q : Position) :
    (Γ.twist (axialShift q)).kinetic = Γ.kinetic - ⟪q,Γ.axialCurrent⟫_ℝ +
      ‖q‖^2 / 4 * (Γ.spinNumber 0 + Γ.spinNumber 1) := by
  rw [Γ.kinetic_twist, Fin.sum_univ_two]
  norm_num [axialShift, MixedState.axialCurrent, real_inner_smul_left, inner_sub_right, norm_smul]
  ring

/-- Apply the axial spin spiral to an arbitrary spin-density field. -/
def axialSpiral (F : Position → SpinMatrix) (q x : Position) : SpinMatrix :=
  rotate ⟪q,x⟫_ℝ (F x)

@[simp] theorem axialSpiral_zero (F : Position → SpinMatrix) : axialSpiral F 0 = F := by
  funext x
  simp [axialSpiral]

/-- Axial plane waves identify all admissible states before and after rotation. -/
def MixedState.axialRotationEquiv (F : Position → SpinMatrix) (q : Position) :
    {Γ // feasible F Γ} ≃ {Γ // feasible (axialSpiral F q) Γ} where
  toFun s := ⟨s.val.twist (axialShift q), s.property.mono fun x hx => by
    rw [s.val.density_axialShift, hx]
    rfl⟩
  invFun s := ⟨s.val.twist (axialShift (-q)), s.property.mono fun x hx => by
    rw [s.val.density_axialShift, hx]
    simp [axialSpiral, ← rotate_add]⟩
  left_inv s := Subtype.ext (by
    change (s.val.twist (axialShift q)).twist (axialShift (-q)) = _
    simp [MixedState.twist_add, axialShift_neg])
  right_inv s := Subtype.ext (by
    change (s.val.twist (axialShift (-q))).twist (axialShift q) = _
    simp [MixedState.twist_add, axialShift_neg])

/-- Rotation between the density constraints of a flat cutoff and its spiral. -/
def cutoffRotation (f : Position → ℝ) (A : SpinMatrix) (q : Position) :
    CutoffState f A ≃ RotatingCutoffState f A q :=
  (MixedState.axialRotationEquiv (fun x => (f x : ℂ) • A) q).trans
    (Equiv.subtypeEquivRight fun Γ => by
      rw [show axialSpiral (fun x => (f x : ℂ) • A) q = cutoffSpiral f A q from
        funext fun x => rotate_smul _ _ _])

private theorem cutoff_spinNumber_sum (f : Position → ℝ) (A : SpinMatrix) (s : CutoffState f A) :
    s.val.spinNumber 0 + s.val.spinNumber 1 = A.trace.re * (∫ x, f x) := by
  have hd : feasible (fun x => (f x : ℂ) • A) s.val := s.property
  rw [s.val.spinNumber_of_cutoff hd, s.val.spinNumber_of_cutoff hd, Matrix.trace_fin_two, Complex.add_re, add_mul]

theorem cutoffRotation_kinetic (f : Position → ℝ) (A : SpinMatrix) (q : Position) (s : CutoffState f A) :
    (cutoffRotation f A q s).val.kinetic = s.val.kinetic - ⟪q,s.val.axialCurrent⟫_ℝ +
      ‖q‖^2/4 * (A.trace.re * ∫ x, f x) := by
  change (s.val.twist (axialShift q)).kinetic = _
  rw [s.val.kinetic_axialShift, cutoff_spinNumber_sum]

private def flatSpiralState (D : DomainSequence) (A : SpinMatrix) (n : ℕ) :
    SpiralState D A n 0 ≃ CutoffState (D.cutoff n) A :=
  Equiv.subtypeEquivRight fun Γ => by
    rw [show D.spiralField A n 0 = (fun x => D.cutoff n x • A) from
      funext fun x => cutoffSpiral_zero_wavevector _ _ x]

def spiralRotation (D : DomainSequence) (A : SpinMatrix) (n : ℕ) (q : Position) :
    SpiralState D A n 0 ≃ SpiralState D A n q :=
  (flatSpiralState D A n).trans (cutoffRotation (D.cutoff n) A q)

theorem spiralRotation_value (D : DomainSequence) (A : SpinMatrix) (n : ℕ) (q : Position)
    (s : SpiralState D A n 0) :
    (spiralRotation D A n q s).value = s.value - ⟪q,s.val.axialCurrent⟫_ℝ +
      ‖q‖^2/4 * (A.trace.re * D.vol n) := by
  have hk := cutoffRotation_kinetic (D.cutoff n) A q (flatSpiralState D A n s)
  change (s.val.twist (axialShift q)).kinetic = s.val.kinetic - ⟪q,s.val.axialCurrent⟫_ℝ + _ at hk
  rw [D.cutoff_mass] at hk
  simp only [SpiralState.value, DomainSequence.spiralField, cutoffSpiral, Matrix.trace_smul, trace_rotate]
  change (s.val.twist (axialShift q)).kinetic + (s.val.twist (axialShift q)).interaction - _ = _
  rw [hk, s.val.interaction_twist]
  ring

/-- Constant spin tests of the reduced one- and two-particle observables.
The quadratic inequality is the positivity of the squared norm of a linear
combination of a spin-tested orbital and its directional derivative. The
localization identities include the physical axial current of the output. -/
structure FockSpinCurrentData (Γ : MixedState) (q : Position) where
  kinetic : SpinMatrix
  pair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  kinetic_pos : kinetic.PosSemidef
  pair_pos : pair.PosSemidef
  kinetic_trace : kinetic.trace.re = Γ.kinetic
  pair_trace : pair.trace.re = Γ.interaction
  form : SpinMatrix →ₗ[ℝ] SpinMatrix →ₗ[ℝ] ℝ
  symm : ∀ X Y, form X Y = form Y X
  current : ⟪q,Γ.axialCurrent⟫_ℝ = form 1 1
  gram : ∀ (X Y : SpinMatrix) (t : ℝ), 0 ≤
    (∫ x, (X * Γ.matrixDensity x * star X).trace.re) * (t*t) +
      (2 * form X Y)*t + ‖q‖^2 * ((star Y * Y) * kinetic).trace.re
  localize : ∀ S : SpinMatrix, star S * S ≤ 1 → ∃ Λ : MixedState,
    feasible (fun x => S * Γ.matrixDensity x * star S) Λ ∧
    Λ.kinetic = ((star S * S) * kinetic).trace.re ∧
    Λ.interaction = (((star S * S) ⊗ₖ (star S * S)) * pair).trace.re ∧
    ⟪q,Λ.axialCurrent⟫_ℝ = form S S

def FockSpinCurrentTraces : Prop :=
  ∀ (Γ : MixedState) (q : Position), Nonempty (FockSpinCurrentData Γ q)

theorem FockSpinCurrentTraces.toFockSpinLocalization (red : FockSpinCurrentTraces) :
    FockSpinLocalization := by
  intro Γ
  obtain ⟨H⟩ := red Γ 0
  refine ⟨H.kinetic,H.pair,H.kinetic_pos,H.pair_pos,H.kinetic_trace,H.pair_trace,?_⟩
  intro S hS
  obtain ⟨Λ,hd,hk,hw,_⟩ := H.localize S hS
  exact ⟨Λ,hd,hk,hw⟩

private theorem cutoff_spin_trace {f : Position → ℝ} {A : SpinMatrix} (hA : A.PosSemidef)
    (s : CutoffState f A) (X : SpinMatrix) :
    (∫ x, (X * s.val.matrixDensity x * star X).trace.re) =
      hilbertSchmidt (X * CFC.sqrt A)^2 * ∫ x, f x := by
  have hhs : hilbertSchmidt (X * CFC.sqrt A)^2 = (X*A*star X).trace.re := by
    rw [hilbertSchmidt, Real.sq_sqrt (by positivity), hs_trace, star_mul, (CFC.sqrt_nonneg A).star_eq]
    congr 2
    calc
      (X * CFC.sqrt A) * (CFC.sqrt A * star X) = X * (CFC.sqrt A * CFC.sqrt A) * star X := by
        simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self A hA.nonneg]
  rw [hhs, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [s.property] with x hx
  simp only [hx, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul,
    Complex.re_ofReal_mul, mul_comm]

private theorem reduced_cauchy {f : Position → ℝ} {A : SpinMatrix} {V : ℝ} {q : Position}
    (hA : A.PosSemidef) (s : CutoffState f A) (H : FockSpinCurrentData s.val q)
    (hV : 0 < V) (hm : ∫ x, f x = V) (X Y : SpinMatrix) (hY : star Y * Y ≤ 1) :
    (V⁻¹ * H.form X Y)^2 ≤ ‖q‖^2 * hilbertSchmidt (X * CFC.sqrt A)^2 * (s.val.kinetic/V) := by
  have hg := discrim_le_zero (H.gram X Y)
  rw [discrim, cutoff_spin_trace hA, hm] at hg
  have htrace := trace_product_nonneg (Matrix.le_iff.mp hY) H.kinetic_pos
  simp only [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, H.kinetic_trace] at htrace
  have hupper := mul_le_mul_of_nonneg_left (sub_nonneg.mp htrace)
    (show 0 ≤ (hilbertSchmidt (X * CFC.sqrt A)^2 * V) * ‖q‖^2 by positivity)
  rw [inv_mul_eq_div]
  field_simp [hV.ne']
  nlinarith only [hg,hupper]

/-- The physical axial rotation and the unnormalized reduced observables give
all ordered-frame laws for a cutoff of mass V. -/
def orderedSpiralFrame_of_reduced (red : FockSpinCurrentTraces) (f : Position → ℝ)
    {V : ℝ} (hV : 0 < V) (hm : ∫ x, f x = V) (q : Position) : OrderedSpiralFrame f V q where
  current Γ := ⟪q,Γ.axialCurrent⟫_ℝ / V
  rotate := fun A => cutoffRotation f A q
  coulomb := fun _ s => s.val.interaction_twist _
  kinetic := by
    intro A s
    rw [cutoffRotation_kinetic, hm]
    field_simp [hV.ne']
  reduced := by
    intro A hA s
    obtain ⟨H⟩ := red s.val q
    let P : SpinCurrentPairing A q (s.val.kinetic/V) :=
      { form := V⁻¹ • H.form
        symm := fun X Y => by change V⁻¹ * H.form X Y = V⁻¹ * H.form Y X; rw [H.symm]
        cauchy := reduced_cauchy hA s H hV hm }
    refine ⟨P,H.kinetic,H.pair,?_,H.kinetic_pos,H.pair_pos,H.kinetic_trace,H.pair_trace,?_⟩
    · change ⟪q,s.val.axialCurrent⟫_ℝ / V = V⁻¹ * H.form 1 1
      rw [H.current, inv_mul_eq_div]
    · intro S hS
      obtain ⟨Λ,hΛ,hk,hw,hj⟩ := H.localize S hS
      have hd : feasible (fun x => f x • (S * A * star S)) Λ := by
        filter_upwards [hΛ,s.property] with x h₁ h₂
        simp only [h₁,h₂,Matrix.mul_smul,Matrix.smul_mul]
      refine ⟨⟨Λ,hd⟩,hk,hw,?_⟩
      change ⟪q,Λ.axialCurrent⟫_ℝ / V = V⁻¹ * H.form S S
      rw [hj, inv_mul_eq_div]

theorem ordered_tetrahedral_frames (red : FockSpinCurrentTraces) (η : Mollifier)
    {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (q : Position) :
    Nonempty (OrderedSpiralFrame (smoothedIndicator (tetrahedron ℓ) η δ)
      (regionVolume (tetrahedron ℓ)) q) :=
  ⟨orderedSpiralFrame_of_reduced red _ (tetrahedron_volume_pos hℓ) (tile_cutoff_mass η hℓ hδ) q⟩

end TSGA.ManyBody
