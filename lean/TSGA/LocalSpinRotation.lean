import TSGA.LocalRotationWave
import TSGA.LocalRotationMixture
import TSGA.LocalScalarMarginalProof

/-! # Spatial spin rotations of concrete mixed Coulomb states -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped MatrixOrder ComplexOrder

/-- The kinetic construction needs only the local Sobolev product rule. The
weighted scalar marginal follows from Fubini and antisymmetry. -/
theorem LocalSpinCalculus.of_leibniz (h : LocalSectorLeibniz) : LocalSpinCalculus :=
  ⟨localScalarMarginal,h⟩

private def trivialChange (p : PureState) (b : ℝ) (U : Position → unitary SpinMatrix)
    (h : ∀ᵐ x, b • p.matrixDensity x = (U x : SpinMatrix)*(b • p.matrixDensity x)*star (U x : SpinMatrix)) :
    LocalComponentChange p b U where
  rotated := p
  particles := rfl
  interaction := rfl
  density := h
  cross := 0
  extra := 0
  extra_nonneg := le_rfl
  polar t := by simpa only [mul_zero,add_zero] using p.kinetic_nonneg
  kinetic := by simp

/-- Lemma 4.13 at the level of states. Each occupied pure component with
positive spectral weight is multiplied by the tensor product of U at its
particle positions. Its differentiated factors are controlled by the given
one-particle quadratic form; the same construction applies to U*. -/
theorem LocalSpinCalculus.rotationLaw (C : LocalSpinCalculus) {D : Density} {O : Set Position}
    {U : Position → unitary SpinMatrix} {H : MatrixGradient} {w : Position → ℝ}
    (hO : LocalRotationDomain D O) (hU : LocalUnitaryMeasurable U)
    (hH : IsMatrixGradientOn O (fun x => (U x : SpinMatrix)) H)
    (hw : AEMeasurable w volume) (hw0 : ∀ x, 0 ≤ w x)
    (hB : ∀ᵐ x ∂volume.restrict O, (∑ j, star (H x j)*H x j) ≤ (w x : ℂ) • (1 : SpinMatrix))
    (hI : Integrable (fun x => D.charge x * w x)) : RotationLaw D U (∫ x, D.charge x*w x) := by
  classical
  intro Γ hΓ
  obtain ⟨hfin,hs⟩ := C.marginal Γ D hΓ w hw hw0 hI
  have each (k : ℕ) : ∃ R : LocalComponentChange (Γ.component k) (Γ.weight k) U,
      R.extra ≤ (Γ.component k).localMass w := by
    by_cases hz : Γ.weight k = 0
    · let R := trivialChange (Γ.component k) (Γ.weight k) U (by simp [hz])
      exact ⟨R,(Γ.component k).localMass_nonneg hw0⟩
    have hk := lt_of_le_of_ne (Γ.weight_nonneg k) (Ne.symm hz)
    have hm := hfin k hk
    have hloc := C.marginal.localized hΓ k hk
    generalize he : Γ.component k = p at hm hloc ⊢
    cases p with
    | vacuum => exact ⟨trivialChange .vacuum _ _ (by simp [PureState.matrixDensity]),le_rfl⟩
    | occupied ψ =>
      obtain ⟨χ,g,j,hval,hV,hg,hgw,hpol,hK⟩ := C.leibniz.wave hO hU hH hw0 hB ψ hloc hm
      have hd := ψ.localUnitary_matrixDensity χ U hval
      refine ⟨⟨.occupied χ,rfl,hV,?_,g,j,hg,hpol,hK⟩,hgw⟩
      filter_upwards [hd] with x hx
      simp only [PureState.matrixDensity,hx,Matrix.mul_smul,Matrix.smul_mul]
  choose R hR using each
  have bound k := mul_le_mul_of_nonneg_left (hR k) (Γ.weight_nonneg k)
  have hg := hs.summable.of_nonneg_of_le (fun k => mul_nonneg (Γ.weight_nonneg k) (R k).extra_nonneg) bound
  obtain ⟨Δ,hd,hV,rest⟩ := Γ.localRotation_of_components R hg ((hg.tsum_le_tsum bound hs.summable).trans_eq hs.tsum_eq)
  exact ⟨Δ,hd.trans (hΓ.mono fun x hx => by simp [conjugatedDensity,hx]),hV,rest⟩

end TSGA.ManyBody
