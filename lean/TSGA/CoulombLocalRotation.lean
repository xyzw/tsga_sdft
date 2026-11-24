import TSGA.LocalSpinRotation
import TSGA.PhysicalTSGA
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Lemma 4.13 for concrete Coulomb states -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The squared spin gradient in Lemma 4.13 uses the operator norm of the sum
of the three positive matrices. -/
def localSpinSpeed (H : MatrixGradient) (x : Position) : ℝ := ‖∑ j, star (H x j)*H x j‖

private theorem localSpinSpeed_majorizes (H : MatrixGradient) (x : Position) :
    (∑ j, star (H x j)*H x j) ≤ (localSpinSpeed H x : ℂ) • (1 : SpinMatrix) := by
  let G := ∑ j, star (H x j) * H x j
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => star_mul_self_nonneg _
  have h := IsSelfAdjoint.le_algebraMap_norm_self G (IsSelfAdjoint.of_nonneg hG)
  rw [Algebra.algebraMap_eq_smul_one] at h
  exact h

/-- Apply the weak tensor-product rotation to every feasible mixed state.
Taking the infimum gives the sharp operator-norm energy estimate, and rotating
one feasible state gives a representative of the new density. -/
theorem coulomb_local_spin_rotation (leibniz : LocalSectorLeibniz) (F : FiniteEnergyInputs)
    {D : Density} {U : Position → unitary SpinMatrix} {O : Set Position} {H S : MatrixGradient}
    (hD : SqrtRegular D S) (domain : LocalRotationDomain D O)
    (meas : ∀ i j, AEMeasurable (fun x => (U x : SpinMatrix) i j) volume)
    (weak : IsMatrixGradientOn O (fun x => (U x : SpinMatrix)) H)
    (finite : Integrable (fun x => D.charge x * localSpinSpeed H x)) :
    let W := ∫ x, D.charge x * localSpinSpeed H x
    let B := conjugatedDensity D U
    (∃ Γ, feasible B.matrix Γ) ∧
    (∀ Γ, feasible D.matrix Γ → ∃ Λ, feasible B.matrix Λ ∧ Λ.interaction = Γ.interaction ∧
      ∀ ε : ℝ, 0 < ε → Λ.kinetic ≤ (1+ε)*Γ.kinetic + (1+1/ε)*W) ∧
    ∀ ε : ℝ, 0 < ε → energy B.matrix ≤ (1+ε)*energy D.matrix + ε*F.loCoeff*chargeMoment D (4/3) + (1+1/ε)*W := by
  classical
  let C := LocalSpinCalculus.of_leibniz leibniz
  let w := O.indicator (localSpinSpeed H)
  have hm (j : Fin 3) : AEMeasurable (fun x => H x j) (volume.restrict O) :=
    aemeasurable_pi_lambda _ fun i => aemeasurable_pi_lambda _ fun k =>
      (weak j i k).2.1.aestronglyMeasurable.aemeasurable
  have prod : Continuous (fun X : SpinMatrix => star X * X) := continuous_star.mul continuous_id
  have hw : AEMeasurable w volume := (aemeasurable_indicator_iff domain.measurableSet).2 <|
    (Finset.aemeasurable_fun_sum _ fun j _ => prod.measurable.comp_aemeasurable (hm j)).norm
  have zero (x : Position) (hx : x ∉ O) : D.charge x = 0 := by
    rcases domain with ⟨_,hs⟩ | ⟨_,_,_,rfl,h⟩
    · exact image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
    · exact h x hx
  have eq (x) : D.charge x * w x = D.charge x * localSpinSpeed H x := by
    by_cases hx : x ∈ O
    · simp [w,hx]
    · rw [zero x hx, zero_mul, zero_mul]
  have hI : Integrable (fun x => D.charge x*w x) := (funext eq) ▸ finite
  have bound := C.rotationLaw domain meas weak hw (fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)
    ((ae_restrict_mem domain.measurableSet).mono fun x hx => by
      rw [show w x = _ from Set.indicator_of_mem hx (localSpinSpeed H)]
      exact localSpinSpeed_majorizes H x) hI
  simp_rw [eq] at bound
  have rep := F.representable hD
  obtain ⟨Γ,hΓ⟩ := rep
  obtain ⟨Λ,hΛ,_⟩ := bound Γ hΓ
  refine ⟨⟨Λ,hΛ⟩,?_,fun ε he => local_rotation_bound he ⟨Γ,hΓ⟩ bound (F.liebOxford D)⟩
  intro Γ hΓ
  obtain ⟨Λ,hΛ,hW,g,j,hg,hcost,hj,hk⟩ := bound Γ hΓ
  refine ⟨Λ,hΛ,hW,fun ε he => ?_⟩
  have cross := gauge_cross Γ.kinetic_nonneg hg hj he
  have cost := mul_le_mul_of_nonneg_left hcost (by positivity : 0 ≤ 1+1/ε)
  rw [hk]
  simp only [div_eq_mul_inv,one_mul] at cross cost ⊢
  linarith only [cross,cost]

end TSGA.ManyBody
