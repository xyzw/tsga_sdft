import TSGA.CoulombLocalRotation
import TSGA.GradientForm
import TSGA.MinorityRegularity

/-! # Square-root regularity under local spin rotations -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix TSGA.Localization
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The ordinary supported Sobolev multiplier rule for a bounded matrix field.
The majorant controls each partial derivative on the neighborhood where the
coefficient is differentiated. The differentiated product is square integrable
by the weak product rule and the weighted integrability assumption. -/
def LocalMatrixSobolevMultiplier : Prop :=
  ∀ (K O : Set Position), IsClosed K → K ⊆ O →
    (IsOpen O ∨ ∃ c r, 0 < r ∧ O = Metric.closedBall c r) →
    ∀ (A : Position → SpinMatrix) (H : MatrixGradient) (w : Position → ℝ),
      (∀ i j, AEMeasurable (fun x => A x i j) volume) → (∃ b, ∀ x, ‖A x‖ ≤ b) →
      IsMatrixGradientOn O A H → (∀ x ∈ O, ∀ i, ‖H x i‖^2 ≤ w x) →
    ∀ (f : Position → SpinMatrix) (S : MatrixGradient), (∀ x ∉ K, f x = 0) →
      IsMatrixGradientOn Set.univ f S → MemLp (matrixGradNorm S) 2 →
      Integrable (fun x => hilbertSchmidt (f x)^2) →
      Integrable (fun x => hilbertSchmidt (f x)^2 * w x) →
      ∃ T, IsMatrixGradientOn Set.univ (fun x => A x * f x) T ∧ MemLp (matrixGradNorm T) 2

private theorem conjugated_sqrt (D : Density) (U : Position → unitary SpinMatrix) (x : Position) :
    (conjugatedDensity D U).power (1/2) x =
      (U x : SpinMatrix) * D.power (1/2) x * star (U x : SpinMatrix) := by
  let e := Unitary.conjStarAlgAut ℂ SpinMatrix (U x)
  have he : Continuous e := by
    change Continuous (fun m : SpinMatrix => (U x : SpinMatrix) * m * star (U x : SpinMatrix))
    fun_prop
  have h := StarAlgHomClass.map_cfc (S := ℂ) e (fun t : ℝ => t^(1/2 : ℝ)) (D.matrix x)
    (Real.continuous_rpow_const (by norm_num : 0 ≤ (1/2 : ℝ))).continuousOn he
    (D.positive x).isHermitian.isSelfAdjoint ((conjugatedDensity D U).positive x).isHermitian.isSelfAdjoint
  unfold Density.power
  rw [← Matrix.IsHermitian.cfc_eq, ← Matrix.IsHermitian.cfc_eq]
  exact h.symm

private theorem hs_adjoint (M : SpinMatrix) : hilbertSchmidt (star M) = hilbertSchmidt M := by
  simp only [hilbertSchmidt, hs_trace, star_star]
  exact congrArg (fun z : ℂ => Real.sqrt z.re) (Matrix.trace_mul_comm (star M) M)

private theorem hs_left_unitary (U : unitary SpinMatrix) (M : SpinMatrix) :
    hilbertSchmidt ((U : SpinMatrix) * M) = hilbertSchmidt M := by
  simpa using hs_unitary M (star U) 1

set_option maxHeartbeats 600000 in
/-- The rotated positive square root is in H¹. Multiply its two sides in
succession. Unitarity preserves the squared Hilbert–Schmidt norm at each
step, so the same integrable weight controls both products. -/
theorem conjugatedDensity_sqrt_regular (mulRule : LocalMatrixSobolevMultiplier)
    {D : Density} {U : Position → unitary SpinMatrix} {O : Set Position} {H S : MatrixGradient}
    (hD : SqrtRegular D S) (domain : LocalRotationDomain D O) (meas : LocalUnitaryMeasurable U)
    (weak : IsMatrixGradientOn O (fun x => (U x : SpinMatrix)) H)
    (finite : Integrable (fun x => D.charge x * localSpinSpeed H x)) :
    ∃ Z, SqrtRegular (conjugatedDensity D U) Z := by
  let K := tsupport D.charge
  have hK : IsClosed K := isClosed_tsupport _
  have shape : K ⊆ O ∧ (IsOpen O ∨ ∃ c r, 0 < r ∧ O = Metric.closedBall c r) := by
    rcases domain with ⟨ho,hs⟩ | ⟨c,r,hr,rfl,hz⟩
    · exact ⟨hs,Or.inl ho⟩
    · exact ⟨closure_minimal (fun x hx => by by_contra h; exact hx (hz x h)) Metric.isClosed_closedBall,
        Or.inr ⟨c,r,hr,rfl⟩⟩
  have speed (x : Position) (_ : x ∈ O) (i : Fin 3) : ‖H x i‖^2 ≤ localSpinSpeed H x := by
    rw [sq, ← CStarRing.norm_star_mul_self]
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (Finset.single_le_sum (fun j _ => star_mul_self_nonneg (H x j)) (Finset.mem_univ i))
      (star_mul_self_nonneg _)
  have mult := mulRule K O hK shape.1 shape.2 (fun x => (U x : SpinMatrix)) H
    (localSpinSpeed H) meas ⟨1,fun x => (CStarRing.norm_coe_unitary (U x)).le⟩ weak speed
  let R := D.power (1/2)
  have mass (x : Position) : hilbertSchmidt (R x)^2 = D.charge x := by
    rw [hilbertSchmidt, Real.sq_sqrt (by positivity)]
    exact sqrt_hilbertSchmidt_sq D x
  have supp (x : Position) (hx : x ∉ K) : R x = 0 := by
    have h0 : D.charge x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hs : hilbertSchmidt (R x) = 0 := by nlinarith only [mass x,h0]
    ext i j
    exact norm_eq_zero.mp (le_antisymm ((SSW.norm_entry_le_hs (R x) i j).trans_eq hs) (norm_nonneg _))
  obtain ⟨T,hT,hT₂⟩ := mult R S supp hD.weak hD.grad
    (by simpa only [mass] using hD.charge) (by simpa only [mass] using finite)
  let g := fun x => star ((U x : SpinMatrix) * R x)
  let V : MatrixGradient := fun x j => star (T x j)
  have hg : IsMatrixGradientOn Set.univ g V := fun i j k => (hT i k j).conjugate
  have hn (x : Position) : matrixGradNorm V x = matrixGradNorm T x := by
    unfold matrixGradNorm
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simpa only [V, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, norm_star] using
      (Finset.sum_comm (s := (Finset.univ : Finset (Fin 2))) (t := Finset.univ)
        (f := fun j k => ‖T x i k j‖^2))
  have gm (x : Position) : hilbertSchmidt (g x)^2 = D.charge x := by
    rw [show g x = star ((U x : SpinMatrix) * R x) from rfl, hs_adjoint, hs_left_unitary, mass]
  obtain ⟨Z,hZ,hZ₂⟩ := mult g V (fun x hx => by simp [g,supp x hx]) hg
    (by rwa [funext hn]) (by simpa only [gm] using hD.charge) (by simpa only [gm] using finite)
  have herm (x : Position) : star (R x) = R x := by
    change (D.power (1/2) x).conjTranspose = D.power (1/2) x
    rw [Density.power, ← (D.positive x).isHermitian.cfc_eq]
    exact (cfc_predicate (fun t : ℝ => t ^ (1/2 : ℝ)) (D.matrix x)).isHermitian
  have eq (x : Position) : (U x : SpinMatrix) * g x = (conjugatedDensity D U).power (1/2) x := by
    change (U x : SpinMatrix) * star ((U x : SpinMatrix) * R x) = _
    rw [conjugated_sqrt, star_mul, herm, ← Matrix.mul_assoc]
  have hc := funext (conjugated_charge D U)
  exact ⟨Z,hc.symm ▸ hD.charge, (funext eq) ▸ hZ,hZ₂⟩

/-- Lemma 4.13 with both the representability conditions and the Coulomb
energy inequality from the sectorwise rotation of mixed states. -/
theorem coulomb_local_spin_rotation_regular (mulRule : LocalMatrixSobolevMultiplier)
    (leibniz : LocalSectorLeibniz) (F : FiniteEnergyInputs)
    {D : Density} {U : Position → unitary SpinMatrix} {O : Set Position} {H S : MatrixGradient}
    (hD : SqrtRegular D S) (domain : LocalRotationDomain D O) (meas : LocalUnitaryMeasurable U)
    (weak : IsMatrixGradientOn O (fun x => (U x : SpinMatrix)) H)
    (finite : Integrable (fun x => D.charge x * localSpinSpeed H x)) :
    (∃ Z, SqrtRegular (conjugatedDensity D U) Z) ∧ ∀ ε : ℝ, 0 < ε →
      energy (conjugatedDensity D U).matrix ≤ (1+ε)*energy D.matrix + ε*F.loCoeff*chargeMoment D (4/3) +
        (1+1/ε)*(∫ x, D.charge x * localSpinSpeed H x) :=
  ⟨conjugatedDensity_sqrt_regular mulRule hD domain meas weak finite,
    (coulomb_local_spin_rotation leibniz F hD domain meas weak finite).2.2⟩

end TSGA.ManyBody
