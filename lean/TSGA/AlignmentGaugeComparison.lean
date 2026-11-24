import TSGA.AlignmentRotationCost
import TSGA.LocalGaugeComparison
import TSGA.LocalSpinRotation
import TSGA.GradientForm

/-! # Two-sided Coulomb cost for the local eigenframe on a spiral tile -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped ComplexOrder MatrixOrder

private theorem norm_adjoint_gradient (H : MatrixGradient) (x : Position) :
    matrixGradNorm (fun x j => star (H x j)) x = matrixGradNorm H x := by
  unfold matrixGradNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.star_apply,norm_star]
  exact Finset.sum_comm

private theorem gradient_of_adjoint {K : Set Position} {U : Position → unitary SpinMatrix} {H : MatrixGradient}
    (hH : IsMatrixGradientOn K (fun x => (U x : SpinMatrix)) H) :
    IsMatrixGradientOn K (fun x => ((star (U x) : unitary SpinMatrix) : SpinMatrix))
      (fun x i => star (H x i)) := fun i j k => (hH i k j).conjugate

private theorem scalarIdentity_mono {a b : ℝ} (h : a ≤ b) :
    (a : ℂ) • (1 : SpinMatrix) ≤ (b : ℂ) • (1 : SpinMatrix) := by
  apply Matrix.le_iff.mpr
  rw [← sub_smul,← Complex.ofReal_sub]
  exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr h))

private theorem measurableUnitary {K : Set Position} (hK : MeasurableSet K)
    {U : Position → unitary SpinMatrix} {H : MatrixGradient}
    (off : ∀ x ∉ K, U x = 1) (weak : IsMatrixGradientOn K (fun x => (U x : SpinMatrix)) H) :
    ∀ i j, AEMeasurable (fun x => (U x : SpinMatrix) i j) volume := by
  intro i j
  have inside := (weak 0 i j).1.aestronglyMeasurable.aemeasurable
  have outside : AEMeasurable (fun x => (U x : SpinMatrix) i j) (volume.restrict Kᶜ) := by
    apply (aemeasurable_const (b := (1:SpinMatrix) i j)).congr
    filter_upwards [ae_restrict_mem hK.compl] with x hx
    rw [off x hx]
    rfl
  simpa using (aemeasurable_union_iff.mpr ⟨inside,outside⟩)

/-- Use one laboratory rotation and its adjoint on the actual mixed states.
Both kinetic errors are bounded by the square-root cost of the aligning
frame and the squared wavevector times the squared frame displacement. -/
def SpiralTaper.alignmentGauge {c : Position} {R : ℝ} (hR : 0 < R) (t : SpiralTaper (Metric.closedBall c R))
    (F : FiniteEnergyInputs) (C : LocalSpinCalculus) (A M : Density) {V : Position → unitary SpinMatrix}
    {Z S : MatrixGradient} {r d : ℝ} (hr : 0 < r) (off : ∀ x ∉ Metric.closedBall c R, V x = 1)
    (maps : ∀ x ∈ Metric.closedBall c R, M.matrix x = (V x : SpinMatrix)*A.matrix x*star (V x : SpinMatrix))
    (grad : IsMatrixGradientOn (Metric.closedBall c R) (fun x => (V x : SpinMatrix)) Z)
    (estimate : ∀ᵐ x ∂volume.restrict (Metric.closedBall c R),
      r*(matrixGradNorm Z x)^2 ≤ 192^2*(matrixGradNorm S x)^2)
    (near : ∀ x ∈ Metric.closedBall c R, hilbertSchmidt ((V x : SpinMatrix)-1) ≤ d)
    (cap : ∀ x ∈ Metric.closedBall c R, M.charge x ≤ r) (charge : AEMeasurable M.charge volume)
    (shape : Integrable t.shape) (root : AEMeasurable (kineticDensity S) volume)
    (kin : Integrable fun x => t.shape x*kineticDensity S x) (rep : ∃ Γ, feasible (t.field A).matrix Γ) :
    GaugeComparison (t.field A) (t.field M) F.loCoeff := by
  let U := t.alignment V
  let H := laboratoryGradient t.wavevector V Z
  let w := alignmentWeight S r t.wavevector d
  let K := Metric.closedBall c R
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have weak := t.alignment_gradient (weakPlaneWaveProduct_of_isCompact (isCompact_closedBall c R)) grad
  have out (x) (hx : x ∉ K) : U x = 1 := by simp [U,SpiralTaper.alignment,off x hx]
  have hm := measurableUnitary hK out weak
  have weak' := gradient_of_adjoint weak
  have hm' := measurableUnitary hK (U := fun x => star (U x)) (fun x hx => by simp [out x hx]) weak'
  have hw : AEMeasurable w volume :=
    (aemeasurable_const.mul root).add aemeasurable_const
  have wn (x) : 0 ≤ w x := by dsimp [w,alignmentWeight,kineticDensity]; positivity
  have point : ∀ᵐ x ∂volume.restrict K, (matrixGradNorm H x)^2 ≤ w x :=
    alignment_weight_bound hr estimate ((ae_restrict_mem hK).mono near)
  have major := point.mono fun x hx => (spinGradientGram_le H x).trans (scalarIdentity_mono hx)
  have major' := point.mono fun x hx => (spinGradientGram_le (fun x i => star (H x i)) x).trans
    (scalarIdentity_mono (by simpa only [norm_adjoint_gradient] using hx))
  have dom (D : Density) : LocalRotationDomain (t.field D) K := by
    right
    refine ⟨c,R,hR,rfl,fun x hx => ?_⟩
    simp [Density.charge,SpiralTaper.field,SSW.cutoffSpiral,t.outside x hx]
  have target := t.alignment_target V A M maps
  have eqcharge : (t.field A).charge = (t.field M).charge := by
    funext x
    rw [← conjugated_charge (t.field A) U x]
    change ((conjugatedDensity (t.field A) U).matrix x).trace.re = _
    rw [target]
    rfl
  have weighted := alignmentWeight_integral t M (d := d) hr cap charge shape kin
  have hi := weighted.1
  have hb := weighted.2
  have fw := C.rotationLaw (dom A) hm weak hw wn major (by rw [eqcharge]; exact hi)
  have bw := C.rotationLaw (dom M) hm' weak' hw wn major' hi
  exact GaugeComparison.of_rotationLaws F target rep (fw.mono (by rw [eqcharge]; exact hb)) (bw.mono hb)

/-- The polarized branch chooses the local eigenframe by the explicit Pauli
formula. The estimate in the exponent `a = 1/p` gives the displacement
factor in the wavevector term in Proposition 4.16. -/
theorem gapped_alignmentGauge {M : Density} {c : Position} {R r a ω : ℝ} (hR : 0 < R) (hr : 0 < r)
    (t : SpiralTaper (Metric.closedBall c R)) (F : FiniteEnergyInputs) (C : LocalSpinCalculus)
    (sob : SobolevCompositionOn (Metric.closedBall c R)) (cap : ∀ x ∈ Metric.closedBall c R, M.charge x ≤ r)
    (peak : ∃ z ∈ Metric.closedBall c R, M.charge z = r)
    (minor : ∃ y ∈ Metric.closedBall c R, ∃ i : Fin 2, (M.positive y).1.eigenvalues i ≤ r/8)
    (small : ∀ x ∈ Metric.closedBall c R, ∀ y ∈ Metric.closedBall c R, hilbertSchmidt (M.matrix x-M.matrix y) ≤ r/64)
    (ha : 0 < a) (ha' : a ≤ 1) (osc : ∀ x ∈ Metric.closedBall c R, hilbertSchmidt (M.power a x-M.power a c) ≤ ω)
    {S : MatrixGradient} (weak : IsMatrixGradientOn (Metric.closedBall c R) (M.power (1/2)) S)
    (charge : AEMeasurable M.charge volume) (shape : Integrable t.shape) (root : AEMeasurable (kineticDensity S) volume)
    (kin : Integrable fun x => t.shape x*kineticDensity S x) (rep : ∃ Γ, feasible (t.field (referenceDensity M c)).matrix Γ) :
    ∃ G : GaugeComparison (t.field (referenceDensity M c)) (t.field M) F.loCoeff,
      G.forwardCost = alignmentCost t S r ((96/a)*(ω/r^a)) ∧ G.inverseCost = G.forwardCost := by
  have hc := Metric.mem_closedBall_self hR.le (x := c)
  obtain ⟨V,Z,off,grad,maps,base,estimate⟩ := gapped_alignment_unitary M Metric.isClosed_closedBall.measurableSet
    hc sob hr cap peak minor small weak
  have near := alignment_displacement_of_power hr ha ha' hc cap base osc
  exact ⟨t.alignmentGauge hR F C _ M hr off maps grad estimate near cap charge shape root kin rep,rfl,rfl⟩

end TSGA.ManyBody
