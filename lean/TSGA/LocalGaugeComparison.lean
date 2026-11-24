import TSGA.CoulombReplacement
import TSGA.PhysicalTSGA

/-! # Two-sided comparison under a local spin rotation -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix TSGA.Localization
open scoped ComplexOrder MatrixOrder

theorem RotationLaw.mono {D : Density} {U : Position → unitary SpinMatrix} {w b : ℝ}
    (h : RotationLaw D U w) (hb : w ≤ b) : RotationLaw D U b := by
  intro Γ hΓ
  obtain ⟨Λ,hΛ,hI,g,j,hg,hgw,hj,hK⟩ := h Γ hΓ
  exact ⟨Λ,hΛ,hI,g,j,hg,hgw.trans hb,hj,hK⟩

/-- The forward state supplies representability of the rotated density. -/
def GaugeComparison.of_rotationLaws (F : FiniteEnergyInputs) {A B : Density}
    {U : Position → unitary SpinMatrix} {w : ℝ}
    (target : (conjugatedDensity A U).matrix = B.matrix)
    (rep : ∃ Γ, feasible A.matrix Γ) (fw : RotationLaw A U w)
    (bw : RotationLaw B (fun x => star (U x)) w) : GaugeComparison A B F.loCoeff where
  U := U
  target := target
  forwardCost := w
  inverseCost := w
  forward := fw
  inverse := bw
  input_rep := rep
  output_rep := by
    obtain ⟨Γ,hΓ⟩ := rep
    obtain ⟨Λ,hΛ,_⟩ := fw Γ hΓ
    exact ⟨Λ,target ▸ hΛ⟩
  lo_A := F.liebOxford A
  lo_B := F.liebOxford B

/-- On a tile whose spin axes already agree, use the original state for
both comparisons. The derivative contribution vanishes exactly. -/
def GaugeComparison.identity (F : FiniteEnergyInputs) (A : Density) (rep : ∃ Γ, feasible A.matrix Γ) :
    GaugeComparison A A F.loCoeff := by
  let U : Position → unitary SpinMatrix := fun _ => 1
  have target : (conjugatedDensity A U).matrix = A.matrix := by
    funext x
    simp [conjugatedDensity,U]
  have law : RotationLaw A U 0 := by
    intro Γ hΓ
    exact ⟨Γ, target.symm ▸ hΓ,rfl,0,0,le_rfl,le_rfl,by simp,by ring⟩
  exact GaugeComparison.of_rotationLaws F target rep law (by simpa [U] using law)

private theorem gram_le_trace (A : SpinMatrix) (hA : A.PosSemidef) : A ≤ A.trace • (1 : SpinMatrix) := by
  let U := hA.1.eigenvectorUnitary
  have ht := hA.1.trace_eq_sum_eigenvalues
  have he (i : Fin 2) : hA.1.eigenvalues i ≤ ∑ j, hA.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have h := inSpinFrame_mono U he
  have hm : inSpinFrame U hA.1.eigenvalues = A := hA.1.spectral_theorem.symm
  rw [hm] at h
  convert h using 1
  rw [inSpinFrame_const, ht]
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_sum]
  rfl

/-- The squared Hilbert–Schmidt gradient bounds the operator-valued local
kinetic cost, for use when only the matrix square-root gradient is known. -/
theorem spinGradientGram_le (H : MatrixGradient) (x : Position) :
    (∑ j, star (H x j) * H x j) ≤ (((matrixGradNorm H x)^2 : ℝ) : ℂ) • (1 : SpinMatrix) := by
  let A := ∑ j, star (H x j)*H x j
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => star_mul_self_nonneg _
  have ht : A.trace = (((matrixGradNorm H x)^2 : ℝ) : ℂ) := by
    unfold matrixGradNorm
    rw [Real.sq_sqrt (by positivity)]
    unfold A
    rw [Matrix.trace_sum]
    simp only [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul', Complex.sq_norm]
    simp only [← Complex.ofReal_pow, Complex.sq_norm]
    exact Finset.sum_comm
  exact ht ▸ gram_le_trace A (Matrix.nonneg_iff_posSemidef.mp hA)

end TSGA.ManyBody
