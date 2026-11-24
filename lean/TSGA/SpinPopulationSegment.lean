import TSGA.ComparisonMatrices
import TSGA.MinorityFraction

/-! # Spin populations on a fixed-charge segment -/

noncomputable section
namespace TSGA.SSW
open Matrix TSGA.Localization
open scoped ComplexOrder

/-- The two pure-spin endpoints in a prescribed eigenbasis. The coordinate i is
the one whose occupancy increases from 0 to r along the segment. -/
def populationEndpoint (U : unitary SpinMatrix) (r : ℝ) (i : Fin 2) (upper : Bool) : SpinMatrix :=
  inSpinFrame U fun j => if decide (j = i) = upper then r else 0

theorem populationEndpoint_mem (U : unitary SpinMatrix) {r : ℝ} (hr : 0 ≤ r) (i : Fin 2) (b : Bool) :
    populationEndpoint U r i b ∈ fixedCharge r := by
  constructor
  · apply inSpinFrame_pos
    intro j
    split <;> positivity
  · rw [populationEndpoint, inSpinFrame_trace]
    fin_cases i <;> cases b <;> simp

private theorem frame_combo (U : unitary SpinMatrix) (a b : ℝ) (v w : Fin 2 → ℝ) :
    a • inSpinFrame U v + b • inSpinFrame U w =
      inSpinFrame U (fun i => a*v i+b*w i) := by
  let F := Unitary.conjStarAlgAut ℂ SpinMatrix U
  have hm (s : ℝ) (X : SpinMatrix) : F (s • X) = s • F X := by
    change (U : SpinMatrix) * (s • X) * (star U : SpinMatrix) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  change a • F _ + b • F _ = F _
  rw [← hm, ← hm, ← map_add]
  apply congrArg F
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.smul_apply, Complex.real_smul]
  · simp [Matrix.smul_apply, h, diagonal_apply_ne]

theorem population_segment (U : unitary SpinMatrix) {r : ℝ} (hr : 0 < r) (i : Fin 2)
    {v : Fin 2 → ℝ} (hv : v 0+v 1 = r) :
    AffineMap.lineMap (populationEndpoint U r i false) (populationEndpoint U r i true) (v i/r) = inSpinFrame U v := by
  rw [AffineMap.lineMap_apply_module, populationEndpoint, populationEndpoint, frame_combo]
  apply congrArg (inSpinFrame U)
  funext j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> linarith

theorem spin_population_sum {A : SpinMatrix} (h : A.PosSemidef) :
    h.1.eigenvalues 0+h.1.eigenvalues 1 = A.trace.re := by
  rw [h.1.trace_eq_sum_eigenvalues]
  simp [Fin.sum_univ_two]

/-- The cube-root estimate along a segment bounds the cost of changing the
two occupancies in a common frame by the root distance of the original
matrices, even if the latter have different eigenvectors. -/
theorem fixed_frame_population_change {e : SpinMatrix → ℝ} {r u F : ℝ} (hr : 0 < r) (hu : 0 < u)
    (hF : 0 ≤ F)
    (frac : ∀ P ∈ fixedCharge r, ∀ Q ∈ fixedCharge r, ∀ s ∈ Set.Icc (0:ℝ) (1/2), ∀ t ∈ Set.Icc (0:ℝ) (1/2),
      |e (AffineMap.lineMap P Q t)-e (AffineMap.lineMap P Q s)| ≤ F*|t^u-s^u|)
    {A B : SpinMatrix} (hA : A ∈ fixedCharge r) (hB : B ∈ fixedCharge r) :
    |e A - e (inSpinFrame hA.1.1.eigenvectorUnitary hB.1.1.eigenvalues)| ≤
      F*(hilbertSchmidt (hA.1.1.cfc (fun x => x^u)-hB.1.1.cfc (fun x => x^u))/r^u) := by
  let a := hA.1.1.eigenvalues
  let b := hB.1.1.eigenvalues
  let U := hA.1.1.eigenvectorUnitary
  have ha : a 0+a 1 = r := (spin_population_sum hA.1).trans hA.2
  have hb : b 0+b 1 = r := (spin_population_sum hB.1).trans hB.2
  obtain ⟨i, ha', hb'⟩ : ∃ i : Fin 2, a i ≤ r/2 ∧ b i ≤ r/2 := by
    rcases spin_indices_same_order hA.1.1 hB.1.1 with ⟨h,k⟩ | ⟨h,k⟩
    · refine ⟨1, ?_, ?_⟩ <;> change a 1 ≤ a 0 at h <;> change b 1 ≤ b 0 at k <;> linarith
    · refine ⟨0, ?_, ?_⟩ <;> change a 0 ≤ a 1 at h <;> change b 0 ≤ b 1 at k <;> linarith
  have hpos := Real.rpow_pos_of_pos hr u
  have hdist : |(a i/r)^u-(b i/r)^u| ≤
      hilbertSchmidt (hA.1.1.cfc (fun x => x^u)-hB.1.1.cfc (fun x => x^u))/r^u := by
    rw [Real.div_rpow (hA.1.eigenvalues_nonneg _) hr.le, Real.div_rpow (hB.1.eigenvalues_nonneg _) hr.le,
      ← sub_div, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (eigenvalue_power_distance hA.1 hB.1 hu.le i) hpos.le
  have h := frac _ (populationEndpoint_mem U hr.le i false) _ (populationEndpoint_mem U hr.le i true)
    (b i/r) ⟨div_nonneg (hB.1.eigenvalues_nonneg _) hr.le, (div_le_iff₀ hr).2 (by linarith)⟩
    (a i/r) ⟨div_nonneg (hA.1.eigenvalues_nonneg _) hr.le, (div_le_iff₀ hr).2 (by linarith)⟩
  rw [population_segment U hr i ha, population_segment U hr i hb] at h
  have spec : inSpinFrame U a = A := hA.1.1.spectral_theorem.symm
  rw [spec] at h
  exact h.trans (mul_le_mul_of_nonneg_left hdist hF)

end TSGA.SSW
