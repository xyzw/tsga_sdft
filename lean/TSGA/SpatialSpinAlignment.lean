import TSGA.SpinComparison
import TSGA.RayRegularity
import TSGA.MatrixChainRule

/-! # Weak gradient of the local aligning rotation

On a ball with a spectral gap for the square root, the normalized traceless
part specifies a spin axis. Normalizing the Pauli intertwiner a second time
gives its unitary rotation. Both normalizations are Lipschitz on the range.
-/

noncomputable section
namespace TSGA.Localization

open MeasureTheory SSW
open scoped Matrix.Norms.Frobenius

private theorem equal_norm_directions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (h : ‖u‖ = ‖v‖) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*‖u-v‖ ≤ 2*‖a • u-b • v‖ := by
  have radial : ‖(a-b) • v‖ ≤ ‖a • u-b • v‖ := by
    have hr := abs_norm_sub_norm_le (a • u) (b • v)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, h,
      ← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg v)] using hr
  calc
    _ = ‖a • u-a • v‖ := by rw [← smul_sub, norm_smul, Real.norm_of_nonneg ha]
    _ ≤ ‖a • u-b • v‖ + ‖b • v-a • v‖ := by simpa only [dist_eq_norm] using dist_triangle (a • u) (b • v) (a • v)
    _ ≤ _ := by rw [norm_sub_rev (b • v), ← sub_smul]; linarith only [radial]

private theorem norm_sq_trace (U : SpinMatrix) : ‖U‖ ^ 2 = (U * star U).trace.re := by
  rw [← hs_eq_norm, hilbertSchmidt, Real.sq_sqrt (by positivity)]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.sq_norm, Complex.mul_conj]

private theorem spin_unitary_norm {U : SpinMatrix} (h : U ∈ unitary SpinMatrix) : ‖U‖ = Real.sqrt 2 := by
  have hsq := norm_sq_trace U
  rw [(Unitary.mem_iff.mp h).2] at hsq
  norm_num [Matrix.trace_one] at hsq
  exact (Real.sqrt_sq (norm_nonneg U)).symm.trans (congrArg Real.sqrt hsq)

private theorem pauli_unit {n : Fin 3 → ℝ} (hn : spinDot n n = 1) : pauli n ∈ unitary SpinMatrix :=
  Matrix.mem_unitaryGroup_iff.mpr (by rw [pauli_star, pauli_sq hn])

private theorem axis_distance {n m : Fin 3 → ℝ} {X Y : SpinMatrix} {a b g : ℝ}
    (hn : spinDot n n = 1) (hm : spinDot m m = 1) (hg : 0 < g) (ha : g ≤ a) (hb : g ≤ b)
    (hX : a • pauli n = (2:ℝ) • X - X.trace.re • 1)
    (hY : b • pauli m = (2:ℝ) • Y - Y.trace.re • 1) : g*‖pauli n-pauli m‖ ≤ 12*‖X-Y‖ := by
  have h2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have htr := abs_trace_re_le_hilbertSchmidt (X-Y)
  rw [hs_eq_norm,Matrix.trace_sub,Complex.sub_re] at htr
  have h1 : ‖(1 : SpinMatrix)‖ ≤ 2 := (spin_unitary_norm (one_mem _)).le.trans h2
  have hgap := equal_norm_directions ((spin_unitary_norm (pauli_unit hn)).trans (spin_unitary_norm (pauli_unit hm)).symm)
    (hg.le.trans ha) (hg.le.trans hb)
  rw [hX, hY, show (2:ℝ) • X-X.trace.re • 1-((2:ℝ) • Y-Y.trace.re • 1) =
    (2:ℝ) • (X-Y) - (X.trace.re-Y.trace.re) • 1 by rw [smul_sub,sub_smul]; abel] at hgap
  have hnorm := norm_sub_le ((2:ℝ) • (X-Y)) ((X.trace.re-Y.trace.re) • (1:SpinMatrix))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hnorm
  have ht := mul_le_mul htr h1 (norm_nonneg _) (by positivity : (0:ℝ) ≤ 2*‖X-Y‖)
  linarith only [hgap,hnorm,ht,mul_le_mul_of_nonneg_right ha (norm_nonneg (pauli n-pauli m))]

/-- The twice-normalized rotation on the hemisphere has a Lipschitz bound
in the original square root X. The identities for the traceless part are
the Pauli spectral decompositions at the two endpoints. -/
theorem alignSpin_lipschitz_gap {n m n₀ : Fin 3 → ℝ} {X Y : SpinMatrix} {a b g : ℝ}
    (hn : spinDot n n = 1) (hm : spinDot m m = 1) (h₀ : spinDot n₀ n₀ = 1)
    (hn₀ : -(1/2:ℝ) ≤ spinDot n n₀) (hm₀ : -(1/2:ℝ) ≤ spinDot m n₀)
    (hg : 0 < g) (ha : g ≤ a) (hb : g ≤ b)
    (hX : a • pauli n = (2:ℝ) • X - X.trace.re • 1)
    (hY : b • pauli m = (2:ℝ) • Y - Y.trace.re • 1) :
    hilbertSchmidt (alignSpin n n₀ - alignSpin m n₀) ≤ (48/g)*hilbertSchmidt (X-Y) := by
  have h2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hax := axis_distance hn hm hg ha hb hX hY
  let den := fun v => Real.sqrt (2*(1+spinDot v n₀))
  have hd (v : Fin 3 → ℝ) (hv : -(1/2:ℝ) ≤ spinDot v n₀) : 1 ≤ den v := by
    change 1 ≤ Real.sqrt _
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have repr (v : Fin 3 → ℝ) (hv : -(1/2:ℝ) ≤ spinDot v n₀) :
      den v • alignSpin v n₀ = 1+pauli v*pauli n₀ := by
    change den v • ((den v)⁻¹ • _) = _
    rw [smul_smul,mul_inv_cancel₀ (zero_lt_one.trans_le (hd v hv)).ne', one_smul]
  have hu := equal_norm_directions
    ((spin_unitary_norm (alignSpin_unitary hn h₀ (by linarith))).trans
      (spin_unitary_norm (alignSpin_unitary hm h₀ (by linarith))).symm)
    (zero_le_one.trans (hd n hn₀)) (zero_le_one.trans (hd m hm₀))
  rw [repr n hn₀, repr m hm₀, add_sub_add_left_eq_sub, ← sub_mul] at hu
  have hmul := (Matrix.frobenius_norm_mul (pauli n-pauli m) (pauli n₀)).trans
    (mul_le_mul_of_nonneg_left ((spin_unitary_norm (pauli_unit h₀)).le.trans h2) (norm_nonneg _))
  have hrot : ‖alignSpin n n₀-alignSpin m n₀‖ ≤ 4*‖pauli n-pauli m‖ := by
    linarith only [hu,hmul,le_mul_of_one_le_left (norm_nonneg (alignSpin n n₀-alignSpin m n₀)) (hd n hn₀)]
  rw [hs_eq_norm,hs_eq_norm,div_mul_eq_mul_div,le_div_iff₀ hg]
  linarith only [mul_le_mul_of_nonneg_left hrot hg.le, hax]

/-- The local Lipschitz composition theorem for a finite-dimensional
Sobolev map on a ball, in the weak derivative convention of this project. -/
def SobolevCompositionOn (K : Set Position) : Prop :=
  ∀ (u v : Position → SpinMatrix) (W : MatrixGradient) (L : ℝ), 0 ≤ L →
    (∀ x ∈ K, ∀ y ∈ K, hilbertSchmidt (v x-v y) ≤ L*hilbertSchmidt (u x-u y)) →
    IsMatrixGradientOn K u W → ∃ Z : MatrixGradient, IsMatrixGradientOn K v Z ∧
      ∀ᵐ x ∂volume.restrict K, matrixGradNorm Z x ≤ L*matrixGradNorm W x

/-- If the square-root spectral gap is at least g, the aligning rotation
costs at most (48/g)² times the square-root kinetic density on the ball. -/
theorem alignSpin_weak_gradient {K : Set Position} (sob : SobolevCompositionOn K)
    {S : Position → SpinMatrix} {n : Position → Fin 3 → ℝ} {n₀ : Fin 3 → ℝ}
    {gap : Position → ℝ} {g : ℝ} (hg : 0 < g) (h₀ : spinDot n₀ n₀ = 1)
    (haxes : ∀ x ∈ K, spinDot (n x) (n x) = 1 ∧ -(1/2:ℝ) ≤ spinDot (n x) n₀ ∧
      g ≤ gap x ∧ gap x • pauli (n x) = (2:ℝ) • S x - (S x).trace.re • 1)
    {W : MatrixGradient} (hW : IsMatrixGradientOn K S W) :
    ∃ Z : MatrixGradient, IsMatrixGradientOn K (fun x => alignSpin (n x) n₀) Z ∧
      ∀ᵐ x ∂volume.restrict K, (matrixGradNorm Z x)^2 ≤ (48/g)^2*(matrixGradNorm W x)^2 := by
  have hL : 0 ≤ 48/g := by positivity
  obtain ⟨Z,hZ,hle⟩ := sob S (fun x => alignSpin (n x) n₀) W (48/g) hL (fun x hx y hy =>
    alignSpin_lipschitz_gap (haxes x hx).1 (haxes y hy).1 h₀ (haxes x hx).2.1 (haxes y hy).2.1
      hg (haxes x hx).2.2.1 (haxes y hy).2.2.1 (haxes x hx).2.2.2 (haxes y hy).2.2.2) hW
  refine ⟨Z,hZ,hle.mono fun x h => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (show 0 ≤ matrixGradNorm Z x from Real.sqrt_nonneg _) h 2

end TSGA.Localization
