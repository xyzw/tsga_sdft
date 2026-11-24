import TSGA.SpatialSpinAlignment
import TSGA.BlochFrameTransport

/-! # Spin alignment on the gapped comparison ball of Proposition 4.16 -/

noncomputable section
namespace TSGA.Localization
open MeasureTheory
open scoped ComplexOrder

/-- An eigenvalue below r/8 somewhere in the comparison ball forces a gap
throughout it when the full density oscillation is at most r/64. -/
theorem gap_on_small_tile (D : Density) {K : Set Position} {r : ℝ} (hr : 0 < r)
    (peak : ∃ z ∈ K, D.charge z = r)
    (minor : ∃ y ∈ K, ∃ i : Fin 2, (D.positive y).1.eigenvalues i ≤ r/8)
    (small : ∀ x ∈ K, ∀ y ∈ K, hilbertSchmidt (D.matrix x-D.matrix y) ≤ r/64) :
    ∀ x ∈ K, r/2 ≤ blochGap (D.matrix x) := by
  obtain ⟨z,hz,hmax⟩ := peak
  obtain ⟨y,hy,i,he⟩ := minor
  intro x hx
  have htr := (SSW.abs_trace_re_le_hilbertSchmidt (D.matrix z-D.matrix x)).trans
    (mul_le_mul_of_nonneg_left (small z hz x hx) (by norm_num : (0:ℝ) ≤ 2))
  rw [Matrix.trace_sub,Complex.sub_re] at htr
  change |D.charge z-D.charge x| ≤ _ at htr
  rw [hmax] at htr
  have hd := eigenvalue_power_distance (D.positive x) (D.positive y) (zero_le_one : (0:ℝ) ≤ 1) i
  have one {M : SpinMatrix} (hm : M.PosSemidef) : hm.1.cfc (fun t => t^(1:ℝ)) = M := by
    simp only [Real.rpow_one]
    change hm.1.cfc id = _
    rw [← hm.1.cfc_eq, cfc_id ℝ M hm.1.isSelfAdjoint]
  rw [one (D.positive x),one (D.positive y),Real.rpow_one,Real.rpow_one] at hd
  have hei := (abs_le.mp (hd.trans (small x hx y hy))).2
  have ht := congrArg Complex.re (D.positive x).1.trace_eq_sum_eigenvalues
  simp only [Fin.sum_univ_two,Complex.add_re] at ht
  change D.charge x = (D.positive x).1.eigenvalues 0 + (D.positive x).1.eigenvalues 1 at ht
  let v := (D.positive x).1.eigenvalues
  have hsum : r - r/32 ≤ v 0 + v 1 := by
    change r - r/32 ≤ (D.positive x).1.eigenvalues 0 + (D.positive x).1.eigenvalues 1
    linarith only [ht, (abs_le.mp htr).2]
  have hmin : v i ≤ 9*r/64 := by
    change (D.positive x).1.eigenvalues i ≤ _
    linarith only [hei,he]
  rw [blochGap_eq_eigenvalue_gap (D.positive x).1]
  change r/2 ≤ |v 0-v 1|
  fin_cases i
  · change v 0 ≤ 9*r/64 at hmin
    apply le_trans _ (neg_le_abs (v 0-v 1))
    linarith only [hsum,hmin,hr]
  · change v 1 ≤ 9*r/64 at hmin
    apply le_trans _ (le_abs_self (v 0-v 1))
    linarith only [hsum,hmin,hr]

/-- At a gapped density with small oscillation, the explicit rotations align
the center's majority-spin projector throughout the tile. Their weak kinetic
cost is controlled by the weak gradient of the original square root. -/
theorem gapped_tile_alignment (D : Density) {c : Position} {K : Set Position} (hc : c ∈ K)
    (sob : SobolevCompositionOn K) {r : ℝ} (hr : 0 < r)
    (trace_le : ∀ x ∈ K, D.charge x ≤ r) (peak : ∃ z ∈ K, D.charge z = r)
    (minor : ∃ y ∈ K, ∃ i : Fin 2, (D.positive y).1.eigenvalues i ≤ r/8)
    (small : ∀ x ∈ K, ∀ y ∈ K, hilbertSchmidt (D.matrix x-D.matrix y) ≤ r/64)
    {W : MatrixGradient} (weak : IsMatrixGradientOn K (D.power (1/2)) W) :
    let n := fun x => blochAxis (D.power (1/2) x)
    let V := fun x => alignSpin (n x) (n c)
    (∀ x ∈ K, V x ∈ unitary SpinMatrix ∧ V x*spinProjector (n c)*star (V x) = spinProjector (n x) ∧
      V x*SpectralExtrema.referenceFrame D c x*star (V x) = D.matrix x) ∧
    ∃ Z : MatrixGradient, IsMatrixGradientOn K V Z ∧
      ∀ᵐ x ∂volume.restrict K, r*(matrixGradNorm Z x)^2 ≤ 192^2*(matrixGradNorm W x)^2 := by
  have gap := gap_on_small_tile D hr peak minor small
  let S := D.power (1/2)
  let n := fun x => blochAxis (S x)
  let g := Real.sqrt r/4
  have hg : 0 < g := div_pos (Real.sqrt_pos.mpr hr) (by norm_num)
  have hS (x) : (S x).IsHermitian := by
    change ((D.positive x).1.cfc _).IsHermitian
    rw [← (D.positive x).1.cfc_eq]
    exact (cfc_predicate (fun t : ℝ => t^(1/2:ℝ)) (D.matrix x)).isHermitian
  have hgap (x) (hx : x ∈ K) : g ≤ blochGap (S x) :=
    sqrt_matrix_blochGap (D.positive x) hr (trace_le x hx) (gap x hx)
  have unit (x) (hx : x ∈ K) : spinDot (n x) (n x) = 1 := blochAxis_unit (hg.trans_le (hgap x hx))
  have rep (x) (hx : x ∈ K) := blochGap_smul_pauli (hS x) (hg.trans_le (hgap x hx))
  have hemi (x) (hx : x ∈ K) : -(1/2:ℝ) ≤ spinDot (n x) (n c) := by
    have hnear : hilbertSchmidt (D.matrix x-D.matrix c) ≤ blochGap (D.matrix x)/2 := by
      linarith only [small x hx c hc, gap x hx, hr]
    have hangle := blochAxis_dot_nonneg_of_close (D.positive x).1 (D.positive c).1 hnear
    change -(1/2:ℝ) ≤ spinDot (blochAxis ((D.positive x).1.cfc _)) (blochAxis ((D.positive c).1.cfc _))
    rw [blochAxis_matrix_sqrt (D.positive x),blochAxis_matrix_sqrt (D.positive c)]
    linarith only [hangle]
  constructor
  · intro x hx
    have hdir : -1 < spinDot (n x) (n c) := by linarith [hemi x hx]
    refine ⟨alignSpin_unitary (unit x hx) (unit c hc) hdir,
      alignSpin_projector (unit x hx) (unit c hc) hdir, ?_⟩
    have haxis (z) : n z = blochAxis (D.matrix z) := blochAxis_matrix_sqrt (D.positive z)
    change alignSpin (n x) (n c)*SpectralExtrema.referenceFrame D c x*star (alignSpin (n x) (n c)) = _
    rw [haxis x,haxis c] at hdir ⊢
    exact alignSpin_referenceFrame D c x ((half_pos hr).trans_le (gap c hc)) ((half_pos hr).trans_le (gap x hx)) hdir
  obtain ⟨Z,hZ,hle⟩ := alignSpin_weak_gradient (S := S) sob hg (unit c hc)
    (fun x hx => ⟨unit x hx,hemi x hx,hgap x hx,rep x hx⟩) weak
  refine ⟨Z,hZ,hle.mono fun x h => ?_⟩
  have hcoef : r*(48/g)^2 = 192^2 := by
    dsimp only [g]
    field_simp [(Real.sqrt_pos.mpr hr).ne']
    nlinarith only [Real.sq_sqrt hr.le]
  calc
    _ ≤ r*((48/g)^2*(matrixGradNorm W x)^2) := mul_le_mul_of_nonneg_left h hr.le
    _ = _ := by rw [← mul_assoc,hcoef]

end TSGA.Localization
