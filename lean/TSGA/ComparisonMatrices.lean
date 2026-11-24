import TSGA.PowerOscillation
import TSGA.RayRegularity
import Mathlib.Analysis.Matrix.Order

/-! # Constant comparison matrices on the localization ball

Componentwise extrema of the ordered eigenvalues are put in a single
reference basis. Their powers stay close to the original matrix field
even when the eigenspaces vary. These are the comparison matrices in
the gapped branch of Proposition 4.16.
-/

noncomputable section
namespace TSGA.Localization
open Matrix
open scoped ComplexOrder MatrixOrder

/-- A Hermitian spin matrix with prescribed eigenvalues in basis U. -/
def inSpinFrame (U : unitary SpinMatrix) (v : Fin 2 → ℝ) : SpinMatrix :=
  Unitary.conjStarAlgAut ℂ SpinMatrix U (diagonal (fun i => (v i : ℂ)))

private theorem unframe (U V : unitary SpinMatrix) (X : SpinMatrix) :
    (U : SpinMatrix) * ((star U : SpinMatrix) * X * V) * (star V : SpinMatrix) = X := by
  have hu : (U : SpinMatrix) * (star U : SpinMatrix) = 1 := Unitary.coe_mul_star_self U
  have hv : (V : SpinMatrix) * (star V : SpinMatrix) = 1 := Unitary.coe_mul_star_self V
  calc
    _ = ((U : SpinMatrix) * (star U : SpinMatrix)) * X * ((V : SpinMatrix) * (star V : SpinMatrix)) := by simp only [mul_assoc]
    _ = _ := by rw [hu, hv, one_mul, mul_one]

private theorem framed_left (U V : unitary SpinMatrix) (a : Fin 2 → ℝ) :
    (star U : SpinMatrix) * inSpinFrame U a * V =
      diagonal (fun i => (a i : ℂ)) * ((star U : SpinMatrix) * V) := by
  change (star U : SpinMatrix) * (↑U * _ * (star U : SpinMatrix)) * ↑V = _
  calc
    _ = ((star U : SpinMatrix) * ↑U) * diagonal (fun i => (a i : ℂ)) * ((star U : SpinMatrix) * V) := by simp only [mul_assoc]
    _ = _ := by rw [Unitary.coe_star_mul_self, one_mul]

private theorem framed_right (U V : unitary SpinMatrix) (a : Fin 2 → ℝ) :
    (star U : SpinMatrix) * inSpinFrame V a * V =
      ((star U : SpinMatrix) * V) * diagonal (fun i => (a i : ℂ)) := by
  change (star U : SpinMatrix) * (↑V * _ * (star V : SpinMatrix)) * ↑V = _
  calc
    _ = ((star U : SpinMatrix) * ↑V) * diagonal (fun i => (a i : ℂ)) * ((star V : SpinMatrix) * ↑V) := by simp only [mul_assoc]
    _ = _ := by rw [Unitary.coe_star_mul_self, mul_one]

theorem inSpinFrame_pos (U : unitary SpinMatrix) {a : Fin 2 → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (inSpinFrame U a).PosSemidef :=
  (PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (ha i))).mul_mul_conjTranspose_same (U : SpinMatrix)

theorem inSpinFrame_sub (U : unitary SpinMatrix) (a b : Fin 2 → ℝ) :
    inSpinFrame U a - inSpinFrame U b = inSpinFrame U (a-b) := by
  simp only [inSpinFrame, ← map_sub, diagonal_sub, Pi.sub_apply, Complex.ofReal_sub]

theorem inSpinFrame_mono (U : unitary SpinMatrix) {a b : Fin 2 → ℝ} (h : ∀ i, a i ≤ b i) :
    inSpinFrame U a ≤ inSpinFrame U b := by
  rw [Matrix.le_iff, inSpinFrame_sub]
  exact inSpinFrame_pos U fun i => sub_nonneg.mpr (h i)

theorem inSpinFrame_const (U : unitary SpinMatrix) (t : ℝ) :
    inSpinFrame U (fun _ => t) = t • (1 : SpinMatrix) := by
  have hd : diagonal (fun _ : Fin 2 => (t : ℂ)) = t • (1 : SpinMatrix) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.smul_apply, Complex.real_smul]
    · simp [h, diagonal_apply_ne, Matrix.one_apply_ne]
  have hu : (U : SpinMatrix) * (star U : SpinMatrix) = 1 := Unitary.coe_mul_star_self U
  change (U : SpinMatrix) * diagonal (fun _ : Fin 2 => (t : ℂ)) * (star U : SpinMatrix) = _
  rw [hd, Matrix.mul_smul, mul_one, Matrix.smul_mul, hu]

theorem inSpinFrame_floor_iff (U : unitary SpinMatrix) (a : Fin 2 → ℝ) (t : ℝ) :
    t • (1 : SpinMatrix) ≤ inSpinFrame U a ↔ ∀ i, t ≤ a i := by
  rw [← inSpinFrame_const U t]
  refine ⟨fun h i => ?_, inSpinFrame_mono U⟩
  rw [Matrix.le_iff, inSpinFrame_sub] at h
  have h' := h.conjTranspose_mul_mul_same (U : SpinMatrix)
  change ((star U : SpinMatrix) * inSpinFrame U _ * U).PosSemidef at h'
  rw [framed_left, Unitary.coe_star_mul_self, mul_one] at h'
  have hi := h'.diag_nonneg (i := i)
  rw [diagonal_apply_eq] at hi
  exact sub_nonneg.mp (Complex.zero_le_real.mp hi)

theorem inSpinFrame_trace (U : unitary SpinMatrix) (a : Fin 2 → ℝ) :
    (inSpinFrame U a).trace.re = a 0 + a 1 := by
  change ((↑U * _ * (star U : SpinMatrix)) : SpinMatrix).trace.re = _
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  simp

/-- Functional calculus in any prescribed eigenbasis. On a repeated
eigenvalue the two scalar functions agree on the whole eigenspace. -/
theorem inSpinFrame_cfc (V : unitary SpinMatrix) (a : Fin 2 → ℝ) (h : (inSpinFrame V a).IsHermitian)
    (f : ℝ → ℝ) : h.cfc f = inSpinFrame V (f ∘ a) := by
  let U := h.eigenvectorUnitary
  have hspec : inSpinFrame U h.eigenvalues = inSpinFrame V a := h.spectral_theorem.symm
  have hdiag := (framed_left U V h.eigenvalues).symm.trans
    ((congrArg (fun M : SpinMatrix => (star U : SpinMatrix) * M * V) hspec).trans (framed_right U V a))
  have he : (star U : SpinMatrix) * h.cfc f * V = (star U : SpinMatrix) * inSpinFrame V (f ∘ a) * V := by
    change (star U : SpinMatrix) * inSpinFrame U (f ∘ h.eigenvalues) * V = _
    rw [framed_left, framed_right]
    ext i j
    have hentry := congrArg (fun M : SpinMatrix => M i j) hdiag
    simp only [diagonal_mul, mul_diagonal] at hentry ⊢
    by_cases hz : ((star U : SpinMatrix) * V) i j = 0
    · simp [hz]
    · rw [mul_comm] at hentry
      have heig : h.eigenvalues i = a j := Complex.ofReal_inj.mp (mul_left_cancel₀ hz hentry)
      simp [heig, mul_comm]
  simpa only [unframe] using congrArg (fun M : SpinMatrix => (U : SpinMatrix) * M * (star V : SpinMatrix)) he

theorem inSpinFrame_hs (U : unitary SpinMatrix) (a : Fin 2 → ℝ) :
    hilbertSchmidt (inSpinFrame U a)^2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [← hs_unitary _ U U, framed_left, Unitary.coe_star_mul_self, mul_one,
    hilbertSchmidt, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, diagonal_apply, Real.norm_eq_abs]

theorem overlap_rows (U : unitary SpinMatrix) (i : Fin 2) :
    ‖U.val i 0‖^2 + ‖U.val i 1‖^2 = 1 := by
  have h := congrArg (fun M : SpinMatrix => (M i i).re) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj, Complex.sq_norm] using h

theorem overlap_cols (U : unitary SpinMatrix) (j : Fin 2) :
    ‖U.val 0 j‖^2 + ‖U.val 1 j‖^2 = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_apply, norm_star] using overlap_rows (star U) j

/-- Mathlib's eigenvalue indexing puts the two matrices in the same order. -/
theorem spin_indices_same_order {A B : SpinMatrix} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.eigenvalues 1 ≤ hA.eigenvalues 0 ∧ hB.eigenvalues 1 ≤ hB.eigenvalues 0) ∨
    (hA.eigenvalues 0 ≤ hA.eigenvalues 1 ∧ hB.eigenvalues 0 ≤ hB.eigenvalues 1) := by
  let e := (Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin 2))) (β := Fin 2) (Fintype.card_fin _)).symm
  rcases le_total (e 0) (e 1) with h | h
  · exact Or.inl ⟨hA.eigenvalues₀_antitone h, hB.eigenvalues₀_antitone h⟩
  · exact Or.inr ⟨hA.eigenvalues₀_antitone h, hB.eigenvalues₀_antitone h⟩

/-- The two-component Hoffman–Wielandt inequality for every increasing
spectral function. Mathlib indexes both matrices through the same fixed
equivalence, so their eigenvalues have the same ordering. -/
theorem eigenvalue_distances_le_hs {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Ici 0)) :
    ∑ i, (f (hA.1.eigenvalues i) - f (hB.1.eigenvalues i))^2 ≤
      hilbertSchmidt (hA.1.cfc f - hB.1.cfc f)^2 := by
  let a := f ∘ hA.1.eigenvalues
  let b := f ∘ hB.1.eigenvalues
  let U := star hA.1.eigenvectorUnitary * hB.1.eigenvectorUnitary
  let w := fun i j : Fin 2 => ‖(U : SpinMatrix) i j‖^2
  have row (i : Fin 2) : w i 0 + w i 1 = 1 := overlap_rows U i
  have col (j : Fin 2) : w 0 j + w 1 j = 1 := overlap_cols U j
  have hsort : 0 ≤ (a 0 - a 1)*(b 0-b 1) := by
    have hm {M : SpinMatrix} (h : M.PosSemidef) {i j : Fin 2} (he : h.1.eigenvalues i ≤ h.1.eigenvalues j) :
        f (h.1.eigenvalues i) ≤ f (h.1.eigenvalues j) := hf (h.eigenvalues_nonneg _) (h.eigenvalues_nonneg _) he
    rcases spin_indices_same_order hA.1 hB.1 with ⟨h,k⟩ | ⟨h,k⟩
    · exact mul_nonneg (sub_nonneg.mpr (hm hA h)) (sub_nonneg.mpr (hm hB k))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hm hA h)) (sub_nonpos.mpr (hm hB k))
  rw [spectral_square]
  change (∑ i, (a i-b i)^2) ≤ ∑ i, ∑ j, (a i-b j)^2 * w i j
  simp only [Fin.sum_univ_two]
  have h00 : w 0 0 = 1-w 0 1 := by linarith only [row 0]
  have h10 : w 1 0 = w 0 1 := by linarith only [row 0, col 0]
  have h11 : w 1 1 = 1-w 0 1 := by linarith only [col 1]
  rw [h00, h10, h11]
  nlinarith only [mul_nonneg hsort (show 0 ≤ w 0 1 from sq_nonneg _)]

theorem eigenvalue_power_distance {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u : ℝ} (hu : 0 ≤ u) (i : Fin 2) :
    |hA.1.eigenvalues i^u - hB.1.eigenvalues i^u| ≤
    hilbertSchmidt (hA.1.cfc (fun t => t^u) - hB.1.cfc (fun t => t^u)) := by
  have h := eigenvalue_distances_le_hs hA hB (f := fun t => t^u)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow hx hxy hu)
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1 (by
    rw [sq_abs]
    exact (Finset.single_le_sum (fun (j : Fin 2) _ => sq_nonneg (hA.1.eigenvalues j ^ u - hB.1.eigenvalues j ^ u)) (Finset.mem_univ i)).trans h)


/-- The reference basis is fixed at c. Extremal eigenvalues of different
spin indices can be attained at different points of the same ball. -/
structure SpectralExtrema (D : Density) (K : Set Position) where
  minimumPoint : Fin 2 → Position
  maximumPoint : Fin 2 → Position
  min_mem : ∀ i, minimumPoint i ∈ K
  max_mem : ∀ i, maximumPoint i ∈ K
  lower : ∀ i x, x ∈ K → (D.positive (minimumPoint i)).1.eigenvalues i ≤ (D.positive x).1.eigenvalues i
  upper : ∀ i x, x ∈ K → (D.positive x).1.eigenvalues i ≤ (D.positive (maximumPoint i)).1.eigenvalues i

open scoped Topology in
theorem spinEigenvalue_power_continuousOn (D : Density) {K : Set Position} {u : ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn (D.power u) K) (i : Fin 2) :
    ContinuousOn (fun x => (D.positive x).1.eigenvalues i ^ u) K := by
  intro x hx
  have hh : Continuous hilbertSchmidt := by unfold hilbertSchmidt; fun_prop
  have hd : ContinuousWithinAt (fun y => D.power u y - D.power u x) K x :=
    (hc x hx).sub continuousWithinAt_const
  have hlim := (hh.continuousAt (x := D.power u x - D.power u x)).tendsto.comp hd
  have hl : Filter.Tendsto (fun y => hilbertSchmidt (D.power u y-D.power u x)) (𝓝[K] x) (𝓝 0) := by
    simpa [Function.comp_def, hilbertSchmidt] using hlim
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _ => dist_nonneg) _ hl
  intro y
  simpa only [Real.dist_eq, Density.power] using eigenvalue_power_distance (D.positive y) (D.positive x) hu i

/-- A continuous representative of M^θ is enough to select the extrema,
as supplied by Morrey's embedding on the localization ball. -/
def SpectralExtrema.ofContinuousPower (D : Density) {K : Set Position} (hk : IsCompact K) (hn : K.Nonempty)
    {u : ℝ} (hu : 0 < u) (hc : ContinuousOn (D.power u) K) : SpectralExtrema D K := by
  classical
  have hcont (i : Fin 2) : ContinuousOn (fun x => (D.positive x).1.eigenvalues i) K := by
    have h := (spinEigenvalue_power_continuousOn D hu.le hc i).rpow_const
      (p := u⁻¹) (fun _ _ => Or.inr (inv_nonneg.mpr hu.le))
    simpa only [← Real.rpow_mul ((D.positive _).eigenvalues_nonneg i),
      mul_inv_cancel₀ hu.ne', Real.rpow_one] using h
  choose l hl hmin using fun i => hk.exists_isMinOn hn (hcont i)
  choose u hu hmax using fun i => hk.exists_isMaxOn hn (hcont i)
  exact ⟨l,u,hl,hu, fun i => isMinOn_iff.mp (hmin i), fun i => isMaxOn_iff.mp (hmax i)⟩

def SpectralExtrema.onCompact (D : Density) {K : Set Position} (hk : IsCompact K) (hn : K.Nonempty)
    (hc : ContinuousOn D.matrix K) : SpectralExtrema D K := by
  apply ofContinuousPower D hk hn (u := 1) zero_lt_one
  have h : D.power 1 = D.matrix := by
    funext x
    simp only [Density.power, Real.rpow_one]
    change (D.positive x).1.cfc id = _
    rw [← (D.positive x).1.cfc_eq, cfc_id ℝ _ (D.positive x).1.isSelfAdjoint]
  exact h.symm ▸ hc

namespace SpectralExtrema

variable {D : Density} {K : Set Position} (E : SpectralExtrema D K)

def lowerMatrix (c : Position) : SpinMatrix :=
  inSpinFrame (D.positive c).1.eigenvectorUnitary (fun i => (D.positive (E.minimumPoint i)).1.eigenvalues i)

def upperMatrix (c : Position) : SpinMatrix :=
  inSpinFrame (D.positive c).1.eigenvectorUnitary (fun i => (D.positive (E.maximumPoint i)).1.eigenvalues i)

/-- The local eigenvalues expressed in the reference spin basis. -/
def referenceFrame (D : Density) (c x : Position) : SpinMatrix :=
  inSpinFrame (D.positive c).1.eigenvectorUnitary (D.positive x).1.eigenvalues

/-- The reference-frame field is unitarily equivalent to the original spin density at each point. -/
theorem referenceFrame_conjugate (D : Density) (c x : Position) :
    ∃ V : unitary SpinMatrix, Unitary.conjStarAlgAut ℂ SpinMatrix V (referenceFrame D c x) = D.matrix x := by
  let U := (D.positive c).1.eigenvectorUnitary
  let W := (D.positive x).1.eigenvectorUnitary
  refine ⟨W * star U, ?_⟩
  have h : W * star U * U = W := by simp [mul_assoc]
  calc
    _ = Unitary.conjStarAlgAut ℂ SpinMatrix (W * star U * U)
        (diagonal (fun i => ((D.positive x).1.eigenvalues i : ℂ))) := by
      rw [map_mul (Unitary.conjStarAlgAut ℂ SpinMatrix) (W * star U) U]
      rfl
    _ = D.matrix x := by rw [h]; exact (D.positive x).1.spectral_theorem.symm

theorem lower_pos (c : Position) : (E.lowerMatrix c).PosSemidef :=
  inSpinFrame_pos _ fun i => (D.positive _).eigenvalues_nonneg i

theorem upper_pos (c : Position) : (E.upperMatrix c).PosSemidef :=
  inSpinFrame_pos _ fun i => (D.positive _).eigenvalues_nonneg i

theorem ordered (c : Position) {x : Position} (hx : x ∈ K) :
    E.lowerMatrix c ≤ referenceFrame D c x ∧ referenceFrame D c x ≤ E.upperMatrix c :=
  ⟨inSpinFrame_mono _ fun i => E.lower i x hx, inSpinFrame_mono _ fun i => E.upper i x hx⟩

/-- A scalar lower bound on the two occupancies passes to both constant matrices. -/
theorem minority_floor (c : Position) {t : ℝ}
    (h : ∀ x ∈ K, t • (1 : SpinMatrix) ≤ D.matrix x) :
    t • (1 : SpinMatrix) ≤ E.lowerMatrix c ∧ t • (1 : SpinMatrix) ≤ E.upperMatrix c := by
  have he (x : Position) (hx : x ∈ K) (i : Fin 2) : t ≤ (D.positive x).1.eigenvalues i := by
    have spec : inSpinFrame (D.positive x).1.eigenvectorUnitary (D.positive x).1.eigenvalues = D.matrix x :=
      (D.positive x).1.spectral_theorem.symm
    have hh := h x hx
    rw [← spec] at hh
    exact (inSpinFrame_floor_iff _ _ t).1 hh i
  exact ⟨(inSpinFrame_floor_iff _ _ t).2 fun i => he _ (E.min_mem i) i,
    (inSpinFrame_floor_iff _ _ t).2 fun i => he _ (E.max_mem i) i⟩

private theorem charge_sum (D : Density) (x : Position) :
    D.charge x = (D.positive x).1.eigenvalues 0 + (D.positive x).1.eigenvalues 1 := by
  rw [Density.charge, (D.positive x).1.trace_eq_sum_eigenvalues]
  simp [Fin.sum_univ_two]

theorem trace_bounds (c : Position) {x : Position} (hx : x ∈ K) {r : ℝ} (hr : ∀ y ∈ K, D.charge y ≤ r) :
    (E.lowerMatrix c).trace.re ≤ D.charge x ∧ D.charge x ≤ (E.upperMatrix c).trace.re ∧
    (E.upperMatrix c).trace.re ≤ 2*r := by
  rw [lowerMatrix, upperMatrix, inSpinFrame_trace, inSpinFrame_trace, charge_sum]
  have h0 := hr _ (E.max_mem 0)
  have h1 := hr _ (E.max_mem 1)
  rw [charge_sum] at h0 h1
  exact ⟨add_le_add (E.lower 0 x hx) (E.lower 1 x hx), add_le_add (E.upper 0 x hx) (E.upper 1 x hx),
    by linarith only [h0, h1, (D.positive (E.maximumPoint 0)).eigenvalues_nonneg (1 : Fin 2),
      (D.positive (E.maximumPoint 1)).eigenvalues_nonneg (0 : Fin 2)]⟩

open scoped Matrix.Norms.Frobenius in
private theorem triangle (A B C : SpinMatrix) :
    hilbertSchmidt (A-C) ≤ hilbertSchmidt (A-B) + hilbertSchmidt (B-C) := by
  have h (X : SpinMatrix) : hilbertSchmidt X = ‖X‖ := by
    simp only [hilbertSchmidt, Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow]
  simpa only [h, dist_eq_norm] using dist_triangle A B C

/-- A single choice of extrema works simultaneously for all positive powers.
The input ω is the actual pairwise oscillation of the u power on K, or any
upper bound for it. -/
theorem power_comparison (c : Position) (hc : c ∈ K) {u ω : ℝ} (hu : 0 < u) (hω : 0 ≤ ω)
    (osc : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.power u y - D.power u z) ≤ ω)
    {x : Position} (hx : x ∈ K) :
    hilbertSchmidt ((E.lower_pos c).1.cfc (fun t => t^u) - D.power u x) ≤ 3*ω ∧
    hilbertSchmidt ((E.upper_pos c).1.cfc (fun t => t^u) - D.power u x) ≤ 3*ω := by
  let U := (D.positive c).1.eigenvectorUnitary
  let vc := (D.positive c).1.eigenvalues
  have haux (k : Fin 2 → Position) (hk : ∀ i, k i ∈ K) :
      let b := fun i => (D.positive (k i)).1.eigenvalues i
      let hB := inSpinFrame_pos U (fun i => (D.positive (k i)).eigenvalues_nonneg i)
      hilbertSchmidt (hB.1.cfc (fun t => t^u) - D.power u x) ≤ 3*ω := by
    intro b hB
    have heig (i : Fin 2) : |b i^u - vc i^u| ≤ ω :=
      (eigenvalue_power_distance (D.positive (k i)) (D.positive c) hu.le i).trans (osc _ (hk i) _ hc)
    have hnorm : hilbertSchmidt (hB.1.cfc (fun t => t^u) - D.power u c) ≤ 2*ω := by
      rw [inSpinFrame_cfc]
      change hilbertSchmidt (inSpinFrame U (fun i => (b i)^u) - inSpinFrame U (fun i => (vc i)^u)) ≤ _
      rw [inSpinFrame_sub]
      have hn (X : SpinMatrix) : 0 ≤ hilbertSchmidt X := Real.sqrt_nonneg _
      apply (sq_le_sq₀ (hn _) (mul_nonneg (by norm_num) hω)).1
      rw [inSpinFrame_hs]
      simp only [Pi.sub_apply]
      have hsq (i : Fin 2) := sq_le_sq' (abs_le.mp (heig i)).1 (abs_le.mp (heig i)).2
      nlinarith only [hsq 0, hsq 1, sq_nonneg ω]
    linarith only [triangle (hB.1.cfc (fun t => t^u)) (D.power u c) (D.power u x), hnorm, osc c hc x hx]
  exact ⟨haux E.minimumPoint E.min_mem, haux E.maximumPoint E.max_mem⟩

private theorem cfc_one {A : SpinMatrix} (h : A.PosSemidef) :
    h.1.cfc (fun t : ℝ => t^(1:ℝ)) = A := by
  simp only [Real.rpow_one]
  change h.1.cfc id = A
  rw [← h.1.cfc_eq, cfc_id ℝ A h.1.isSelfAdjoint]

/-- If the peak charge is attained and the matrix oscillation is small, the physical
minority-spin condition gives the common floor νr/2 for the two matrices. -/
theorem minority_at_peak (c : Position) {r ν η : ℝ} (hν : 0 ≤ ν) (hη : η ≤ r/4)
    (peak : ∃ z ∈ K, D.charge z = r)
    (osc : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.matrix y - D.matrix z) ≤ η)
    (hm : ∀ y ∈ K, (ν*D.charge y) • (1 : SpinMatrix) ≤ D.matrix y) :
    (ν*r/2) • (1 : SpinMatrix) ≤ E.lowerMatrix c ∧ (ν*r/2) • (1 : SpinMatrix) ≤ E.upperMatrix c := by
  obtain ⟨z, hz, hmax⟩ := peak
  apply E.minority_floor c
  intro y hy
  have hdiff := (SSW.abs_trace_re_le_hilbertSchmidt (D.matrix z - D.matrix y)).trans
    (mul_le_mul_of_nonneg_left (osc z hz y hy) (by norm_num : (0:ℝ) ≤ 2))
  rw [Matrix.trace_sub, Complex.sub_re] at hdiff
  change |D.charge z - D.charge y| ≤ _ at hdiff
  have hcharge : r/2 ≤ D.charge y := by rw [hmax] at hdiff; linarith only [(abs_le.mp hdiff).2, hη]
  have hscale : ν*r/2 ≤ ν*D.charge y := by linarith only [mul_le_mul_of_nonneg_left hcharge hν]
  apply le_trans _ (hm y hy)
  let U := (D.positive y).1.eigenvectorUnitary
  rw [← inSpinFrame_const U, ← inSpinFrame_const U]
  exact inSpinFrame_mono U fun _ => hscale

/-- The three comparisons at the powers 1/p, θ and 1 for either extremal matrix.
Here d is the normalized oscillation at 1/p and ω bounds the oscillation at θ. -/
theorem power_estimates (c : Position) (hc : c ∈ K) {θ p r d ω : ℝ}
    (hp : 0 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hr : 0 ≤ r) (hd : 0 ≤ d) (hω : 0 ≤ ω)
    (htrace : ∀ y ∈ K, D.charge y ≤ r)
    (hroot : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.power (1/p) y - D.power (1/p) z) ≤ r^(1/p)*d)
    (hosc : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.power θ y - D.power θ z) ≤ ω)
    {B : SpinMatrix} (hB : B.PosSemidef) (hb : B = E.lowerMatrix c ∨ B = E.upperMatrix c)
    {x : Position} (hx : x ∈ K) :
    hilbertSchmidt (hB.1.cfc (fun t => t^(1/p)) - D.power (1/p) x) ≤ 3*(r^(1/p)*d) ∧
    hilbertSchmidt (hB.1.cfc (fun t => t^θ) - D.power θ x) ≤ 3*ω ∧
    hilbertSchmidt (B-D.matrix x) ≤ 3*((1/θ*r^(1-θ))*ω) := by
  have bound {u k : ℝ} (hu : 0 < u) (hk : 0 ≤ k)
      (h : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.power u y - D.power u z) ≤ k) :
      hilbertSchmidt (hB.1.cfc (fun t => t^u) - D.power u x) ≤ 3*k := by
    rcases hb with hb | hb <;> subst B
    · exact (E.power_comparison c hc hu hk h hx).1
    · exact (E.power_comparison c hc hu hk h hx).2
  have hcoef : 0 ≤ 1/θ*r^(1-θ) := mul_nonneg (one_div_nonneg.mpr hθ.le) (Real.rpow_nonneg hr _)
  refine ⟨bound (one_div_pos.mpr hp) (mul_nonneg (Real.rpow_nonneg hr _) hd) hroot,
    bound hθ hω hosc, ?_⟩
  have hone := bound (u := 1) zero_lt_one (mul_nonneg hcoef hω) (fun y hy z hz =>
    (matrix_power_oscillation (D.positive y) (D.positive z) hθ hθ' hr (htrace y hy) (htrace z hz)).trans
      (mul_le_mul_of_nonneg_left (hosc y hy z hz) hcoef))
  rw [cfc_one hB, show D.power 1 x = D.matrix x from cfc_one (D.positive x)] at hone
  exact hone

end SpectralExtrema
end TSGA.Localization
