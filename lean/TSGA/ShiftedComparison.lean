import TSGA.ComparisonMatrices

/-! # Comparison on a uniformly positive localization ball

Scalar shifts bracket the field in its original spin frame. The minority
floor makes every sublinear matrix power Lipschitz on the relevant spectra.
-/

noncomputable section
namespace TSGA.Localization
open Matrix
open scoped ComplexOrder MatrixOrder

private theorem scalar_identity_mono {a b : ℝ} (h : a ≤ b) :
    a • (1 : SpinMatrix) ≤ b • (1 : SpinMatrix) := by
  simpa only [inSpinFrame_const] using
    (inSpinFrame_mono (1 : unitary SpinMatrix) (a := fun _ => a) (b := fun _ => b) fun _ => h)

private theorem eig_floor {A : SpinMatrix} (hA : A.PosSemidef) {a : ℝ}
    (h : a • (1 : SpinMatrix) ≤ A) (i : Fin 2) : a ≤ hA.1.eigenvalues i := by
  have hs : inSpinFrame hA.1.eigenvectorUnitary hA.1.eigenvalues = A := hA.1.spectral_theorem.symm
  rw [← hs] at h
  exact (inSpinFrame_floor_iff _ _ a).1 h i

/-- Lipschitz continuity of a sublinear matrix power with a strictly positive common floor. -/
theorem matrix_power_floor {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {m u : ℝ} (hm : 0 < m) (hu : 0 < u) (hu' : u ≤ 1)
    (ha : m • (1 : SpinMatrix) ≤ A) (hb : m • (1 : SpinMatrix) ≤ B) :
    hilbertSchmidt (hA.1.cfc (fun t => t^u) - hB.1.cfc (fun t => t^u)) ≤
      (u*m^(u-1))*hilbertSchmidt (A-B) := by
  have hid {X : SpinMatrix} (hX : X.PosSemidef) : hX.1.cfc id = X := by
    rw [← hX.1.cfc_eq, cfc_id ℝ X hX.1.isSelfAdjoint]
  suffices h : ∀ i j, |hA.1.eigenvalues i ^ u - hB.1.eigenvalues j ^ u| ≤
      (u*m^(u-1)) * |id (hA.1.eigenvalues i) - id (hB.1.eigenvalues j)| by
    simpa only [hid hA, hid hB] using spectral_lipschitz_of_eigenvalues hA hB (fun t => t^u) id
      (mul_nonneg hu.le (Real.rpow_nonneg hm.le _)) h
  intro i j
  have hd (s : ℝ) (hs : s ∈ Set.Ici m) : HasDerivAt (fun t : ℝ => t^u) (u*s^(u-1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl (hm.trans_le hs).ne')
  have bound (s : ℝ) (hs : s ∈ Set.Ici m) : ‖u*s^(u-1)‖ ≤ u*m^(u-1) := by
    rw [Real.norm_of_nonneg (mul_nonneg hu.le (Real.rpow_nonneg (hm.le.trans hs) _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hs (sub_nonpos.mpr hu')) hu.le
  simpa only [id_eq, Real.norm_eq_abs] using (convex_Ici m).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) bound (eig_floor hB hb j) (eig_floor hA ha i)

private theorem hs_shift_order {A B : SpinMatrix} (hA : A.IsHermitian) (hB : B.IsHermitian) {η : ℝ}
    (hd : hilbertSchmidt (B-A) ≤ η) : A-η • (1 : SpinMatrix) ≤ B := by
  let d := hilbertSchmidt (B-A)
  have h := SSW.hilbertSchmidt_shift_posSemidef (hB.sub hA)
  have h' := h.add ((PosSemidef.one : (1 : SpinMatrix).PosSemidef).smul (sub_nonneg.mpr hd))
  apply Matrix.le_iff.mpr
  have he : B - (A-η • (1 : SpinMatrix)) = d • 1 + (B-A) + (η-d) • 1 := by
    rw [sub_smul]; abel
  rw [he]
  exact h'

/-- If M is at least r/8 and its oscillation is at most η ≤ r/64, the shifts
M(c)±ηI bracket it in physical space, and both matrices are at least r/16. -/
theorem shifted_comparison (D : Density) {K : Set Position} {c x : Position}
    (hc : c ∈ K) (hx : x ∈ K) {r η : ℝ} (hr : 0 ≤ r) (hsmall : η ≤ r/64)
    (osc : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.matrix y - D.matrix z) ≤ η)
    (floor : ∀ y ∈ K, (r/8) • (1 : SpinMatrix) ≤ D.matrix y) :
    let lo := D.matrix c - η • (1 : SpinMatrix)
    let hi := D.matrix c + η • (1 : SpinMatrix)
    (r/16) • (1 : SpinMatrix) ≤ lo ∧ lo ≤ D.matrix x ∧ D.matrix x ≤ hi ∧ (r/16) • (1 : SpinMatrix) ≤ hi := by
  intro lo hi
  have hlow : lo ≤ D.matrix x := hs_shift_order (D.positive c).1 (D.positive x).1 (osc x hx c hc)
  have hhigh : D.matrix x ≤ hi := by
    apply (sub_le_iff_le_add).1
    exact hs_shift_order (D.positive x).1 (D.positive c).1 (osc c hc x hx)
  have hmin : (r/16) • (1 : SpinMatrix) ≤ lo := by
    apply le_sub_iff_add_le.mpr
    rw [← add_smul]
    exact (scalar_identity_mono (show r/16+η ≤ r/8 by linarith)).trans (floor c hc)
  exact ⟨hmin, hlow, hhigh, hmin.trans (hlow.trans hhigh)⟩

open scoped Matrix.Norms.Frobenius in
/-- Every intermediate scalar shift, including the two comparison matrices,
has the stated power control with the explicit spectral floor r/16. -/
theorem shifted_power_comparison (D : Density) {K : Set Position} {c x : Position}
    (hc : c ∈ K) (hx : x ∈ K) {r η t : ℝ} (hr : 0 < r) (hsmall : η ≤ r/64) (ht : |t| ≤ η)
    (osc : ∀ y ∈ K, ∀ z ∈ K, hilbertSchmidt (D.matrix y - D.matrix z) ≤ η)
    (floor : ∀ y ∈ K, (r/8) • (1 : SpinMatrix) ≤ D.matrix y) :
    let B := D.matrix c + t • (1 : SpinMatrix)
    ∃ hB : B.PosSemidef, ∀ {u : ℝ}, 0 < u → u ≤ 1 →
      hilbertSchmidt (hB.1.cfc (fun z => z^u) - D.power u x) ≤ (u*(r/16)^(u-1))*(3*η) := by
  intro B
  have hm : (r/16) • (1 : SpinMatrix) ≤ B := by
    change _ ≤ D.matrix c + t • (1 : SpinMatrix)
    apply sub_le_iff_le_add.mp
    rw [← sub_smul]
    exact (scalar_identity_mono (show r/16-t ≤ r/8 by linarith [(abs_le.mp ht).1])).trans (floor c hc)
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    ((PosSemidef.one.smul (show 0 ≤ r/16 by positivity)).nonneg.trans hm)
  refine ⟨hB, fun {u} hu hu' => ?_⟩
  have hmx := (scalar_identity_mono (show r/16 ≤ r/8 by linarith)).trans (floor x hx)
  apply (matrix_power_floor hB (D.positive x) (by positivity : 0 < r/16) hu hu' hm hmx).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hu.le (Real.rpow_nonneg (by positivity) _))
  have hI : ‖(1 : SpinMatrix)‖ ≤ 2 := by
    rw [← SSW.hs_eq_norm]
    simpa using SSW.hilbertSchmidt_le_trace (PosSemidef.one : (1 : SpinMatrix).PosSemidef)
  have ho := osc c hc x hx
  rw [SSW.hs_eq_norm] at ho ⊢
  have he : B - D.matrix x = t • (1 : SpinMatrix) + (D.matrix c - D.matrix x) := by dsimp [B]; abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs]
  linarith only [ho, mul_le_mul ht hI (norm_nonneg _) ((abs_nonneg t).trans ht)]

end TSGA.Localization
