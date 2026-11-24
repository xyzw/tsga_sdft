import TSGA.ComparisonMatrices

/-! # Quantitative alignment of two spin eigenframes

Eigenvector phases are chosen to minimize their distance. This gives a
global pointwise rotation, including for orthogonal majority spinors.
-/

noncomputable section
namespace TSGA.Localization
open Matrix
open scoped ComplexOrder

private theorem exists_phase (z : ℂ) : ∃ d : ℂ, ‖d‖ = 1 ∧ ‖z‖ • d = z := by
  by_cases hz : z = 0
  · exact ⟨1, norm_one, by simp [hz]⟩
  have hn := norm_pos_iff.mpr hz
  exact ⟨‖z‖⁻¹ • z, by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne'],
    by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]⟩

private theorem diagonal_unitary (d : Fin 2 → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    Matrix.diagonal d ∈ unitary SpinMatrix := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.star_apply, Complex.mul_conj, ← Complex.sq_norm, hd]
  · simp [Matrix.star_apply, diagonal_apply_ne, h, Ne.symm h, Matrix.one_apply_ne]

private theorem diagonal_conjugate (d : unitary SpinMatrix) (v : Fin 2 → ℂ)
    (hv : (d : SpinMatrix) = diagonal v) (a : Fin 2 → ℂ) :
    Unitary.conjStarAlgAut ℂ SpinMatrix d (diagonal a) = diagonal a := by
  have comm : (d : SpinMatrix) * diagonal a = diagonal a * (d : SpinMatrix) := by
    rw [hv]; simp [diagonal_mul_diagonal, mul_comm]
  have hd : (d : SpinMatrix) * star (d : SpinMatrix) = 1 := Unitary.coe_mul_star_self d
  change (d : SpinMatrix) * diagonal a * star (d : SpinMatrix) = _
  rw [comm, mul_assoc, hd, mul_one]

private theorem frame_transport (U V P : unitary SpinMatrix) (v : Fin 2 → ℂ)
    (hv : (P : SpinMatrix) = diagonal v) (b : Fin 2 → ℝ) :
    Unitary.conjStarAlgAut ℂ SpinMatrix (U * P * star V) (inSpinFrame V b) = inSpinFrame U b := by
  let F := Unitary.conjStarAlgAut ℂ SpinMatrix
  let X := diagonal (fun i => (b i : ℂ))
  have act (S T : unitary SpinMatrix) (M : SpinMatrix) : F S (F T M) = F (S*T) M := by
    rw [map_mul]; rfl
  change F (U*P*star V) (F V X) = F U X
  rw [act, show U*P*star V*V = U*P by simp [mul_assoc], ← act]
  exact congrArg (F U) (diagonal_conjugate P v hv (fun i => (b i : ℂ)))

/-- Alignment changes the eigenvectors of B into those of A, preserving the
ordered occupancies of B. The displacement times the spectral gap of f(A)
is controlled even when the two bases have orthogonal first spinors. -/
theorem eigenframe_alignment {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Ici 0)) :
    ∃ S : unitary SpinMatrix,
      Unitary.conjStarAlgAut ℂ SpinMatrix S B = inSpinFrame hA.1.eigenvectorUnitary hB.1.eigenvalues ∧
      hilbertSchmidt ((S : SpinMatrix)-1) * |f (hA.1.eigenvalues 0)-f (hA.1.eigenvalues 1)| ≤
        4*hilbertSchmidt (hA.1.cfc f-hB.1.cfc f) := by
  let U := hA.1.eigenvectorUnitary
  let V := hB.1.eigenvectorUnitary
  let T : unitary SpinMatrix := star U * V
  choose v hv hf' using fun i : Fin 2 => exists_phase ((T : SpinMatrix) i i)
  let P : unitary SpinMatrix := ⟨diagonal v, diagonal_unitary v hv⟩
  let S := U * P * star V
  refine ⟨S, ?_, ?_⟩
  · have hspec : inSpinFrame V hB.1.eigenvalues = B := hB.1.spectral_theorem.symm
    apply (congrArg (Unitary.conjStarAlgAut ℂ SpinMatrix S) hspec.symm).trans
    exact frame_transport U V P v rfl hB.1.eigenvalues
  let w := fun i j : Fin 2 => ‖(T : SpinMatrix) i j‖^2
  have row (i : Fin 2) : w i 0 + w i 1 = 1 := overlap_rows T i
  have col (j : Fin 2) : w 0 j + w 1 j = 1 := overlap_cols T j
  have hw : w 1 0 = w 0 1 := by linarith only [row 0, col 0]
  have hdiag (i : Fin 2) : ‖v i-(T : SpinMatrix) i i‖^2 ≤ 1-w i i := by
    have hsq : w i i ≤ 1 := by
      fin_cases i
      · change w 0 0 ≤ 1
        linarith only [row 0, show 0 ≤ w 0 1 from sq_nonneg _]
      · change w 1 1 ≤ 1
        linarith only [row 1, show 0 ≤ w 1 0 from sq_nonneg _]
    have hle : ‖(T : SpinMatrix) i i‖ ≤ 1 := by
      change ‖(T : SpinMatrix) i i‖^2 ≤ 1 at hsq
      nlinarith only [hsq, norm_nonneg ((T : SpinMatrix) i i)]
    have hsub : v i-(T : SpinMatrix) i i = (1-‖(T : SpinMatrix) i i‖) • v i := by
      rw [sub_smul, one_smul, hf']
    rw [hsub, norm_smul, hv, mul_one, Real.norm_of_nonneg (sub_nonneg.mpr hle)]
    dsimp only [w]
    nlinarith only [mul_nonneg (norm_nonneg ((T : SpinMatrix) i i)) (sub_nonneg.mpr hle)]
  have hdist : hilbertSchmidt ((S : SpinMatrix)-1)^2 ≤ 4*w 0 1 := by
    have he : (star U : SpinMatrix) * ((S : SpinMatrix)-1) * (V : SpinMatrix) = (P : SpinMatrix) - T := by
      rw [mul_sub, sub_mul, mul_one]
      change (↑(star U * S * V) : SpinMatrix) - ↑T = _
      have h : star U * S * V = P := calc
        _ = (star U * U) * P * (star V * V) := by dsimp only [S]; simp only [mul_assoc]
        _ = _ := by simp
      rw [h]
    rw [← hs_unitary _ U V, he, hilbertSchmidt, Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_two, Matrix.sub_apply]
    change ‖diagonal v 0 0 - _‖^2 + ‖diagonal v 0 1 - _‖^2 +
      (‖diagonal v 1 0 - _‖^2 + ‖diagonal v 1 1 - _‖^2) ≤ _
    simp only [diagonal_apply_eq, diagonal_apply_ne v (by decide : (0:Fin 2) ≠ 1),
      diagonal_apply_ne v (by decide : (1:Fin 2) ≠ 0), zero_sub, norm_neg]
    change ‖v 0-(T : SpinMatrix) 0 0‖^2 + w 0 1 + (w 1 0 + ‖v 1-(T : SpinMatrix) 1 1‖^2) ≤ _
    linarith only [hdiag 0, hdiag 1, row 0, col 1, hw]
  let a := f ∘ hA.1.eigenvalues
  let b := f ∘ hB.1.eigenvalues
  have sort : 0 ≤ (a 0-a 1)*(b 0-b 1) := by
    have hm {M : SpinMatrix} (h : M.PosSemidef) {i j : Fin 2} (he : h.1.eigenvalues i ≤ h.1.eigenvalues j) :
        f (h.1.eigenvalues i) ≤ f (h.1.eigenvalues j) := hf (h.eigenvalues_nonneg _) (h.eigenvalues_nonneg _) he
    rcases spin_indices_same_order hA.1 hB.1 with ⟨h,k⟩ | ⟨h,k⟩
    · exact mul_nonneg (sub_nonneg.mpr (hm hA h)) (sub_nonneg.mpr (hm hB k))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hm hA h)) (sub_nonpos.mpr (hm hB k))
  have hgap : (a 0-a 1)^2 ≤ 2*((a 0-b 1)^2+(a 1-b 0)^2) := by
    nlinarith only [sort, sq_nonneg (b 0-b 1), sq_nonneg ((a 0-b 1)+(a 1-b 0))]
  let d := hilbertSchmidt (hA.1.cfc f-hB.1.cfc f)
  have hspec := spectral_square hA.1 hB.1 f
  change d^2 = ∑ i, ∑ j, (a i-b j)^2*w i j at hspec
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hw] at hspec
  have hcross : (a 0-a 1)^2*w 0 1 ≤ 2*d^2 := by
    nlinarith only [hspec, mul_le_mul_of_nonneg_right hgap (show 0 ≤ w 0 1 from sq_nonneg _),
      mul_nonneg (sq_nonneg (a 0-b 0)) (show 0 ≤ w 0 0 from sq_nonneg _),
      mul_nonneg (sq_nonneg (a 1-b 1)) (show 0 ≤ w 1 1 from sq_nonneg _)]
  change _ * |a 0-a 1| ≤ 4*d
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).1
  rw [mul_pow, sq_abs]
  change hilbertSchmidt ((S : SpinMatrix)-1)^2 * (a 0-a 1)^2 ≤ (4*d)^2
  nlinarith only [hcross, mul_le_mul_of_nonneg_right hdist (sq_nonneg (a 0-a 1)), sq_nonneg d]

end TSGA.Localization
