import TSGA.SharpInterpolation
import TSGA.SpectralLipschitz

/-! # Sobolev comparison for matrix powers

The analytic input is Lipschitz composition for a finite-dimensional
Hilbert-space-valued local Sobolev function. It is stated in distance form
on the range, so no extension of the scalar function outside the spectrum is
needed. The spectral estimate and the bound for the derivative of a sum are
proved below.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory
open scoped ComplexOrder

/-- The finite-dimensional Sobolev Lipschitz composition theorem on the
range of `u`. The two-point inequality defines a Lipschitz map `u x ↦ v x`
on that range. Applying the ACL characterization along each coordinate line
and summing the squared derivative bounds gives this Hilbert–Schmidt form. -/
def SobolevLipschitzComposition : Prop :=
  ∀ (u v : Position → SpinMatrix) (W : MatrixGradient) (L : ℝ), 0 ≤ L →
    (∀ x y, hilbertSchmidt (v x - v y) ≤ L * hilbertSchmidt (u x - u y)) →
    IsMatrixGradientOn Set.univ u W →
    ∃ Z : MatrixGradient, IsMatrixGradientOn Set.univ v Z ∧
      AEStronglyMeasurable (matrixGradNorm Z) volume ∧
      ∀ᵐ x, matrixGradNorm Z x ≤ L * matrixGradNorm W x

private theorem weak_add {M N : Position → SpinMatrix} {G T : MatrixGradient}
    (hG : IsMatrixGradientOn Set.univ M G) (hT : IsMatrixGradientOn Set.univ N T) :
    IsMatrixGradientOn Set.univ (fun x => M x + N x) (G+T) := by
  intro i j k
  obtain ⟨hM, hg, hm⟩ := hG i j k
  obtain ⟨hN, ht, hn⟩ := hT i j k
  refine ⟨hM.add hN, hg.add ht, ?_⟩
  intro ψ hψ hc hs
  have hw := hm ψ hψ hc hs
  have hv := hn ψ hψ hc hs
  simp only [Measure.restrict_univ] at hw hv ⊢
  let d := fun x => (fderiv ℝ ψ x) (PiLp.single 2 i 1)
  have hd : Continuous d := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcd : HasCompactSupport d := hc.fderiv_apply ℝ _
  have int {f : Position → ℂ} {w : Position → ℝ} (hf : LocallyIntegrableOn f Set.univ)
      (hw : Continuous w) (hcw : HasCompactSupport w) : Integrable fun x => w x • f x :=
    (locallyIntegrableOn_univ.mp hf).integrable_smul_left_of_hasCompactSupport hw hcw
  change (∫ x, d x • (M x j k + N x j k)) = -(∫ x, ψ x • (G x i j k + T x i j k))
  simp_rw [smul_add]
  rw [integral_add (int hM hd hcd) (int hN hd hcd),
    integral_add (int hg hψ.continuous hc) (int ht hψ.continuous hc)]
  change (∫ x, d x • M x j k) = _ at hw
  change (∫ x, d x • N x j k) = _ at hv
  rw [hw, hv, neg_add]

private theorem grad_add_le (G T : MatrixGradient) (x : Position) :
    matrixGradNorm (G+T) x ≤ matrixGradNorm G x + matrixGradNorm T x := by
  let pack (W : MatrixGradient) : EuclideanSpace ℂ (Fin 3 × Fin 2 × Fin 2) :=
    WithLp.toLp 2 (fun i => W x i.1 i.2.1 i.2.2)
  have hn (W : MatrixGradient) : ‖pack W‖ = matrixGradNorm W x := by
    simp [pack, matrixGradNorm, PiLp.norm_eq_of_L2, Fintype.sum_prod_type]
  have ha : pack (G+T) = pack G + pack T := rfl
  simpa only [← hn, ha] using norm_add_le (pack G) (pack T)

private theorem power_sum (D : Density) (a b : ℝ) (x : Position) :
    (D.positive x).isHermitian.cfc (fun s => s ^ a + s ^ b) = D.power a x + D.power b x := by
  let h := (D.positive x).isHermitian
  have hs : (spectrum ℝ (D.matrix x)).Finite := by
    rw [h.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  unfold Density.power
  simp only [← h.cfc_eq]
  exact cfc_add (a := D.matrix x) (fun s : ℝ => s ^ a) (fun s : ℝ => s ^ b)
    (hs.continuousOn _) (hs.continuousOn _)

/-- Hilbert–Schmidt spectral comparison and ordinary Sobolev composition give
the weak power comparison used by the sharp alternative of Theorem 3.3. -/
theorem weakPowerComparison_of_sobolev (H : SobolevLipschitzComposition) : WeakPowerComparison := by
  intro D a k l L G T _ _ _ hL lip hG hT
  let u := fun x => D.power a x + D.power (a*k) x
  let v := D.power (a*l)
  have hpoint (x y : Position) : hilbertSchmidt (v x - v y) ≤ L * hilbertSchmidt (u x - u y) := by
    have hs (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
        |s^(a*l) - t^(a*l)| ≤ L * |(s^a + s^(a*k)) - (t^a + t^(a*k))| := by
      simpa only [← Real.rpow_mul hs, ← Real.rpow_mul ht] using
        lip (s^a) (t^a) (Real.rpow_nonneg hs _) (Real.rpow_nonneg ht _)
    dsimp only [u, v]
    rw [← power_sum D a (a*k) x, ← power_sum D a (a*k) y]
    exact spectral_lipschitz (D.positive x) (D.positive y) (fun s => s^(a*l))
      (fun s => s^a + s^(a*k)) hL hs
  obtain ⟨Z, hz, hm, hb⟩ := H u v (G+T) L hL hpoint (weak_add hG hT)
  exact ⟨Z, hz, hm, hb.mono fun x hx => hx.trans (mul_le_mul_of_nonneg_left (grad_add_le G T x) hL)⟩

end TSGA.Localization
