import TSGA.SpectralLipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Oscillations of positive spin matrices at a fixed charge scale

These are the two power comparisons at the beginning of Proposition 4.16.
The scalar mean-value bound is only needed on the interval containing the
spectra. The two matrices may have different eigenvectors or zero eigenvalues.
-/

namespace TSGA.Localization

open Matrix
open scoped ComplexOrder

private theorem power_on_interval {k r : ℝ} (hk : 1 ≤ k) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 r) (hy : y ∈ Set.Icc 0 r) :
    |x^k-y^k| ≤ k*r^(k-1) * |x-y| := by
  have der (s : ℝ) : HasDerivAt (fun t : ℝ => t^k) (k*s^(k-1)) s :=
    Real.hasDerivAt_rpow_const (Or.inr hk)
  have bound (s : ℝ) (hs : s ∈ Set.Icc 0 r) : ‖k*s^(k-1)‖ ≤ k*r^(k-1) := by
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hs.1 _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.1 hs.2 (by linarith)) (by linarith)
  simpa only [Real.norm_eq_abs] using (convex_Icc (0 : ℝ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (der s).hasDerivWithinAt) bound hy hx

private theorem eigenvalue_le_charge {M : SpinMatrix} (h : M.PosSemidef) (i : Fin 2) :
    h.isHermitian.eigenvalues i ≤ M.trace.re := by
  rw [h.1.trace_eq_sum_eigenvalues, Fin.sum_univ_two, Complex.add_re]
  fin_cases i
  · exact le_add_of_nonneg_right (h.eigenvalues_nonneg 1)
  · exact le_add_of_nonneg_left (h.eigenvalues_nonneg 0)

/-- On matrices of trace at most r, the u power is Lipschitz relative to
the a power with constant (u/a) r^(u−a). -/
theorem matrix_power_oscillation {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a u r : ℝ} (ha : 0 < a) (hau : a ≤ u) (hr : 0 ≤ r) (hbA : A.trace.re ≤ r) (hbB : B.trace.re ≤ r) :
    hilbertSchmidt (hA.1.cfc (fun t => t^u) - hB.1.cfc (fun t => t^u)) ≤
      (u/a * r^(u-a)) * hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a)) := by
  let k := u/a
  have hk : 1 ≤ k := (one_le_div ha).2 hau
  have hak : a*k = u := by dsimp [k]; field_simp
  have hscale : (r^a)^(k-1) = r^(u-a) := by rw [← Real.rpow_mul hr, mul_sub, hak, mul_one]
  apply spectral_lipschitz_of_eigenvalues hA hB _ _
    (mul_nonneg (div_nonneg (ha.le.trans hau) ha.le) (Real.rpow_nonneg hr _))
  intro i j
  have coord {M : SpinMatrix} (hM : M.PosSemidef) (h : M.trace.re ≤ r) (l : Fin 2) :
      hM.1.eigenvalues l ^ a ∈ Set.Icc 0 (r^a) :=
    ⟨Real.rpow_nonneg (hM.eigenvalues_nonneg l) _, Real.rpow_le_rpow (hM.eigenvalues_nonneg l)
      ((eigenvalue_le_charge hM l).trans h) ha.le⟩
  have hs := power_on_interval hk (coord hA hbA i) (coord hB hbB j)
  rwa [← Real.rpow_mul (hA.eigenvalues_nonneg i), ← Real.rpow_mul (hB.eigenvalues_nonneg j), hak, hscale] at hs

end TSGA.Localization
