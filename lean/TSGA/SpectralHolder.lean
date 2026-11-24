import TSGA.PowerOscillation
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Comparing the cube root with a prescribed matrix power

The overlap weights of the two spectral bases sum to two. Normalizing them
and applying scalar concavity gives the Hilbert–Schmidt Hölder bound at
singular matrices as well as in the interior of the positive cone.
-/

noncomputable section

namespace TSGA.Localization

open Matrix
open scoped ComplexOrder

private theorem scalar_power_holder {x y γ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hγ : 0 < γ) (hle : γ ≤ 1) : |x^γ-y^γ| ≤ |x-y|^γ := by
  have ordered {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : t^γ-s^γ ≤ (t-s)^γ := by
    have h := Real.rpow_add_le_add_rpow hs (sub_nonneg.mpr hst) hγ.le hle
    rw [add_sub_cancel] at h
    linarith
  rcases le_total x y with h | h
  · rw [abs_sub_comm x y, abs_sub_comm (x^γ) (y^γ), abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hx h hγ.le))]
    exact ordered hx h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hy h hγ.le))]
    exact ordered hy h

private theorem square_power {s : ℝ} (hs : 0 ≤ s) (γ : ℝ) : (s^γ)^2 = (s^2)^γ := by
  rw [← Real.rpow_mul_natCast hs, mul_comm, Real.rpow_natCast_mul hs]

/-- The dimension factor is exactly 2^((1−γ)/2) for two spin components. -/
theorem spectral_power_holder {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a u : ℝ} (hu : 0 < u) (hua : u ≤ a) :
    hilbertSchmidt (hA.1.cfc (fun t => t^u) - hB.1.cfc (fun t => t^u)) ≤
      (2 : ℝ)^((1-u/a)/2) * hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))^(u/a) := by
  let γ := u/a
  have ha := hu.trans_le hua
  have hγ : 0 < γ := div_pos hu ha
  have hle : γ ≤ 1 := (div_le_one ha).2 hua
  have hau : a*γ = u := by dsimp [γ]; field_simp
  let U : unitary SpinMatrix := star hA.1.eigenvectorUnitary * hB.1.eigenvectorUnitary
  let w (b : Fin 2 × Fin 2) := ‖(U : SpinMatrix) b.1 b.2‖^2 / 2
  let X (s : ℝ) (b : Fin 2 × Fin 2) := (hA.1.eigenvalues b.1 ^ s - hB.1.eigenvalues b.2 ^ s)^2
  let H (s : ℝ) := hilbertSchmidt (hA.1.cfc (fun t => t^s) - hB.1.cfc (fun t => t^s))
  have hH (s : ℝ) : 0 ≤ H s := Real.sqrt_nonneg _
  have hw (b : Fin 2 × Fin 2) : 0 ≤ w b := by dsimp [w]; positivity
  have hsum : ∑ b, w b = 1 := by
    simp only [w, ← Finset.sum_div, Fintype.sum_prod_type, hs_trace]
    norm_num [Matrix.trace_fin_two]
  have hrepr (s : ℝ) : ∑ b, w b * X s b = H s ^ 2 / 2 := by
    rw [show H s ^ 2 = _ from spectral_square hA.1 hB.1 (fun t => t^s), Fintype.sum_prod_type]
    simp only [X, w, Finset.sum_div, show (U : SpinMatrix) =
      (star hA.1.eigenvectorUnitary : SpinMatrix) * hB.1.eigenvectorUnitary from rfl]
    apply Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hx (b : Fin 2 × Fin 2) : X u b ≤ (X a b)^γ := by
    let x := hA.1.eigenvalues b.1
    let y := hB.1.eigenvalues b.2
    have hx := hA.eigenvalues_nonneg b.1
    have hy := hB.eigenvalues_nonneg b.2
    have hh := scalar_power_holder (Real.rpow_nonneg hx a) (Real.rpow_nonneg hy a) hγ hle
    rw [← Real.rpow_mul hx, ← Real.rpow_mul hy, hau] at hh
    simpa only [X, square_power (abs_nonneg _) γ, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hj := (Real.concaveOn_rpow hγ.le hle).le_map_sum (t := Finset.univ)
    (fun b _ => hw b) hsum (fun b _ => show X a b ∈ Set.Ici (0:ℝ) by
      change 0 ≤ (hA.1.eigenvalues b.1 ^ a - hB.1.eigenvalues b.2 ^ a)^2
      exact sq_nonneg _)
  simp only [smul_eq_mul, hrepr] at hj
  have h := (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hx b) (hw b)).trans hj
  rw [hrepr] at h
  have hc : ((2:ℝ)^((1-γ)/2) * H a ^γ)^2 = 2 * (H a ^2/2)^γ := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), square_power (hH a),
      Real.div_rpow (sq_nonneg _) (by norm_num)]
    rw [show ((1-γ)/2)*(2 : ℕ) = 1-γ by push_cast; ring, Real.rpow_sub (by norm_num), Real.rpow_one]
    ring
  apply (sq_le_sq₀ (hH u) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hH a) _))).1
  change H u ^ 2 ≤ ((2:ℝ)^((1-γ)/2) * H a ^γ)^2
  rw [hc]
  linarith only [h]

/-- Equation `eq:theta_to_cube_root`. The constant depends only on θ. -/
theorem theta_to_cube_root {θ : ℝ} (hθ : 0 < θ) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ},
      0 < r → A.trace.re ≤ r → B.trace.re ≤ r →
      let D := fun s : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^s) - hB.1.cfc (fun t => t^s))
      D (1/3) / r^(1/3 : ℝ) ≤ C * (D θ / r^θ)^(min 1 (1/(3*θ))) := by
  let u : ℝ := 1/3
  have hu : 0 < u := by norm_num [u]
  have he : 1/(3*θ) = u/θ := by dsimp [u]; ring
  rw [he]
  by_cases h : θ ≤ u
  · refine ⟨u/θ, div_pos hu hθ, ?_⟩
    intro A B hA hB r hr hrA hrB D
    rw [min_eq_left ((one_le_div hθ).2 h), Real.rpow_one]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hr _)).2
    have hx := matrix_power_oscillation hA hB hθ h hr.le hrA hrB
    change D u ≤ u/θ * (D θ / r^θ) * r^u
    apply hx.trans_eq
    rw [Real.rpow_sub hr]
    ring
  · let C := (2 : ℝ)^((1-u/θ)/2)
    refine ⟨C, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    intro A B hA hB r hr _ _ D
    have hut := (lt_of_not_ge h).le
    rw [min_eq_right ((div_le_one hθ).2 hut)]
    have hx := spectral_power_holder hA hB hu hut
    have hγ : θ*(u/θ) = u := by field_simp
    change D u / r^u ≤ C * (D θ / r^θ)^(u/θ)
    rw [Real.div_rpow (show 0 ≤ D θ from Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le θ), ← Real.rpow_mul hr.le, hγ,
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hx (Real.rpow_nonneg hr.le _)

end TSGA.Localization
