import TSGA.KineticTrial
import TSGA.SpectralLipschitz
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.MeanValue

/-! # The layer-cake gradient estimate

In the square-root eigenvalue `r`, the dilation curve is
`t ↦ √η(t/r²)`. Its derivative has an L² norm independent of `r`. The
two spectral bases transfer the squared scalar Lipschitz estimate to
the integrated Hilbert–Schmidt norm, including at a vanishing eigenvalue.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory Set TSGA.Localization
open scoped ComplexOrder

abbrev profileMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev ProfileL2 := Lp ℝ 2 profileMeasure

def profileAt (η : ℝ → ℝ) (e t : ℝ) : ℝ := if e = 0 then 0 else √(η (t/e))

/-- Ordinary L² differentiation of dilations. The coefficient and norm of
the derivative are computed below from its explicit pointwise formula. -/
structure DilationDerivative (η : ℝ → ℝ) where
  curve : ℝ → ProfileL2
  velocity : ℝ → ProfileL2
  represents : ∀ r, 0 ≤ r → (⇑(curve r)) =ᵐ[profileMeasure] profileAt η (r^2)
  continuous : ContinuousOn curve (Ici 0)
  differentiates : ∀ r > 0, HasDerivAt curve (velocity r) r
  derivative_value : ∀ r > 0, (⇑(velocity r)) =ᵐ[profileMeasure] fun t =>
    (-2*t/r^3) * deriv (fun s => √(η s)) (t/r^2)

private theorem profile_norm (v : ProfileL2) : ‖v‖^2 = ∫ t, (v t)^2 ∂profileMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, sq]

theorem profile_velocity_norm {η : ℝ → ℝ} (d : DilationDerivative η) {r : ℝ} (hr : 0 < r) :
    ‖d.velocity r‖ ^ 2 = trialStiffness η := by
  let H (s : ℝ) := s^2 * (deriv (fun t => √(η t)) s)^2
  have he : (fun t => (d.velocity r t)^2) =ᵐ[profileMeasure]
      fun t => (4/r^2) * H ((r^2)⁻¹ * t) := by
    filter_upwards [d.derivative_value r hr] with t ht
    rw [ht]
    simp only [H, div_eq_mul_inv, mul_comm (r^2)⁻¹ t]
    ring
  rw [profile_norm, integral_congr_ae he, integral_const_mul]
  change _ * (∫ t in Ioi (0:ℝ), H ((r^2)⁻¹ * t)) = _
  rw [integral_comp_mul_left_Ioi H 0 (inv_pos.mpr (sq_pos_of_pos hr))]
  simp only [mul_zero, inv_inv, smul_eq_mul]
  change (4/r^2)*(r^2 * _) = 4 * _
  field_simp
  rfl

theorem profile_lipschitz {η : ℝ → ℝ} (d : DilationDerivative η) :
    LipschitzOnWith ⟨√(trialStiffness η), Real.sqrt_nonneg _⟩ d.curve (Ici 0) := by
  have h : LipschitzOnWith ⟨√(trialStiffness η), Real.sqrt_nonneg _⟩ d.curve (Ioi 0) := by
    apply (convex_Ioi (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr => (d.differentiates r hr).hasDerivWithinAt)
    intro r hr
    change ‖d.velocity r‖ ≤ √(trialStiffness η)
    rw [← profile_velocity_norm d hr, Real.sqrt_sq (norm_nonneg _)]
  rw [← closure_Ioi (a := (0:ℝ))]
  exact h.closure (by simpa only [closure_Ioi] using d.continuous)

private theorem squareRoot_rep {η : ℝ → ℝ} (d : DilationDerivative η) {e : ℝ} (he : 0 ≤ e) :
    (⇑(d.curve (√e))) =ᵐ[profileMeasure] profileAt η e := by
  simpa only [Real.sq_sqrt he] using d.represents (√e) (Real.sqrt_nonneg _)

private theorem profile_sub {η : ℝ → ℝ} (d : DilationDerivative η) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (⇑(d.curve (√a) - d.curve (√b))) =ᵐ[profileMeasure] fun t => profileAt η a t - profileAt η b t :=
  (Lp.coeFn_sub ..).trans ((squareRoot_rep d ha).sub (squareRoot_rep d hb))

theorem profile_distance {η : ℝ → ℝ} (d : DilationDerivative η) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t, (profileAt η a t - profileAt η b t)^2 ∂profileMeasure) ≤
      trialStiffness η * (√a-√b)^2 := by
  let V := d.curve (√a) - d.curve (√b)
  have he : ‖V‖^2 = ∫ t, (profileAt η a t - profileAt η b t)^2 ∂profileMeasure :=
    (profile_norm V).trans (integral_congr_ae ((profile_sub d ha hb).pow_const 2))
  have hl := (profile_lipschitz d).dist_le_mul (x := √a) (y := √b) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [dist_eq_norm, Real.dist_eq] at hl
  change ‖V‖ ≤ √(trialStiffness η) * |√a-√b| at hl
  rw [← he]
  exact (pow_le_pow_left₀ (norm_nonneg V) hl 2).trans_eq (by
    rw [mul_pow, sq_abs, Real.sq_sqrt (trialStiffness_nonneg η)])

/-- The matrix distance estimate includes all overlaps of the two
eigenvector bases. No commutation hypothesis is needed. -/
theorem layer_matrix_distance {η : ℝ → ℝ} (d : DilationDerivative η) (D : Density) (x y : Position) :
    Integrable (fun t => hilbertSchmidt (layerAmplitude η D t x - layerAmplitude η D t y)^2) profileMeasure ∧
    (∫ t, hilbertSchmidt (layerAmplitude η D t x - layerAmplitude η D t y)^2 ∂profileMeasure) ≤
      trialStiffness η * hilbertSchmidt (D.power (1/2) x - D.power (1/2) y)^2 := by
  let A := (D.positive x).isHermitian
  let B := (D.positive y).isHermitian
  let W := fun i j => ‖((star A.eigenvectorUnitary : SpinMatrix) * B.eigenvectorUnitary) i j‖^2
  let Δ := fun i j t => (profileAt η (A.eigenvalues i) t - profileAt η (B.eigenvalues j) t)^2 * W i j
  have ht (t) : hilbertSchmidt (layerAmplitude η D t x - layerAmplitude η D t y)^2 =
      ∑ i, ∑ j, Δ i j t := spectral_square A B _
  have hI (i j) : Integrable (Δ i j) profileMeasure := by
    let V := d.curve (√(A.eigenvalues i)) - d.curve (√(B.eigenvalues j))
    have hv : Integrable (fun t => (V t)^2) profileMeasure := (Lp.memLp V).integrable_sq
    exact ((hv.congr ((profile_sub d ((D.positive x).eigenvalues_nonneg i)
      ((D.positive y).eigenvalues_nonneg j)).pow_const 2)).mul_const (W i j))
  have hx : hilbertSchmidt (D.power (1/2) x - D.power (1/2) y)^2 =
      ∑ i, ∑ j, (√(A.eigenvalues i) - √(B.eigenvalues j))^2 * W i j := by
    simp only [Real.sqrt_eq_rpow]
    exact spectral_square A B (fun t => t ^ (1/2 : ℝ))
  simp_rw [ht]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j), ?_⟩
  rw [hx, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j)]
  simp only [Finset.mul_sum, integral_finsetSum _ (fun j _ => hI _ j)]
  apply Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [show (∫ t, Δ i j t ∂profileMeasure) = _ by
    exact integral_mul_const (W i j) (fun t => (profileAt η (A.eigenvalues i) t - profileAt η (B.eigenvalues j) t)^2)]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (profile_distance d ((D.positive x).eigenvalues_nonneg i)
    ((D.positive y).eigenvalues_nonneg j)) (sq_nonneg _)

/-- Jointly measurable representatives used by the L²-valued Sobolev rule. -/
structure FamilyMeasurable (F : ℝ → Position → SpinMatrix) (V : ℝ → MatrixGradient) : Prop where
  value : ∀ j k, AEStronglyMeasurable (fun z : Position × ℝ => F z.2 z.1 j k) (volume.prod profileMeasure)
  gradient : ∀ i j k, AEStronglyMeasurable (fun z : Position × ℝ => V z.2 z.1 i j k) (volume.prod profileMeasure)

/-- Standard Sobolev composition into the Hilbert space of L² matrix families,
stated in terms of its coordinate weak gradients. The two-point distance is
assumed for arbitrary fields, independently of the layer profile. -/
def FamilySobolevComposition : Prop :=
  ∀ (u : Position → SpinMatrix) (F : ℝ → Position → SpinMatrix) (S : MatrixGradient)
    (V : ℝ → MatrixGradient) (L : ℝ), 0 ≤ L →
    IsMatrixGradientOn univ u S →
    (∀ t > 0, IsMatrixGradientOn univ (F t) (V t)) →
    FamilyMeasurable F V →
    (∀ x y, (∫ t, hilbertSchmidt (F t x - F t y)^2 ∂profileMeasure) ≤ L * hilbertSchmidt (u x-u y)^2) →
    (∀ x y, Integrable (fun t => hilbertSchmidt (F t x-F t y)^2) profileMeasure) →
    ∀ᵐ x, layerCost V x ≤ L * kineticDensity S x

/-- The exact dilation derivative gives the stronger coefficient Kη. In
particular it supplies the gradient-estimate field of a layer trial with
the coefficient (1+√Kη)² used in the manuscript. -/
theorem layer_gradient_estimate {η : ℝ → ℝ} (d : DilationDerivative η)
    (sob : FamilySobolevComposition) {D : Density} {S : MatrixGradient} {V : ℝ → MatrixGradient}
    (hS : IsMatrixGradientOn univ (D.power (1/2)) S)
    (hV : ∀ t > 0, IsMatrixGradientOn univ (layerAmplitude η D t) (V t))
    (hmeas : FamilyMeasurable (layerAmplitude η D) V) :
    (∀ᵐ x, layerCost V x ≤ trialStiffness η * kineticDensity S x) ∧
    (∀ᵐ x, layerCost V x ≤ (1 + √(trialStiffness η))^2 * kineticDensity S x) := by
  have h := sob (D.power (1/2)) (layerAmplitude η D) S V (trialStiffness η)
    (trialStiffness_nonneg η) hS hV hmeas (fun x y => (layer_matrix_distance d D x y).2)
    (fun x y => (layer_matrix_distance d D x y).1)
  refine ⟨h, h.mono fun x hx => hx.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))⟩
  nlinarith [Real.sq_sqrt (trialStiffness_nonneg η), Real.sqrt_nonneg (trialStiffness η)]

/-- Lower-level input for the Fermi-projector construction. The Sobolev
gradient of the layer is identified, and its contribution to the kinetic
trace is left unevaluated. -/
def LayerConstruction (cTF κ₁ κ₂ : ℝ) : Prop :=
  ∀ (D : Density) (S : MatrixGradient), SqrtRegular D S → ∀ ε : ℝ, 0 < ε →
    ∃ w : LayerTrialData D cTF κ₁ κ₂ ε, Nonempty (DilationDerivative w.profile) ∧
      FamilyMeasurable (layerAmplitude w.profile D) w.gradient

theorem LayerConstruction.trials {cTF κ₁ κ₂ : ℝ} (H : LayerConstruction cTF κ₁ κ₂)
    (sob : FamilySobolevComposition) : LayerTrials cTF κ₁ κ₂ := by
  intro D S hD ε hε
  obtain ⟨w, ⟨d⟩, hm⟩ := H D S hD ε hε
  exact ⟨⟨w, (layer_gradient_estimate d sob hD.weak w.weak_gradient hm).2⟩⟩

end TSGA.ManyBody
