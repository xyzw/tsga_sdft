import TSGA.SkeletonRays
import TSGA.SkeletonMultiplier
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Cubic electrostatic cost of the locally neutral skeleton

The Fourier series and its normalization are those of the unit three-torus.
The pyramid field vanishes off a layer of relative volume at most 3s and
is bounded there by 16Rs. The difference between the two mollifiers costs
one power of s before Parseval is applied to the shell indicator.
-/

noncomputable section
namespace TSGA.Skeleton
open MeasureTheory Set UnitAddTorus

/-- Use the normalized Haar measure entering the Fourier basis on ℝ/ℤ. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Torus := UnitAddTorus (Fin 3)
abbrev Mode := Fin 3 → ℤ
abbrev cellMeasure : Measure Torus := volume
abbrev TorusL2 := Lp ℂ 2 cellMeasure

def frequency (n : Mode) : Position := WithLp.toLp 2 (fun i => 2*Real.pi*(n i : ℝ))

@[simp] theorem frequency_zero : frequency 0 = 0 := by ext i; simp [frequency]

/-- Ray coordinates on the periodic pyramid partition. The last geometric
identity is the shell volume obtained from the Jacobian proportional to λ². -/
structure PyramidCoordinates where
  radial : Torus → ℝ
  radial_measurable : Measurable radial
  radial_le_one : ∀ x, radial x ≤ 1
  offset : Torus → Fin 3 → ℝ
  radius : ℝ
  offset_bound : ∀ x i, |offset x i| ≤ radius
  shell_volume : ∀ u ∈ Icc (0:ℝ) 1, cellMeasure.real {x | 1-u ≤ radial x} = shellFraction u

/-- The two scale-independent Fourier identities remaining in the geometric
assembly. The ray-coordinate formulas express both the shell and its radial flux through
the same face integral g. The second identity is periodic convolution. -/
structure SkeletonCoefficients (P : PyramidCoordinates) (s b : ℝ) (η : SSW.Mollifier) where
  flux : Fin 3 → TorusL2
  shell : TorusL2
  error : Torus → ℂ
  flux_eq : ∀ j, ∀ᵐ x, flux j x =
    ((P.offset x j * rayPrimitive s (P.radial x) / P.radial x^3 : ℝ) : ℂ)
  shell_eq : ∀ᵐ x, shell x = if 1-s/2 ≤ P.radial x then 1 else 0
  ray_coordinates : ∀ n : Mode, n ≠ 0 → ∃ g g' : ℝ → ℂ,
    (∀ t, HasDerivAt g (g' t) t) ∧ Continuous g' ∧
    mFourierCoeff (fun x => (if 1-s/2 ≤ P.radial x then (shellCoefficient s : ℂ) else 0) -
      (if 1-s ≤ P.radial x then 1 else 0)) n =
      (shellCoefficient s : ℂ)*rayValue (s/2) g-rayValue s g ∧
    Complex.I * (∑ j, ((frequency n j : ℝ) : ℂ) * mFourierCoeff (flux j) n) =
      rayFlux s g'-(shellCoefficient s : ℂ)*rayFlux (s/2) g'
  convolution : ∀ n : Mode, n ≠ 0 →
    mFourierCoeff error n = multiplier η (b*s) (frequency n) *
      mFourierCoeff (fun x => (if 1-s/2 ≤ P.radial x then (shellCoefficient s : ℂ) else 0) -
        (if 1-s ≤ P.radial x then 1 else 0)) n +
      (shellCoefficient s : ℂ) * (multiplier η (b*s/2) (frequency n) - multiplier η (b*s) (frequency n)) *
        mFourierCoeff shell n

theorem SkeletonCoefficients.divergence {P : PyramidCoordinates} {s b : ℝ} {η : SSW.Mollifier}
    (C : SkeletonCoefficients P s b η) (hs : 0 < s) (hs' : s ≤ 1/2) (n : Mode) (hn : n ≠ 0) :
    mFourierCoeff (fun x => (if 1-s/2 ≤ P.radial x then (shellCoefficient s : ℂ) else 0) -
      (if 1-s ≤ P.radial x then 1 else 0)) n =
      Complex.I * ∑ j, ((frequency n j : ℝ) : ℂ) * mFourierCoeff (C.flux j) n := by
  obtain ⟨g,g',hg,hg',ha,hb⟩ := C.ray_coordinates n hn
  exact ha.trans ((neutral_integration_by_parts hs hs' hg hg').trans hb.symm)

private theorem l2_on_layer {P : PyramidCoordinates} {s B : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2)
    (f : TorusL2) (h : ∀ᵐ x, ‖f x‖ ≤ if 1-s ≤ P.radial x then B else 0) :
    (∫ x, ‖f x‖^2) ≤ 3*s*B^2 := by
  classical
  let S := {x | 1-s ≤ P.radial x}
  have hS : MeasurableSet S := measurableSet_le measurable_const P.radial_measurable
  have hi : Integrable (S.indicator fun _ => B^2) := (integrable_const _).indicator hS
  have hc := integral_mono_of_nonneg (μ := volume) (ae_of_all _ fun x => sq_nonneg ‖f x‖) hi
    (by filter_upwards [h] with x hx
        by_cases hx' : 1-s ≤ P.radial x
        · rw [ite_eq_left hx'] at hx
          rw [indicator_of_mem (show x ∈ S from hx')]
          exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx
        · rw [ite_eq_right hx'] at hx
          rw [indicator_of_notMem (show x ∉ S from hx'),le_antisymm hx (norm_nonneg _)]
          norm_num)
  rw [integral_indicator_const _ hS,smul_eq_mul] at hc
  have hvol : volume.real S ≤ 3*s :=
    (P.shell_volume s ⟨hs.le,by linarith⟩).trans_le (shellFraction_le hs.le (by linarith))
  exact hc.trans (mul_le_mul_of_nonneg_right hvol (sq_nonneg _))

private theorem flux_l2 {P : PyramidCoordinates} {s b : ℝ} {η : SSW.Mollifier}
    (C : SkeletonCoefficients P s b η) (hs : 0 < s) (hs' : s ≤ 1/2) (j : Fin 3) :
    (∫ x, ‖C.flux j x‖^2) ≤ 3*s*(16*P.radius*s)^2 := by
  apply l2_on_layer hs hs'
  filter_upwards [C.flux_eq j] with x hx
  rw [hx,Complex.norm_real,Real.norm_eq_abs]
  by_cases h : 1-s ≤ P.radial x
  · rw [ite_eq_left h]
    exact rayFlux_bound hs hs' (P.radial_le_one x) (P.offset_bound x j)
  · simp [h,rayPrimitive_off_shell hs.le (lt_of_not_ge h)]

private theorem shell_l2 {P : PyramidCoordinates} {s b : ℝ} {η : SSW.Mollifier}
    (C : SkeletonCoefficients P s b η) (hs : 0 < s) (hs' : s ≤ 1/2) :
    (∫ x, ‖C.shell x‖^2) ≤ 3*s := by
  have h := l2_on_layer (P := P) (B := 1) hs hs' C.shell (by
    filter_upwards [C.shell_eq] with x hx
    by_cases hu : 1-s/2 ≤ P.radial x
    · simp [hx,hu,show 1-s ≤ P.radial x by linarith]
    · simp [hx,hu]; split <;> norm_num)
  simpa using h

private def weight (err : Torus → ℂ) (n : Mode) : ℝ := ‖mFourierCoeff err n‖^2 / ‖frequency n‖^2

private theorem mode_bound {P : PyramidCoordinates} {s b : ℝ} {η : SSW.Mollifier}
    (C : SkeletonCoefficients P s b η) (hs : 0 < s) (hs' : s ≤ 1/2) (n : Mode) :
    weight C.error n ≤ 6*(∑ j, ‖mFourierCoeff (C.flux j) n‖^2) +
      2*(|b| *firstMoment η)^2*s^2*‖mFourierCoeff C.shell n‖^2 := by
  let k := frequency n
  let f := fun j => ‖mFourierCoeff (C.flux j) n‖
  let g := ‖mFourierCoeff C.shell n‖
  let L := |b| *firstMoment η
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) (firstMoment_nonneg η)
  have hb : 0 ≤ 6*(∑ j, (f j)^2)+2*L^2*s^2*g^2 := by positivity
  by_cases hn : n = 0
  · subst n
    simpa only [weight,frequency_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),div_zero] using hb
  by_cases hk : ‖k‖ = 0
  · change ‖_‖^2/‖k‖^2 ≤ _
    simpa [hk] using hb
  have hk' := lt_of_le_of_ne (norm_nonneg k) (Ne.symm hk)
  have hc := shellCoefficient_bounds hs hs'
  have h1 : ‖(Complex.I * ∑ j, ((k j : ℝ):ℂ)*mFourierCoeff (C.flux j) n)‖ ≤ ‖k‖*(∑ j, f j) := by
    rw [norm_mul,Complex.norm_I,one_mul,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le k j) (norm_nonneg _)
  have h2 := multiplier_difference η (b*s/2) (b*s) k
  rw [show b*s/2-b*s= -(b*s)/2 by ring,abs_div,abs_neg,abs_mul,abs_of_pos hs,abs_of_pos (by norm_num : (0:ℝ)<2)] at h2
  have hnorm : ‖mFourierCoeff C.error n‖ ≤ ‖k‖*((∑ j, f j) + L*s*g) := by
    rw [C.convolution n hn, C.divergence hs hs' n hn]
    apply (norm_add_le ..).trans
    simp only [norm_mul, Complex.norm_real,Real.norm_of_nonneg hc.1]
    rw [norm_mul,Complex.norm_I,one_mul] at h1
    have ha := mul_le_mul (multiplier_norm η (b*s) k) h1 (norm_nonneg _) zero_le_one
    have hc' := mul_le_mul hc.2 h2 (norm_nonneg _) (by norm_num)
    have hd := mul_le_mul_of_nonneg_right hc' (norm_nonneg (mFourierCoeff C.shell n))
    change _ ≤ ‖k‖*((∑ j, f j)+L*s*g)
    dsimp only [k,f,g,L] at *
    simp only [Complex.norm_I,one_mul] at *
    linarith only [ha,hd]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) hnorm)).mpr hnorm
  change ‖mFourierCoeff C.error n‖^2/‖k‖^2 ≤ _
  apply (div_le_iff₀ (sq_pos_of_pos hk')).2
  apply hsq.trans
  rw [mul_pow]
  apply (mul_le_mul_of_nonneg_left _ (sq_nonneg ‖k‖)).trans_eq (mul_comm _ _)
  change ((∑ j, f j)+L*s*g)^2 ≤ 6*(∑ j, (f j)^2)+2*L^2*s^2*g^2
  simp only [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (f 0-f 1),sq_nonneg (f 1-f 2),sq_nonneg (f 0-f 2),
    sq_nonneg ((f 0+f 1+f 2)-L*s*g)]

/-- The nonzero-mode estimate of eq. Fourier_skeleton. Division at the zero
frequency contributes zero, so the sum can be taken over the full lattice. -/
theorem skeleton_fourier {P : PyramidCoordinates} {s b : ℝ} {η : SSW.Mollifier}
    (C : SkeletonCoefficients P s b η) (hs : 0 < s) (hs' : s ≤ 1/2) :
    Summable (fun n : Mode => ‖mFourierCoeff C.error n‖^2/‖frequency n‖^2) ∧
    (∑' n : Mode, ‖mFourierCoeff C.error n‖^2/‖frequency n‖^2) ≤
      (54*(16*P.radius)^2 + 6*(|b| *firstMoment η)^2)*s^3 := by
  classical
  have hfinite (T : Finset Mode) :
      ∑ n ∈ T, weight C.error n ≤ (54*(16*P.radius)^2+6*(|b| *firstMoment η)^2)*s^3 := by
    have h (f : TorusL2) : ∑ n ∈ T, ‖mFourierCoeff f n‖^2 ≤ ∫ x, ‖f x‖^2 :=
      sum_le_hasSum T (fun n _ => sq_nonneg _) (hasSum_sq_mFourierCoeff (d := Fin 3) f)
    have hb := Finset.sum_le_sum fun n (_ : n ∈ T) => mode_bound C hs hs' n
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
    rw [Finset.sum_comm] at hb
    have hF := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (h (C.flux j)).trans (flux_l2 C hs hs' j)
    have hG := (h C.shell).trans (shell_l2 C hs hs')
    simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hF
    linarith only [hb,hF,mul_le_mul_of_nonneg_left hG (show 0 ≤ 2*(|b| *firstMoment η)^2*s^2 by positivity)]
  have hw : 0 ≤ weight C.error := fun n => div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_le hw hfinite,Real.tsum_le_of_sum_le hw hfinite⟩

/-- Restoring the physical tile length yields the coefficient δ³/ℓ multiplying
the rotation/dilation average and the squared charge density. -/
theorem skeleton_physical_scale {ℓ δ : ℝ} (he : 0 < ℓ) : ℓ^2*(δ/ℓ)^3 = δ^3/ℓ := by
  field_simp [he.ne']

/-- The electrostatic remainder after the rotation/dilation estimate in
Theorem 4.10. The hypothesis is the averaged Fourier representation bound
before estimating the skeleton. -/
theorem averaged_electrostatic {P : PyramidCoordinates} {ℓ δ b α K E : ℝ} {η : SSW.Mollifier}
    (he : 0 < ℓ) (hd : 0 < δ) (hs : δ/ℓ ≤ 1/2) (hα : 0 < α) (hα' : α ≤ 1) (hK : 0 ≤ K)
    (C : SkeletonCoefficients P (δ/ℓ) b η) (ρ : Position → ℝ)
    (havg : E ≤ K*Real.log α⁻¹*ℓ^2 *
      (∑' n : Mode, ‖mFourierCoeff C.error n‖^2/‖frequency n‖^2) * ∫ x, ρ x^2) :
    E ≤ K*(54*(16*P.radius)^2+6*(|b| * firstMoment η)^2)*Real.log α⁻¹*(δ^3/ℓ)*(∫ x, ρ x^2) := by
  have ha : 0 ≤ Real.log α⁻¹ := Real.log_nonneg ((one_le_inv₀ hα).mpr hα')
  have h := (skeleton_fourier C (div_pos hd he) hs).2
  apply havg.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity))
    (integral_nonneg fun x => sq_nonneg (ρ x))).trans_eq
  rw [← skeleton_physical_scale (δ := δ) he]
  ring

end TSGA.Skeleton
