import TSGA.CutoffFisher
import Mathlib.Analysis.Convex.Contractible

/-! # Fisher estimates for mollified domains

The square root of the cutoff is a translated kernel amplitude measured in
L² of the domain. Its pointwise translation differences are bounded by those
of the amplitude on the whole space. A ball avoiding the boundary lies
entirely inside or entirely outside the domain, so small translations there
cost zero. The integrated translation estimate also gives a volume bound.
-/

noncomputable section
namespace TSGA.SSW
open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology Convolution

/-- Quantitative scalar Sobolev difference quotients in three dimensions.
The factor three comes from summing the bounds for three coordinate directions.
Both conclusions apply to any given weak gradient. -/
structure SobolevDifferenceBounds : Prop where
  pointwise : ∀ (u : Position → ℝ) (G : Position → Position), MemLp u 2 →
    (∀ i, WeakPartialOn univ i u (fun x => G x i)) → MemLp G 2 →
    ∀ (K : Position → ℝ), (∀ x, ∀ᶠ h in 𝓝 (0 : Position), (u (x+h)-u x)^2 ≤ K x * ‖h‖^2) →
      ∀ᵐ x, ‖G x‖^2 ≤ 3*K x
  integral : ∀ (u : Position → ℝ) (G : Position → Position), MemLp u 2 →
    (∀ i, WeakPartialOn univ i u (fun x => G x i)) → MemLp G 2 →
    ∀ (K : ℝ), (∀ h : Position, (∫ x, (u (x+h)-u x)^2) ≤ K*‖h‖^2) →
      (∫ x, ‖G x‖^2) ≤ 3*K

private theorem pointwise_cutoff_difference {Ω : Set Position} (hm : MeasurableSet Ω)
    (η : Mollifier) {δ : ℝ} (hδ : 0 < δ) (x h : Position) :
    let f := smoothedIndicator Ω η δ
    let w := fun y => √(η.scaled δ y)
    (√(f (x+h))-√(f x))^2 ≤ ∫ y, (w (y+h)-w y)^2 := by
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  intro f w
  have hn (y) : 0 ≤ η.scaled δ y := mul_nonneg (by positivity [hδ] : 0 ≤ (δ^3)⁻¹) (η.nonneg _)
  have hw : MemLp w 2 := amplitude_L2 hn (η.scaled_integrable hδ)
  have hx (z : Position) : MemLp (fun y => w (z-y)) 2 (volume.restrict Ω) :=
    (hw.comp_measurePreserving (measurePreserving_sub_left volume z)).restrict _
  have mass (z : Position) : (∫ y in Ω, w (z-y)^2) = f z := by
    simp_rw [show ∀ t, w t^2 = η.scaled δ t from fun t => Real.sq_sqrt (hn t)]
    exact (convolution_restrict Ω hm _ z).symm
  let v := fun y => (w (y+h)-w y)^2
  have hi : Integrable v := ((hw.comp_measurePreserving (measurePreserving_add_right volume h)).sub hw).integrable_sq
  calc
    _ ≤ ∫ y in Ω, v (x-y) := by
      rw [← mass (x+h),← mass x]
      simpa only [v,show ∀ y, x+h-y = x-y+h from fun _ => by abel] using norm_difference (hx (x+h)) (hx x)
    _ ≤ ∫ y, v (x-y) := setIntegral_le_integral (hi.comp_sub_left x) (ae_of_all _ fun _ => sq_nonneg _)
    _ = _ := integral_sub_left_eq_self v volume x

/-- A cutoff is locally constant wherever a ball containing the translated
kernel support misses the domain boundary. -/
private theorem cutoff_local_constant {Ω : Set Position} (hΩ : IsOpen Ω) (η : Mollifier) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs : Function.support η.kernel ⊆ Metric.ball 0 R)
    {x : Position} (hx : x ∉ Metric.thickening ((R+1)*δ) (frontier Ω)) :
    ∀ᶠ h in 𝓝 (0 : Position), smoothedIndicator Ω η δ (x+h) = smoothedIndicator Ω η δ x := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let V := Metric.ball x ((R+1)*δ)
  have hd : V ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro y hy
    by_cases h : y ∈ Ω
    · exact Or.inl h
    · refine Or.inr (fun hc => hx (Metric.mem_thickening_iff.mpr ⟨y,?_,?_⟩))
      · exact ⟨hc,by simpa only [hΩ.interior_eq] using h⟩
      · simpa only [dist_comm] using (Metric.mem_ball.mp hy)
  have splitV : V ⊆ Ω ∨ V ⊆ (closure Ω)ᶜ :=
    IsPreconnected.subset_or_subset hΩ isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun _ hy hc => hc (subset_closure hy)) hd (convex_ball x _).isPreconnected
  let χ := Ω.indicator fun _ => (1 : ℝ)
  let c := χ x
  have hxV : x ∈ V := Metric.mem_ball_self (by positivity)
  have constV (y : Position) (hy : y ∈ V) : χ y = c := by
    rcases splitV with inside | outside
    · simp [χ,c,inside hy,inside hxV]
    · have ex (z) (hz : z ∈ V) : z ∉ Ω := fun ht => outside hz (subset_closure ht)
      simp [χ,c,ex _ hy,ex _ hxV]
  have eqn (h : Position) (hh : ‖h‖ < δ) : smoothedIndicator Ω η δ (x+h) = c := by
    have factor (y : Position) : χ y * η.scaled δ (x+h-y) = c * η.scaled δ (x+h-y) := by
      by_cases hz : η.kernel (δ⁻¹ • (x+h-y)) = 0
      · simp [Mollifier.scaled,hz]
      · have hr := Metric.mem_ball.mp (hs hz)
        simp only [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le),← div_eq_inv_mul] at hr
        have hdist : ‖x+h-y‖ < R*δ := (div_lt_iff₀ hδ).mp hr
        have hy : y ∈ V := by
          change dist y x < _
          calc
            _ ≤ dist y (x+h) + dist (x+h) x := dist_triangle _ _ _
            _ = ‖x+h-y‖ + ‖h‖ := by rw [dist_comm y,dist_eq_norm,dist_eq_norm]; abel_nf
            _ < (R+1)*δ := by linarith only [hdist,hh]
        rw [constV y hy]
    change (∫ y, χ y*η.scaled δ (x+h-y)) = c
    simp_rw [factor]
    rw [integral_const_mul,integral_sub_left_eq_self,η.scaled_mass hδ,mul_one]
  filter_upwards [Metric.ball_mem_nhds (0 : Position) hδ] with h hh
  rw [eqn h (by simpa using hh)]
  simpa using (eqn 0 (by simpa using hδ)).symm

/-- Fisher bounds with constants depending only on the unscaled mollifier.
The first estimate is supported on a boundary layer. The second remains
effective for a smoothing width larger than the size of the domain. -/
theorem cutoff_gradient_bounds (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds) (η : Mollifier) :
    ∃ R > 0, ∃ B ≥ 0, ∀ {Ω : Set Position}, IsOpen Ω → volume Ω ≠ ⊤ → ∀ {δ : ℝ}, 0 < δ →
      ∃ G : Position → Position, (∀ i, WeakPartialOn univ i (fun x => √(smoothedIndicator Ω η δ x))
        (fun x => G x i)) ∧ MemLp G 2 ∧
        (∀ᵐ x, ‖G x‖^2 ≤ (Metric.thickening (R*δ) (frontier Ω)).indicator (fun _ => B/δ^2) x) ∧
        (∫ x, ‖G x‖^2) ≤ B*regionVolume Ω/δ^2 := by
  classical
  let u := fun x => √(η.kernel x)
  obtain ⟨C,hC,htrans⟩ := (sob u (amplitude_L2 η.nonneg η.integrable)).1 η.sqrt_gradient
  obtain ⟨r,hr,hs⟩ := η.compact.isBounded.subset_ball_lt 0 (0 : Position)
  refine ⟨r+1,by positivity,3*C,by positivity,?_⟩
  intro Ω hΩ hv δ hδ
  let f := smoothedIndicator Ω η δ
  let w := fun x => √(η.scaled δ x)
  let v := fun x => √(f x)
  let S := Metric.thickening ((r+1)*δ) (frontier Ω)
  let K := S.indicator fun _ => C/δ^2
  obtain ⟨G,hw,hG⟩ := smoothedIndicator_sqrt_sobolev sob hΩ.measurableSet hv η hδ
  have hp (x : Position) : 0 ≤ f x := by
    change 0 ≤ ∫ y, Ω.indicator (fun _ => (1 : ℝ)) y * η.scaled δ (x-y)
    exact integral_nonneg fun _ => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg hδ.le _)) (η.nonneg _))
  have hi : Integrable (Ω.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff hΩ.measurableSet).2 (integrableOn_const hv)
  have hv2 : MemLp v 2 := amplitude_L2 hp (hi.integrable_convolution _ (η.scaled_integrable hδ))
  have amp (h : Position) : (∫ x, (w (x+h)-w x)^2) ≤ C/δ^2*‖h‖^2 := by
    calc
      _ = ∫ y, (u (y+δ⁻¹ • h)-u y)^2 := scale_amplitude_difference η hδ h
      _ ≤ C * ‖δ⁻¹ • h‖^2 := htrans _
      _ = _ := by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le),mul_pow,inv_pow]; ring
  have point (x : Position) : ∀ᶠ h in 𝓝 (0 : Position), (v (x+h)-v x)^2 ≤ K x * ‖h‖^2 := by
    by_cases hx : x ∈ S
    · apply Eventually.of_forall
      intro h
      simpa only [K,indicator_of_mem hx] using (pointwise_cutoff_difference hΩ.measurableSet η hδ x h).trans (amp h)
    · filter_upwards [cutoff_local_constant hΩ η hr hδ (subset_tsupport η.kernel |>.trans hs) hx] with h he
      simp [K,hx,v,f,he]
  refine ⟨G,hw,hG,?_,?_⟩
  · filter_upwards [quant.pointwise v G hv2 hw hG K point] with x hx
    change ‖G x‖^2 ≤ S.indicator (fun _ => 3*C/δ^2) x
    by_cases h : x ∈ S
    · simpa only [K,indicator_of_mem h,mul_div_assoc] using hx
    · simpa only [K,indicator_of_notMem h,mul_zero] using hx
  · have globalBound (h : Position) : (∫ x, (v (x+h)-v x)^2) ≤ (regionVolume Ω*(C/δ^2))*‖h‖^2 := by
      apply (cutoff_translation_energy hΩ.measurableSet hv η hδ h).trans
      exact (mul_le_mul_of_nonneg_left (amp h) ENNReal.toReal_nonneg).trans_eq (mul_assoc _ _ _).symm
    exact (quant.integral v G hv2 hw hG _ globalBound).trans_eq (by ring)

end TSGA.SSW
