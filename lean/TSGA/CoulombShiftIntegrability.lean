import TSGA.CoulombLatticeMixture

/-! # Integrability for physical Coulomb tilings

The Coulomb potential on the unit ball is integrable. Splitting at unit
distance gives absolute integrability of the direct kernel for every
bounded, integrable charge used in the tile construction.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization Set Metric
open scoped InnerProductSpace

theorem measurable_smoothedRegion {Ω : Set Position} (hΩ : MeasurableSet Ω)
    (η : Mollifier) {d : ℝ} (hd : 0 < d) : Measurable (smoothedIndicator Ω η d) := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let χ := Ω.indicator (fun _ => (1:ℝ))
  let K := η.scaled d
  have hi := (η.scaled_integrable hd).aestronglyMeasurable
  let k := hi.mk K
  have hk : Measurable k := hi.stronglyMeasurable_mk.measurable
  have hm : Measurable (fun z : Position × Position => χ z.2 * k (z.1-z.2)) :=
    ((measurable_const.indicator hΩ).comp measurable_snd).mul (hk.comp (measurable_fst.sub measurable_snd))
  convert hm.stronglyMeasurable.integral_prod_right' (ν := volume) |>.measurable using 1
  funext x
  apply integral_congr_ae
  have he := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp hi.ae_eq_mk
  filter_upwards [he] with y hy
  exact congrArg (fun a => χ y*a) hy

theorem compact_smoothedRegion {Ω : Set Position} (hΩ : Bornology.IsBounded Ω)
    (η : Mollifier) {d : ℝ} (hd : 0 < d) :
    ∃ B : ℝ, ∀ x, smoothedIndicator Ω η d x ≠ 0 → ‖x‖ ≤ B := by
  classical
  obtain ⟨A,_,ha⟩ := hΩ.subset_ball_lt 0 (0 : Position)
  obtain ⟨B,_,hb⟩ := η.compact.isBounded.subset_ball_lt 0 (0 : Position)
  refine ⟨A+B*d,?_⟩
  intro x hx
  change (∫ y, Ω.indicator (fun _ => (1:ℝ)) y * η.scaled d (x-y)) ≠ 0 at hx
  obtain ⟨y,hy⟩ := exists_ne_zero_of_integral_ne_zero hx
  have hyΩ : y ∈ Ω := by by_contra h; exact hy (by simp [h])
  have hk : η.kernel (d⁻¹ • (x-y)) ≠ 0 := fun hz => hy (by simp [Mollifier.scaled,hz])
  have h := mem_ball.mp (hb (subset_tsupport η.kernel hk))
  simp only [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le),← div_eq_inv_mul] at h
  have hy' : ‖y‖ < A := by simpa [mem_ball] using ha hyΩ
  have hxy := (div_lt_iff₀ hd).mp h
  calc
    ‖x‖ = ‖y + (x-y)‖ := by congr 1; abel
    _ ≤ ‖y‖+‖x-y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hy'.le hxy.le

private theorem directKernel_cutoff {f : Position → ℝ} (hm : Measurable f) (hi : Integrable f)
    (hb : ∀ x, f x ∈ Icc 0 1) : Integrable (directKernel f f) pairVolume := by
  classical
  let k := (ball (0 : Position) 1).indicator (fun z => ‖z‖⁻¹)
  have hk : Integrable k := by
    apply (integrable_indicator_iff measurableSet_ball).2
    apply integrableOn_ball_of_norm_le_rpow (α := 1) (C := 1)
      (by simp [finrank_euclideanSpace]) (by simp [finrank_euclideanSpace])
    · exact ae_of_all _ fun y => by simp [Real.rpow_neg_one]
    · exact continuous_norm.measurable.inv.aestronglyMeasurable
  have hnear := (measurePreserving_sub_prod (volume : Measure Position) (volume : Measure Position)).integrable_comp_of_integrable (hk.mul_prod hi)
  have hfar := hi.mul_prod hi
  have hme : Measurable (directKernel f f) :=
    ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).div (measurable_fst.sub measurable_snd).norm
  apply (hnear.add hfar).mono' hme.aestronglyMeasurable
  filter_upwards with z
  change ‖f z.1*f z.2/‖z.1-z.2‖‖ ≤ k (z.1-z.2)*f z.2 + f z.1*f z.2
  have hpos := mul_nonneg (hb z.1).1 (hb z.2).1
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hpos (norm_nonneg _))]
  by_cases h : z.1-z.2 ∈ ball (0 : Position) 1
  · rw [show k (z.1-z.2) = ‖z.1-z.2‖⁻¹ by simp [k,h]]
    have hle := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hb z.2).1 (hb z.1).2)
      (inv_nonneg.mpr (norm_nonneg (z.1-z.2)))
    rw [div_eq_mul_inv]
    linarith [mul_comm (f z.2) ‖z.1-z.2‖⁻¹]
  · have hn : 1 ≤ ‖z.1-z.2‖ := le_of_not_gt (fun hl => h (mem_ball_zero_iff.mpr hl))
    simpa [k,h] using div_le_self hpos hn

/-- A bounded open region smoothed with the specified mollifier gives a
Borel, integrable and boundedly supported matrix field. Its physical charge
has an absolutely integrable direct Coulomb kernel. -/
theorem cutoffSpiral_source_data {Ω : Set Position} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (η : Mollifier) {d : ℝ} (hd : 0 < d) (M : SpinMatrix) (q : Position) :
    let F := cutoffSpiral (smoothedIndicator Ω η d) M q
    let r := fun x => (F x).trace.re
    (∀ i j, Measurable (fun x => F x i j)) ∧ (∀ i j, Integrable (fun x => F x i j)) ∧
      (∃ B : ℝ, ∀ x, F x ≠ 0 → ‖x‖ ≤ B) ∧ Integrable (directKernel r r) pairVolume := by
  classical
  intro F r
  let f := smoothedIndicator Ω η d
  have hf := measurable_smoothedRegion hΩ η hd
  have hh := smoothedIndicator_bounds Ω η hd
  have hχ : Integrable (Ω.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hΩ).2 (integrableOn_const hb.measure_lt_top.ne)
  have hi : Integrable f := hχ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (η.scaled_integrable hd)
  have hm (i j : Fin 2) : Measurable (fun x => F x i j) := by
    dsimp only [F,cutoffSpiral,Matrix.smul_apply,smul_eq_mul]
    simp_rw [rotate_by_entry]
    apply (Complex.measurable_ofReal.comp hf).mul
    unfold phaseFactor
    fun_prop
  refine ⟨hm,?_,?_,?_⟩
  · intro i j
    apply (hi.mul_const ‖M i j‖).mono' (hm i j).aestronglyMeasurable
    filter_upwards with x
    simp [F,f,cutoffSpiral,rotate_by_entry,phaseFactor,Complex.norm_exp,abs_of_nonneg (hh x).1]
  · obtain ⟨B,hB⟩ := compact_smoothedRegion hb η hd
    exact ⟨B, fun x hx => hB x fun h => hx (by simp [F,cutoffSpiral,h])⟩
  · apply ((directKernel_cutoff hf hi hh).mul_const (M.trace.re^2)).congr
    filter_upwards with z
    simp [r,F,cutoffSpiral,directKernel,Matrix.trace_smul]
    ring

private theorem boundedBlock_energy_measurable (borel : LevyLiebBorel)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    {D : Position → SpinMatrix} (hmD : ∀ i j, Measurable (fun x => D x i j))
    (hD : ∀ i j, Integrable (fun x => D x i j)) (p : Option LatticeTile) :
    Measurable (fun τ => energy (latticeBlockDensity ℓ δ η R D τ p)) := by
  let w := fun τ x => latticeBlock ℓ δ η p (R x-τ)
  have hw : Measurable (fun z : Position × Position => w z.1 z.2) :=
    (latticeBlock_measurable ℓ hδ η p).comp ((R.continuous.measurable.comp measurable_snd).sub measurable_fst)
  have hm (i j : Fin 2) : Measurable (fun z : Position × Position => latticeBlockDensity ℓ δ η R D z.1 p z.2 i j) :=
    (Complex.measurable_ofReal.comp hw).mul ((hmD i j).comp measurable_snd)
  apply measurable_coulomb_energy_family borel _ hm
  intro τ i j
  apply memLp_one_iff_integrable.mpr
  apply ((hD i j).norm.const_mul 2).mono' ((hm i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards with x
  have hp := latticeBlock_bounds hδ hscale hs p (R x-τ)
  change ‖(w τ x:ℂ)*D x i j‖ ≤ 2*‖D x i j‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.1]
  exact mul_le_mul_of_nonneg_right hp.2 (norm_nonneg _)

private theorem constrainedSearch_nonneg (F : Position → SpinMatrix) : 0 ≤ levyLieb F := by
  classical
  by_cases h : ∃ Γ, feasible F Γ
  · exact le_levyLieb h fun Γ _ => add_nonneg Γ.kinetic_nonneg Γ.interaction_nonneg
  · have hset : {e | ∃ Γ : MixedState, feasible F Γ ∧ e = Γ.kinetic + Γ.interaction} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro e ⟨Γ,hΓ,_⟩
      exact h ⟨Γ,hΓ⟩
    simp [levyLieb,hset]

/-- A single parent direct kernel controls all of the fixed-scale lower
bounds. Only finiteness of this bound is needed for shift integrability. -/
theorem windowed_field_energy_floor (D : Position → SpinMatrix) :
    let r := fun x => (D x).trace.re
    Integrable (directKernel r r) pairVolume → ∃ C : ℝ, ∀ (w : Position → ℝ), Measurable w →
      (∀ x, w x ∈ Icc 0 2) → -C ≤ energy (fun x => (w x : ℂ) • D x) := by
  intro r hr
  let k := directKernel r r
  refine ⟨(∫ z, 4*‖k z‖ ∂pairVolume)/2,?_⟩
  intro w hw bound
  let F := fun x => (w x : ℂ) • D x
  let g := fun x => (F x).trace.re
  have hg (x : Position) : g x = w x*r x := by simp [g,F,r,Matrix.trace_smul]
  have he (z : PairSpace) : directKernel g g z = w z.1*w z.2*k z := by simp [k,directKernel,hg]; ring
  have hm : AEStronglyMeasurable (directKernel g g) pairVolume := by
    simp_rw [funext he]
    exact ((hw.comp measurable_fst).mul (hw.comp measurable_snd)).aestronglyMeasurable.mul hr.aestronglyMeasurable
  have hnorm (z : PairSpace) : ‖directKernel g g z‖ ≤ 4*‖k z‖ := by
    have h₁ := bound z.1
    have h₂ := bound z.2
    rw [he,norm_mul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h₁.1 h₂.1)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (mul_le_mul h₁.2 h₂.2 h₂.1 (by norm_num)).trans_eq (by norm_num)
  have hi := (hr.norm.const_mul 4).mono' hm (ae_of_all _ hnorm)
  have hh := integral_mono_ae hi (hr.norm.const_mul 4)
    (ae_of_all _ fun z => (le_abs_self _).trans (hnorm z))
  have hf := constrainedSearch_nonneg F
  change -_ ≤ levyLieb F - hartree g
  rw [hartree_eq_pair _ hi]
  linarith

private theorem latticeBlock_energy_floor {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    (D : Position → SpinMatrix) :
    let r := fun x => (D x).trace.re
    Integrable (directKernel r r) pairVolume → ∃ C : ℝ, ∀ τ p, -C ≤ energy (latticeBlockDensity ℓ δ η R D τ p) := by
  intro r hr
  obtain ⟨C,hC⟩ := windowed_field_energy_floor D hr
  exact ⟨C,fun τ p => hC _ ((latticeBlock_measurable ℓ hδ η p).comp (R.continuous.measurable.sub_const τ))
    (fun x => latticeBlock_bounds hδ hscale hs p (R x-τ))⟩

/-- A shift-dependent upper error with integrable mean controls the energy
of any single block, in particular the skeleton. -/
theorem latticeBlock_integrable_of_upper (borel : LevyLiebBorel)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    {D : Position → SpinMatrix} (hmD : ∀ i j, Measurable (fun x => D x i j))
    (hD : ∀ i j, Integrable (fun x => D x i j)) (p : Option LatticeTile)
    (hr : Integrable (directKernel (fun x => (D x).trace.re) (fun x => (D x).trace.re)) pairVolume)
    {G : Position → ℝ} (hG : Integrable G (latticeShiftMeasure ℓ))
    (hupper : ∀ᵐ τ ∂latticeShiftMeasure ℓ, energy (latticeBlockDensity ℓ δ η R D τ p) ≤ G τ) :
    Integrable (fun τ => energy (latticeBlockDensity ℓ δ η R D τ p)) (latticeShiftMeasure ℓ) := by
  let : IsProbabilityMeasure (latticeShiftMeasure ℓ) := latticeShiftMeasure_probability (by linarith)
  obtain ⟨C,hC⟩ := latticeBlock_energy_floor hδ hscale hs R D hr
  exact integrable_of_le_of_le (boundedBlock_energy_measurable borel hδ hscale hs R hmD hD p).aestronglyMeasurable
    (ae_of_all _ fun τ => hC τ p) hupper (integrable_const (-C)) hG

theorem latticeBlockEnergySum_integrable_of_upper (borel : LevyLiebBorel)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    {D : Position → SpinMatrix} (hmD : ∀ i j, Measurable (fun x => D x i j))
    (hD : ∀ i j, Integrable (fun x => D x i j))
    (hcompact : ∃ B : ℝ, ∀ x, D x ≠ 0 → ‖x‖ ≤ B)
    (hr : Integrable (directKernel (fun x => (D x).trace.re) (fun x => (D x).trace.re)) pairVolume)
    {G : Position → ℝ} (hG : Integrable G (latticeShiftMeasure ℓ))
    (hupper : ∀ᵐ τ ∂latticeShiftMeasure ℓ, latticeBlockEnergySum ℓ δ η R D τ ≤ G τ) :
    Integrable (latticeBlockEnergySum ℓ δ η R D) (latticeShiftMeasure ℓ) := by
  classical
  have hℓ : 0 < ℓ := by linarith
  let : IsProbabilityMeasure (latticeShiftMeasure ℓ) := latticeShiftMeasure_probability hℓ
  obtain ⟨C,hC⟩ := latticeBlock_energy_floor hδ hscale hs R D hr
  obtain ⟨B,hB⟩ := hcompact
  obtain ⟨T,hT⟩ := latticeWindow_finite_range hℓ hδ hs B
  let b := fun p τ => energy (latticeBlockDensity ℓ δ η R D τ p)
  have hm (p : Option LatticeTile) : Measurable (b p) := boundedBlock_energy_measurable borel hδ hscale hs R hmD hD p
  let s := fun τ => b none τ + ∑ p ∈ T, b (some p) τ
  have he : s =ᵐ[latticeShiftMeasure ℓ] latticeBlockEnergySum ℓ δ η R D := by
    filter_upwards [ae_latticeShift_mem ℓ] with τ hτ
    apply congrArg ((b none τ)+·)
    refine (tsum_eq_sum (s := T) (fun p hp => ?_)).symm
    change energy (latticeBlockDensity ℓ δ η R D τ (some p)) = 0
    suffices h : latticeBlockDensity ℓ δ η R D τ (some p) = 0 by rw [h,energy_vacuum]
    funext x
    by_cases hx : D x = 0
    · simp [latticeBlockDensity,hx]
    · simp [latticeBlockDensity,latticeBlock,hT R τ hτ x (hB x hx) p hp]
  have hlo (τ : Position) : -C + T.card • (-C) ≤ s τ := by
    have h := Finset.sum_le_sum (s := T) (fun p _ => hC τ (some p))
    exact add_le_add (hC τ none) (by simpa only [Finset.sum_const] using h)
  apply integrable_of_le_of_le (((hm none).add (Finset.measurable_fun_sum T fun p _ => hm (some p))).aestronglyMeasurable.congr he)
    (he.mono fun τ h => (hlo τ).trans_eq h) hupper (integrable_const _) hG

end TSGA.ManyBody
