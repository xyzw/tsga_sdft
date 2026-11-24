import TSGA.CoulombCutoffArea
import TSGA.IslandTetraProfiles
import Mathlib.Analysis.Calculus.Rademacher

/-! # Fisher integrals of the three deterministic single-island profiles

Both square roots of a smoothed indicator have a Lipschitz bound from the
translation estimate on the mollifier amplitude. Only a tetrahedral shell
contributes to the outer derivative. The smooth core has a Dirichlet cost proportional to its radius.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory MeasureTheory.Measure Filter SSW Metric Set
open scoped Topology NNReal Convolution

private def direction (i : Fin 3) : Position := PiLp.single 2 i 1

private theorem weak_line {f : Position → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (i : Fin 3) :
    WeakPartialOn univ i f (fun x => lineDeriv ℝ f x (direction i)) := by
  refine ⟨locallyIntegrableOn_univ.mpr hf.continuous.locallyIntegrable,
    locallyIntegrableOn_univ.mpr (hf.locallyIntegrable_lineDeriv _),?_⟩
  intro ψ hψ hc _
  obtain ⟨K,hK⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have h := hf.integral_lineDeriv_mul_eq (μ := volume) hK hc (direction i)
  simp_rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv] at h
  simp only [map_neg,neg_mul,integral_neg] at h
  simp only [Measure.restrict_univ,smul_eq_mul,direction] at *
  simpa only [show ∀ x, ψ x*lineDeriv ℝ f x (PiLp.single 2 i 1) = lineDeriv ℝ f x (PiLp.single 2 i 1)*ψ x from fun _ => mul_comm _ _,neg_neg] using congrArg Neg.neg h.symm

private theorem lipschitz_shell {f : Position → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {S : Set Position} (hs : MeasurableSet S) (hfin : volume S ≠ ⊤)
    (flat : ∀ x ∉ S, ∃ c : ℝ, f =ᶠ[𝓝 x] (fun _ => c)) :
    ∃ g : Position → Fin 3 → ℝ, (∀ i, WeakPartialOn univ i f (fun x => g x i)) ∧
      Integrable (fun x => ∑ i, (g x i)^2) ∧
      (∫ x, ∑ i, (g x i)^2) ≤ 3*(L:ℝ)^2*volume.real S := by
  let g := fun x i => lineDeriv ℝ f x (direction i)
  let U := S.indicator fun _ => 3*(L:ℝ)^2
  have hi : Integrable U := (integrable_indicator_iff hs).2 (integrableOn_const hfin)
  have bound (x : Position) : ∑ i, (g x i)^2 ≤ U x := by
    by_cases hx : x ∈ S
    · rw [show U x = 3*(L:ℝ)^2 from indicator_of_mem hx _]
      have h (i : Fin 3) : (g x i)^2 ≤ (L:ℝ)^2 := by
        have d : ‖g x i‖ ≤ (L:ℝ) := by simpa [g,direction] using
          (norm_lineDeriv_le_of_lipschitz ℝ hf (x₀ := x) (v := direction i))
        simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) d 2
      exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)).trans_eq (by simp)
    · obtain ⟨c,eq⟩ := flat x hx
      have z (i : Fin 3) : g x i = 0 := by
        change lineDeriv ℝ f x _ = _
        rw [eq.lineDeriv_eq]; simp [lineDeriv]
      simp [z,U,hx]
  have H := hi.mono' (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    ((hf.memLp_lineDeriv (μ := volume) (direction i)).1.aemeasurable.pow_const (2:ℕ)).aestronglyMeasurable)
    (ae_of_all _ (fun x => (Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (g x i))).le.trans (bound x)))
  refine ⟨g,weak_line hf,H,(integral_mono H hi bound).trans_eq ?_⟩
  simp [U,integral_indicator_const,hs,smul_eq_mul,mul_comm]

/-- The translation argument uses the reverse triangle inequality in
L² of any measurable subset, including the unbounded complement. -/
theorem smoothedRootLipschitz (sob : SobolevDifferenceQuotients) (η : Mollifier) :
    ∃ A ≥ 0, ∀ (Ω : Set Position), MeasurableSet Ω → ∀ {δ : ℝ}, 0 < δ →
      LipschitzWith (Real.toNNReal (A/δ)) (fun x => √(smoothedIndicator Ω η δ x)) := by
  let u := fun x => √(η.kernel x)
  obtain ⟨C,hC,htrans⟩ := (sob u (amplitude_L2 η.nonneg η.integrable)).1 η.sqrt_gradient
  refine ⟨√C,Real.sqrt_nonneg _,?_⟩
  intro Ω hm δ hd
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let w := fun x => √(η.scaled δ x)
  have hn (y) : 0 ≤ η.scaled δ y := mul_nonneg (inv_nonneg.mpr (pow_nonneg hd.le _)) (η.nonneg _)
  have hw : MemLp w 2 := amplitude_L2 hn (η.scaled_integrable hd)
  have hx (z : Position) : MemLp (fun y => w (z-y)) 2 (volume.restrict Ω) :=
    (hw.comp_measurePreserving (measurePreserving_sub_left volume z)).restrict _
  have mass (z : Position) : (∫ y in Ω, w (z-y)^2) = smoothedIndicator Ω η δ z := by
    simp_rw [show ∀ t, w t^2 = η.scaled δ t from fun t => Real.sq_sqrt (hn t)]
    exact (convolution_restrict Ω hm _ z).symm
  apply LipschitzWith.of_dist_le_mul
  intro b a
  let h := b-a
  let v := fun y => (w (y+h)-w y)^2
  have hi : Integrable v := ((hw.comp_measurePreserving (measurePreserving_add_right volume h)).sub hw).integrable_sq
  have H : (√(smoothedIndicator Ω η δ b)-√(smoothedIndicator Ω η δ a))^2 ≤ ∫ y, v y := by
    rw [← mass,← mass]
    calc
      _ ≤ ∫ y in Ω, v (a-y) := by
        simpa only [v,h,show ∀ y : Position, a-y+(b-a) = b-y from fun _ => by abel] using norm_difference (hx b) (hx a)
      _ ≤ ∫ y, v (a-y) := setIntegral_le_integral (hi.comp_sub_left a) (ae_of_all _ fun _ => sq_nonneg _)
      _ = _ := integral_sub_left_eq_self v volume a
  have scale := scale_amplitude_difference η hd h
  change (∫ y, v y) = _ at scale
  rw [scale] at H
  have t := H.trans (htrans (δ⁻¹ • h))
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le),mul_pow] at t
  rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ (div_nonneg (Real.sqrt_nonneg _) hd.le)]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hd.le) (norm_nonneg _))).mp
  rw [sq_abs,mul_pow,div_pow,Real.sq_sqrt hC]
  simpa only [h,inv_pow,div_eq_mul_inv,mul_assoc] using t

private theorem cutoff_compl (Ω : Set Position) (hm : MeasurableSet Ω) (η : Mollifier) {δ : ℝ}
    (hd : 0 < δ) (x : Position) :
    smoothedIndicator Ωᶜ η δ x = 1 - smoothedIndicator Ω η δ x := by
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  change (_ ⋆ _) x = 1-(_ ⋆ _) x
  rw [convolution_restrict Ωᶜ hm.compl,convolution_restrict Ω hm]
  have H := integral_add_compl hm ((η.scaled_integrable hd).comp_sub_left x)
  rw [integral_sub_left_eq_self (η.scaled δ) volume x,η.scaled_mass hd] at H
  linarith only [H]

theorem islandExteriorSingleFisher (sob : SobolevDifferenceQuotients) (η : Mollifier)
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) :
    ∃ C ≥ 0, ∀ {r δ : ℝ}, 0 < δ → δ ≤ r/2 →
      ∃ g : Position → Fin 3 → ℝ, (∀ i, WeakPartialOn univ i
        (fun x => √(1-smoothedIndicator (tetrahedron r) η δ x)) (fun x => g x i)) ∧
        Integrable (fun x => ∑ i, (g x i)^2) ∧ (∫ x, ∑ i, (g x i)^2) ≤ C*r^2/δ := by
  obtain ⟨A,hA,lip⟩ := smoothedRootLipschitz sob η
  refine ⟨3*A^2,by positivity,?_⟩
  intro r δ hd hw
  have hr : 0 < r := by linarith
  let outer := tetrahedron (r+δ)
  let inner := tetrahedron (r-δ)
  let S := outer \ inner
  have hpos : 0 < r-δ := by linarith
  have hfin : volume outer ≠ ⊤ := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos (add_pos hr hd))).2.ne
  have mi := (tetrahedron_open (r-δ)).measurableSet
  have mo := (tetrahedron_open (r+δ)).measurableSet
  have l := lip (tetrahedron r)ᶜ (tetrahedron_open r).measurableSet.compl hd
  simp only [cutoff_compl _ (tetrahedron_open r).measurableSet η hd] at l
  have flat (x : Position) (hx : x ∉ S) : ∃ c : ℝ, (fun t => √(1-smoothedIndicator (tetrahedron r) η δ t)) =ᶠ[𝓝 x] fun _ => c := by
    by_cases h : x ∈ inner
    · refine ⟨0,?_⟩
      filter_upwards [(tetrahedron_open _).mem_nhds h] with y hy
      have v : smoothedIndicator (tetrahedron r) η δ y = 1 := by
        apply smoothed_eq_one hs hd
        intro z hz
        apply tetrahedron_mono (show (r-δ)+16*(δ/16) ≤ r by linarith)
        exact tetrahedron_enlarge hy (by linarith [mem_closedBall.mp hz,dist_comm z y])
      simp [v]
    · have out : x ∉ outer := fun o => hx ⟨o,h⟩
      refine ⟨1,?_⟩
      filter_upwards [ball_mem_nhds x (show 0 < δ/100 by positivity)] with y hy
      have v : smoothedIndicator (tetrahedron r) η δ y = 0 := by
        by_contra hn
        obtain ⟨z,hz,hyz⟩ := smoothed_support_witness hs hd hn
        apply out
        apply tetrahedron_mono (show r+16*(δ/16) ≤ r+δ by linarith)
        exact tetrahedron_enlarge hz (by linarith [dist_triangle z y x,dist_comm z y,mem_ball.mp hy])
      simp [v]
  obtain ⟨g,w,i,b⟩ := lipschitz_shell l (mo.diff mi) (measure_ne_top_of_subset sdiff_subset hfin) flat
  have vol : volume.real S ≤ r^2*δ := by
    rw [show volume.real S = volume.real outer-volume.real inner from measureReal_sdiff
      (μ := volume) (tetrahedron_mono (by linarith)) mi hfin]
    change regionVolume (tetrahedron (r+δ)) - regionVolume (tetrahedron (r-δ)) ≤ _
    rw [tetrahedron_volume (add_pos hr hd),tetrahedron_volume hpos]
    have dd := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le (by linarith : δ ≤ r) 2) hd.le
    nlinarith only [dd,mul_nonneg (sq_nonneg r) hd.le]
  refine ⟨g,w,i,b.trans ?_⟩
  rw [Real.coe_toNNReal _ (div_nonneg hA hd.le)]
  apply (mul_le_mul_of_nonneg_left vol (by positivity : 0 ≤ 3*(A/δ)^2)).trans_eq
  field_simp

theorem islandLayerSingleFisher (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (η : Mollifier) :
    ∃ C ≥ 0, ∀ {r δ : ℝ}, 0 < δ → δ ≤ r/2 →
      ∃ g : Position → Fin 3 → ℝ, (∀ i, WeakPartialOn univ i
        (fun x => √(smoothedIndicator (tetrahedron (r-δ)) η δ x)) (fun x => g x i)) ∧
        Integrable (fun x => ∑ i, (g x i)^2) ∧ (∫ x, ∑ i, (g x i)^2) ≤ C*r^2/δ := by
  obtain ⟨C,hC,H⟩ := tileCutoffAreaBound_of_sobolev sob quant η
  refine ⟨C,hC,?_⟩
  intro r δ hd hw
  have hi : 0 < r-δ := by linarith
  obtain ⟨g,w,mem,bd⟩ := H (r-δ) δ hi hd
  refine ⟨fun x i => g x i,w,?_,?_⟩
  · simpa only [← EuclideanSpace.real_norm_sq_eq] using mem.integrable_norm_pow (p := 2) (by decide)
  · simp only [← EuclideanSpace.real_norm_sq_eq]
    apply bd.trans
    rw [tetrahedron_volume hi,div_le_div_iff₀ (mul_pos hi hd) hd]
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi.le (by linarith : r-δ ≤ r) 2)
      (mul_nonneg (mul_nonneg hC hd.le) hi.le)
    nlinarith only [h,mul_nonneg (mul_nonneg (mul_nonneg hC hd.le) hi.le) (sq_nonneg r)]



theorem islandCoreSingleFisher :
    ∃ C ≥ 0, ∀ {r : ℝ}, 0 < r →
      ∃ g : Position → Fin 3 → ℝ, (∀ i, WeakPartialOn univ i
        (fun x => √(islandCore r x)) (fun x => g x i)) ∧
        Integrable (fun x => ∑ i, (g x i)^2) ∧ (∫ x, ∑ i, (g x i)^2) ≤ C*r := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport islandCoreBump.hasCompactSupport
    (islandCoreBump.contDiff (n := 1)) one_ne_zero
  refine ⟨3*(L:ℝ)^2,by positivity,?_⟩
  intro r hr
  have root (x : Position) : √(islandCore r x) = islandCoreBump (r⁻¹ • x) :=
    Real.sqrt_sq islandCoreBump.nonneg
  have l : LipschitzWith (Real.toNNReal ((L:ℝ)/r)) (fun x => √(islandCore r x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [root,root,Real.coe_toNNReal _ (div_nonneg L.coe_nonneg hr.le)]
    apply (hL.dist_le_mul _ _).trans_eq
    rw [dist_smul₀,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    ring
  have flat (x : Position) (hx : x ∉ tetrahedron r) :
      ∃ c : ℝ, (fun t => √(islandCore r t)) =ᶠ[𝓝 x] fun _ => c := by
    have nx : r/64 < ‖x‖ := by
      by_contra! h
      have hc (j : Fin 3) : |x j| ≤ r/64 := by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x j).trans h
      have a := abs_le.mp (hc 0)
      have b := abs_le.mp (hc 1)
      exact hx ⟨by linarith [hc 2],by linarith,by linarith⟩
    refine ⟨0,?_⟩
    have ev : ∀ᶠ y in 𝓝 x, r/128 < ‖y‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith))
    filter_upwards [ev] with y hy
    rw [root]
    apply islandCoreBump.zero_of_le_dist
    change 1/128 ≤ dist (r⁻¹ • y) 0
    rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),← div_eq_inv_mul,le_div_iff₀ hr]
    linarith
  obtain ⟨g,w,i,b⟩ := lipschitz_shell l (tetrahedron_open r).measurableSet
    (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos hr)).2.ne flat
  refine ⟨g,w,i,b.trans ?_⟩
  rw [Real.coe_toNNReal _ (div_nonneg L.coe_nonneg hr.le)]
  change _*regionVolume (tetrahedron r) ≤ _
  rw [tetrahedron_volume hr]
  field_simp
  nlinarith only [mul_nonneg (sq_nonneg (L:ℝ)) (pow_nonneg hr.le 3)]



/-- Stationary placement of a deterministic Fisher density. The norm of a
spatial gradient is invariant under the orthogonal part of the chart. -/
theorem StationaryIslandPlacements.fisher {Z : Type*} [MeasurableSpace Z] {ι : Measure Z} {κ : ℝ}
    (T : StationaryIslandPlacements ι κ) (hκ : 0 ≤ κ) (g : Position → Fin 3 → ℝ)
    (single : Z → Position → Fin 3 → ℝ) (hg : Integrable fun x => ∑ i, (g x i)^2)
    (iso : ∀ x, ∀ᵐ z ∂ι, (∑ i, (single z x i)^2) = ∑ i, (g (T.chart z x) i)^2) (x : Position) :
    Integrable (fun z => ∑ i, (single z x i)^2) ι ∧
      (∫ z, ∑ i, (single z x i)^2 ∂ι) = κ*(∫ y, ∑ i, (g y i)^2) := by
  let f := fun y => ∑ i, (g y i)^2
  have W := T.stationary x
  have hi : Integrable f (ENNReal.ofReal κ • volume) := hg.smul_measure ENNReal.ofReal_ne_top
  have hj : Integrable f (Measure.map (fun z => T.chart z x) ι) := W.map_eq ▸ hi
  have M := integral_map W.measurable.aemeasurable hj.1
  refine ⟨(W.integrable_comp_of_integrable hi).congr ((iso x).mono (fun _ h => h.symm)),?_⟩
  rw [integral_congr_ae (iso x),← M,W.map_eq,integral_smul_measure,ENNReal.toReal_ofReal hκ]
  rfl

/-- The deterministic derivative and its energy under all rigid transports
of its coordinates. -/
structure PlacedProfileFisher {Z : Type*} [MeasurableSpace Z] {ι : Measure Z} {κ : ℝ}
    (T : StationaryIslandPlacements ι κ) (f : Position → ℝ) (ceiling : ℝ) where
  gradient : Position → Fin 3 → ℝ
  weak : ∀ i, WeakPartialOn univ i f (fun x => gradient x i)
  transported : ∀ (single : Z → Position → Fin 3 → ℝ),
    (∀ x, ∀ᵐ z ∂ι, (∑ i, (single z x i)^2) = ∑ i, (gradient (T.chart z x) i)^2) →
    ∀ x, Integrable (fun z => ∑ i, (single z x i)^2) ι ∧ (∫ z, ∑ i, (single z x i)^2 ∂ι) ≤ ceiling

/-- The constants in all three single-mark intensity bounds are uniform
in the radius and the smoothing width. -/
theorem islandPlacedFisher (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) :
    ∃ A ≥ 0, ∀ {Z : Type*} [MeasurableSpace Z] {ι : Measure Z} {v r δ : ℝ}, 0 < v → 0 < δ → δ ≤ r/2 →
      ∀ T : StationaryIslandPlacements ι (v/(r^3/24)),
      Nonempty (PlacedProfileFisher T (fun x => √(1-smoothedIndicator (tetrahedron r) η δ x)) (A*v/(r*δ))) ∧
      Nonempty (PlacedProfileFisher T (fun x => √(smoothedIndicator (tetrahedron (r-δ)) η δ x)) (A*v/(r*δ))) ∧
      Nonempty (PlacedProfileFisher T (fun x => √(islandCore r x)) (A*v*r⁻¹^2)) := by
  obtain ⟨a,ha,H⟩ := islandExteriorSingleFisher sob η hs
  obtain ⟨b,hb,J⟩ := islandLayerSingleFisher sob quant η
  obtain ⟨c,hc,U⟩ := islandCoreSingleFisher
  refine ⟨24*(a+b+c),by positivity,?_⟩
  intro Z _ ι v r δ hv hd hw T
  have hr : 0 < r := by linarith
  have vol : 0 < r^3/24 := by positivity
  obtain ⟨g₀,w₀,i₀,b₀⟩ := H hd hw
  obtain ⟨g₁,w₁,i₁,b₁⟩ := J hd hw
  obtain ⟨g₂,w₂,i₂,b₂⟩ := U hr
  have shell {g : Position → Fin 3 → ℝ} (ig : Integrable fun x => ∑ i, (g x i)^2)
      {d : ℝ} (cost : (∫ x, ∑ i, (g x i)^2) ≤ d*r^2/δ) (le : d ≤ a+b+c)
      (single : Z → Position → Fin 3 → ℝ)
      (iso : ∀ x, ∀ᵐ z ∂ι, (∑ i, (single z x i)^2) = ∑ i, (g (T.chart z x) i)^2) (x : Position) :
      Integrable (fun z => ∑ i, (single z x i)^2) ι ∧
      (∫ z, ∑ i, (single z x i)^2 ∂ι) ≤ 24*(a+b+c)*v/(r*δ) := by
    obtain ⟨i,w⟩ := T.fisher (div_nonneg hv.le vol.le) g single ig iso x
    refine ⟨i,?_⟩
    rw [w]
    have hbnd := cost.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right le (sq_nonneg _)) hd.le)
    apply (mul_le_mul_of_nonneg_left hbnd (div_nonneg hv.le vol.le)).trans_eq
    field_simp
  refine ⟨⟨⟨g₀,w₀,shell i₀ b₀ (by linarith)⟩⟩,⟨⟨g₁,w₁,shell i₁ b₁ (by linarith)⟩⟩,⟨⟨g₂,w₂,?_⟩⟩⟩
  intro single iso x
  obtain ⟨i,w⟩ := T.fisher (div_nonneg hv.le vol.le) g₂ single i₂ iso x
  refine ⟨i,?_⟩
  rw [w]
  apply (mul_le_mul_of_nonneg_left b₂ (div_nonneg hv.le vol.le)).trans
  have eq : v/(r^3/24)*(c*r) = 24*c*v*r⁻¹^2 := by field_simp
  rw [eq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hv.le) (sq_nonneg _)

end TSGA.ManyBody
