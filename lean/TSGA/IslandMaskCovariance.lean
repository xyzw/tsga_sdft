import TSGA.IslandMasks
import TSGA.IslandCoulombKernel
import TSGA.IslandShellCovariance

/-! # Pair statistics of the actual exterior, layer and core masks -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Islands Set

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ}

namespace IslandProfiles
variable (H : IslandProfiles P v)

def boundaryMark (x : Position) (i : Z) : ℝ := H.outer x i - H.layer x i

omit [IsProbabilityMeasure μ] in
theorem layer_le_outer (x : Position) (i : Z) : H.layer x i ≤ H.outer x i := by
  by_cases h : H.layer x i = 0
  · simpa only [h] using (H.outer_range x i).1
  · rw [H.layer_support x i h]; exact (H.layer_range x i).2

omit [IsProbabilityMeasure μ] in
theorem core_le_layer (x : Position) (i : Z) : H.inner x i ≤ H.layer x i := by
  by_cases h : H.inner x i = 0
  · simpa only [h] using (H.layer_range x i).1
  · rw [H.inner_support x i h]; exact (H.inner_range x i).2

omit [IsProbabilityMeasure μ] in
theorem boundaryMark_range (x : Position) (i : Z) : H.boundaryMark x i ∈ Icc 0 1 :=
  ⟨sub_nonneg.mpr (H.layer_le_outer x i), by unfold boundaryMark; linarith [(H.outer_range x i).2,(H.layer_range x i).1]⟩

omit [IsProbabilityMeasure μ] in
theorem boundaryMark_hits (x : Position) : Integrable (H.boundaryMark x) intensity ∧
    (∫ i, H.boundaryMark x i ∂intensity) = v-H.layerIntensity := by
  refine ⟨(H.outer_mass x).1.sub (H.layer_mass x).1,?_⟩
  exact (integral_sub (H.outer_mass x).1 (H.layer_mass x).1).trans (by rw [(H.outer_mass x).2,(H.layer_mass x).2])

private theorem product_int {f g : Z → ℝ} (hf : Integrable f intensity) (hg : Integrable g intensity)
    (rf : ∀ i, f i ∈ Icc 0 1) (rg : ∀ i, g i ∈ Icc 0 1) : Integrable (fun i => f i*g i) intensity := by
  apply hf.mono' (hf.1.mul hg.1)
  exact ae_of_all _ fun i => by
    change ‖f i * g i‖ ≤ f i
    rw [Real.norm_of_nonneg (mul_nonneg (rf i).1 (rg i).1)]
    exact mul_le_of_le_one_right (rf i).1 (rg i).2

omit [IsProbabilityMeasure μ] in
private theorem window_finite (f : IslandProfile Z) (x : Position)
    (hle : ∀ i, 0 ≤ f x i ∧ f x i ≤ H.outer x i) (ω : Ω) :
    (Function.mulSupport (fun n => 1-f x (P.mark ω n))).Finite := by
  apply H.finite_mulSupport f ω x
  intro i hi ho
  obtain ⟨h₁, h₂⟩ := hle i
  exact hi (by linarith)

private def overlap (f g : IslandProfile Z) (x y : Position) : ℝ := ∫ i, f x i*g y i ∂intensity

private theorem mask_pair {f g : IslandProfile Z} (x y : Position) {a b : ℝ}
    (hf : Integrable (f x) intensity) (hg : Integrable (g y) intensity)
    (ma : (∫ i, f x i ∂intensity) = a) (mb : (∫ i, g y i ∂intensity) = b)
    (rf : ∀ i, f x i ∈ Icc 0 1) (rg : ∀ i, g y i ∈ Icc 0 1)
    (fl : ∀ i, f x i ≤ H.outer x i) (gl : ∀ i, g y i ≤ H.outer y i) :
    Integrable (fun ω => P.uncovered f ω x * P.uncovered g ω y) μ ∧
    (∫ ω, P.uncovered f ω x * P.uncovered g ω y ∂μ) = Real.exp (-a)*Real.exp (-b)*Real.exp (overlap (intensity := intensity) f g x y) := by
  simpa only [PoissonIslandProcess.uncovered,ma,mb,neg_add,Real.exp_add,overlap] using
    P.pair_laplace _ _ hf hg (product_int hf hg rf rg) rf rg
      (H.window_finite f x (fun i => ⟨(rf i).1,fl i⟩)) (H.window_finite g y (fun i => ⟨(rg i).1,gl i⟩))

private theorem center_cov {f g : Ω → ℝ} {a b : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hab : Integrable (fun ω => f ω*g ω) μ) (ma : (∫ ω, f ω ∂μ) = a) (mb : (∫ ω, g ω ∂μ) = b) :
    (∫ ω, (a-f ω)*(b-g ω) ∂μ) = (∫ ω, f ω*g ω ∂μ)-a*b := by
  have pt (ω) : (a-f ω)*(b-g ω) = (f ω*g ω - a*g ω) - f ω*b + a*b := by ring
  simp_rw [pt]
  erw [integral_add ((hab.sub (hg.const_mul a)).sub (hf.mul_const b)) (integrable_const (a*b)),
      integral_sub (hab.sub (hg.const_mul _)) (hf.mul_const _),integral_sub hab (hg.const_mul _),
      integral_const_mul,integral_mul_const,ma,mb,integral_const]
  simp

private theorem mask_cov {f : IslandProfile Z} {m : ℝ} (hf : ∀ x, Integrable (f x) intensity ∧ (∫ i, f x i ∂intensity) = m)
    (rf : ∀ x i, f x i ∈ Icc 0 1) (fl : ∀ x i, f x i ≤ H.outer x i) (x y : Position) :
    (∫ ω, (Real.exp (-m)-P.uncovered f ω x)*(Real.exp (-m)-P.uncovered f ω y) ∂μ) ≤
    overlap (intensity := intensity) f f x y := by
  have mean (z : Position) := P.laplace _ (hf z).1 (rf z)
    (ae_of_all _ (H.window_finite f z fun i => ⟨(rf z i).1, fl z i⟩))
  have pair := H.mask_pair x y (hf x).1 (hf y).1 (hf x).2 (hf y).2 (rf x) (rf y) (fl x) (fl y)
  have ha z : (∫ ω, P.uncovered f ω z ∂μ) = Real.exp (-m) := (mean z).2.trans (by rw [(hf z).2])
  erw [center_cov (f := fun ω => P.uncovered f ω x) (g := fun ω => P.uncovered f ω y) (mean x).1 (mean y).1 pair.1 (ha x) (ha y), pair.2]
  apply le_of_eq_of_le (by ring : _ = Real.exp (-m)*Real.exp (-m)*Real.exp (overlap (intensity := intensity) f f x y)-Real.exp (-m)^2)
  apply oneMask_covariance_le (integral_nonneg (μ := intensity) fun i => mul_nonneg (rf x i).1 (rf y i).1)
  exact (integral_mono (product_int (hf x).1 (hf y).1 (rf x) (rf y)) (hf x).1
    (fun i => mul_le_of_le_one_right (rf x i).1 (rf y i).2)).trans_eq (hf x).2

theorem firstCovariance (x y : Position) :
    (∫ ω, (H.masks.first ω x-H.masks.meanFirst)*(H.masks.first ω y-H.masks.meanFirst) ∂μ) ≤
    markOverlap intensity (fun i x => H.layer x i) (fun i x => H.layer x i) (x,y) := by
  change (∫ ω, ((1-P.uncovered H.layer ω x)-coveredMean H.layerIntensity)*((1-P.uncovered H.layer ω y)-coveredMean H.layerIntensity) ∂μ) ≤ _
  simpa only [coveredMean,sub_sub_sub_cancel_left,markOverlap,overlap] using H.mask_cov H.layer_mass H.layer_range H.layer_le_outer x y

theorem coreCovariance (x y : Position) :
    (∫ ω, (H.masks.core ω x-H.masks.meanCore)*(H.masks.core ω y-H.masks.meanCore) ∂μ) ≤
    markOverlap intensity (fun i x => H.inner x i) (fun i x => H.inner x i) (x,y) := by
  change (∫ ω, ((1-P.uncovered H.inner ω x)-coveredMean H.innerIntensity)*((1-P.uncovered H.inner ω y)-coveredMean H.innerIntensity) ∂μ) ≤ _
  simpa only [coveredMean,sub_sub_sub_cancel_left,markOverlap,overlap] using H.mask_cov H.inner_mass H.inner_range
    (fun x i => (H.core_le_layer x i).trans (H.layer_le_outer x i)) x y

/-- The centred uncovered shell appearing in the charge decomposition. -/
def shellField (ω : Ω) (x : Position) : ℝ :=
  (1-Real.exp (-v)-H.masks.meanFirst) - (1-H.masks.outside ω x-H.masks.first ω x)

private theorem shell_identity (x y : Position) :
    (∫ ω, H.shellField ω x * H.shellField ω y ∂μ) =
      shellCovariance v H.layerIntensity
        (overlap (intensity := intensity) H.layer H.layer x y)
        (overlap (intensity := intensity) H.layer H.boundaryMark x y)
        (overlap (intensity := intensity) H.boundaryMark H.layer x y)
        (overlap (intensity := intensity) H.boundaryMark H.boundaryMark x y) := by
  let A := H.layer
  let U := H.outer
  let S := H.boundaryMark
  let a := Real.exp (-H.layerIntensity)
  let e := Real.exp (-v)
  let k (f g : IslandProfile Z) := overlap (intensity := intensity) f g x y
  have K (f g : IslandProfile Z) (hf : Integrable (f x) intensity) (hg : Integrable (g y) intensity)
      (rf : ∀ i, f x i ∈ Icc 0 1) (rg : ∀ i, g y i ∈ Icc 0 1) := product_int hf hg rf rg
  have AA := H.mask_pair x y (H.layer_mass x).1 (H.layer_mass y).1 (H.layer_mass x).2 (H.layer_mass y).2
    (H.layer_range x) (H.layer_range y) (H.layer_le_outer x) (H.layer_le_outer y)
  have AU := H.mask_pair x y (H.layer_mass x).1 (H.outer_mass y).1 (H.layer_mass x).2 (H.outer_mass y).2
    (H.layer_range x) (H.outer_range y) (H.layer_le_outer x) (fun _ => le_rfl)
  have UA := H.mask_pair x y (H.outer_mass x).1 (H.layer_mass y).1 (H.outer_mass x).2 (H.layer_mass y).2
    (H.outer_range x) (H.layer_range y) (fun _ => le_rfl) (H.layer_le_outer y)
  have UU := H.mask_pair x y (H.outer_mass x).1 (H.outer_mass y).1 (H.outer_mass x).2 (H.outer_mass y).2
    (H.outer_range x) (H.outer_range y) (fun _ => le_rfl) (fun _ => le_rfl)
  have hA z := P.laplace _ (H.layer_mass z).1 (H.layer_range z)
    (ae_of_all _ (H.window_finite H.layer z fun i => ⟨(H.layer_range z i).1, H.layer_le_outer z i⟩))
  have hU z := P.laplace _ (H.outer_mass z).1 (H.outer_range z)
    (ae_of_all _ (H.window_finite H.outer z fun i => ⟨(H.outer_range z i).1, le_rfl⟩))
  let F (z : Position) (ω : Ω) := P.uncovered A ω z - P.uncovered U ω z
  have hF (z : Position) : Integrable (F z) μ := (hA z).1.sub (hU z).1
  have mF (z : Position) : (∫ ω, F z ω ∂μ) = a-e := by
    dsimp only [F,A,U,PoissonIslandProcess.uncovered,a,e]
    rw [integral_sub (hA z).1 (hU z).1,(hA z).2,(hU z).2,(H.layer_mass z).2,(H.outer_mass z).2]
  have expand (ω : Ω) : F x ω * F y ω =
      ((P.uncovered A ω x * P.uncovered A ω y - P.uncovered A ω x * P.uncovered U ω y) -
        P.uncovered U ω x * P.uncovered A ω y) + P.uncovered U ω x * P.uncovered U ω y := by dsimp [F]; ring
  have hFF : Integrable (fun ω => F x ω * F y ω) μ := by
    simp_rw [expand]; exact ((AA.1.sub AU.1).sub UA.1).add UU.1
  have he (ω : Ω) (z : Position) : H.shellField ω z = (a-e)-F z ω := by
    change (1-Real.exp (-v)-(1-Real.exp (-H.layerIntensity))) -
      (1-P.uncovered H.outer ω z-(1-P.uncovered H.layer ω z)) = _
    dsimp [a,e,F,A,U]; ring
  have hright (f : IslandProfile Z) (hf : Integrable (f x) intensity) (rf : ∀ i, f x i ∈ Icc 0 1) :
      k f U = k f A + k f S := by
    change (∫ i, f x i * H.outer y i ∂intensity) = _ + _
    rw [show k f A + k f S = ∫ i, f x i*H.layer y i + f x i*H.boundaryMark y i ∂intensity from
      (integral_add (K f A hf (H.layer_mass y).1 rf (H.layer_range y))
        (K f S hf (H.boundaryMark_hits y).1 rf (H.boundaryMark_range y))).symm]
    apply integral_congr_ae; filter_upwards with i; unfold boundaryMark; ring
  have hleft (g : IslandProfile Z) (hg : Integrable (g y) intensity) (rg : ∀ i, g y i ∈ Icc 0 1) :
      k U g = k A g + k S g := by
    change (∫ i, H.outer x i * g y i ∂intensity) = _ + _
    rw [show k A g + k S g = ∫ i, H.layer x i * g y i + H.boundaryMark x i * g y i ∂intensity from
      (integral_add (K A g (H.layer_mass x).1 hg (H.layer_range x) rg)
        (K S g (H.boundaryMark_hits x).1 hg (H.boundaryMark_range x) rg)).symm]
    apply integral_congr_ae; filter_upwards with i; unfold boundaryMark; ring
  simp_rw [he]
  rw [center_cov (hF x) (hF y) hFF (mF x) (mF y)]
  simp_rw [expand]
  erw [integral_add ((AA.1.sub AU.1).sub UA.1) UU.1,integral_sub (AA.1.sub AU.1) UA.1,
    integral_sub AA.1 AU.1,AA.2,AU.2,UA.2,UU.2]
  change a*a*Real.exp (k A A) - a*e*Real.exp (k A U) - e*a*Real.exp (k U A) +
    e*e*Real.exp (k U U) - (a-e)*(a-e) = _
  rw [hright A (H.layer_mass x).1 (H.layer_range x),hleft A (H.layer_mass y).1 (H.layer_range y),
    hleft U (H.outer_mass y).1 (H.outer_range y),hright A (H.layer_mass x).1 (H.layer_range x),
    hright S (H.boundaryMark_hits x).1 (H.boundaryMark_range x),← add_assoc]
  simp only [shellCovariance,k,A,S,a,e,sq]

/-- A common island gives the shell-overlap term. Distinct shell hits
give the squared shell intensity, restricted to the range of dependence. -/
theorem shellCovarianceBound (hv : v ≤ 1) {R : ℝ}
    (locality : ∀ x y, R ≤ ‖y-x‖ → ∀ i, H.outer x i*H.outer y i = 0) (x y : Position) :
    (∫ ω, H.shellField ω x * H.shellField ω y ∂μ) / ‖x-y‖ ≤
      markOverlap intensity (fun i z => H.boundaryMark z i) (fun i z => H.boundaryMark z i) (x,y) / ‖x-y‖ +
      (Real.exp 1 * (v-H.layerIntensity)^2) * islandNearKernel R (y-x) := by
  rw [H.shell_identity]
  let A := H.layer
  let S := H.boundaryMark
  let k (f g : IslandProfile Z) := overlap (intensity := intensity) f g x y
  have hn (f g : IslandProfile Z) (hf : ∀ i, f x i ∈ Icc 0 1) (hg : ∀ i, g y i ∈ Icc 0 1) :
      0 ≤ k f g := integral_nonneg fun i => mul_nonneg (hf i).1 (hg i).1
  have hb : H.layerIntensity ≤ v := by
    have h : 0 ≤ ∫ i, H.boundaryMark x i ∂intensity := integral_nonneg fun i => (H.boundaryMark_range x i).1
    rw [(H.boundaryMark_hits x).2] at h; linarith
  have hx (f g : IslandProfile Z) (hf : Integrable (f x) intensity) (hg : Integrable (g y) intensity)
      (rf : ∀ i, f x i ∈ Icc 0 1) (rg : ∀ i, g y i ∈ Icc 0 1) :
      k f g ≤ ∫ i, f x i ∂intensity := integral_mono (product_int hf hg rf rg) hf
        (fun i => mul_le_of_le_one_right (rf i).1 (rg i).2)
  have hy (f g : IslandProfile Z) (hf : Integrable (f x) intensity) (hg : Integrable (g y) intensity)
      (rf : ∀ i, f x i ∈ Icc 0 1) (rg : ∀ i, g y i ∈ Icc 0 1) :
      k f g ≤ ∫ i, g y i ∂intensity := integral_mono (product_int hf hg rf rg) hg
        (fun i => mul_le_of_le_one_left (rg i).1 (rf i).2)
  have hk := (hx A A (H.layer_mass x).1 (H.layer_mass y).1 (H.layer_range x) (H.layer_range y)).trans_eq (H.layer_mass x).2
  have hp := (hy A S (H.layer_mass x).1 (H.boundaryMark_hits y).1 (H.layer_range x) (H.boundaryMark_range y)).trans_eq (H.boundaryMark_hits y).2
  have hq := (hx S A (H.boundaryMark_hits x).1 (H.layer_mass y).1 (H.boundaryMark_range x) (H.layer_range y)).trans_eq (H.boundaryMark_hits x).2
  have hd := (hx S S (H.boundaryMark_hits x).1 (H.boundaryMark_hits y).1 (H.boundaryMark_range x) (H.boundaryMark_range y)).trans_eq (H.boundaryMark_hits x).2
  change shellCovariance v H.layerIntensity (k A A) (k A S) (k S A) (k S S) / _ ≤ k S S / _ + _
  by_cases hr : ‖y-x‖ < R
  · have sum : k A A + k A S + k S A + k S S ≤ 2*v := by
      have left (f : IslandProfile Z) (hf : Integrable (f x) intensity) (rf : ∀ i, f x i ∈ Icc 0 1) :
          k f A+k f S ≤ ∫ i, f x i ∂intensity := by
        dsimp only [k,overlap,A,S]
        rw [← integral_add (product_int hf (H.layer_mass y).1 rf (H.layer_range y))
          (product_int hf (H.boundaryMark_hits y).1 rf (H.boundaryMark_range y))]
        apply integral_mono ((product_int hf (H.layer_mass y).1 rf (H.layer_range y)).add
          (product_int hf (H.boundaryMark_hits y).1 rf (H.boundaryMark_range y))) hf
        intro i
        change f x i * H.layer y i + f x i*(H.outer y i-H.layer y i) ≤ f x i
        linarith only [mul_le_of_le_one_right (rf i).1 (H.outer_range y i).2]
      have l₁ := (left A (H.layer_mass x).1 (H.layer_range x)).trans_eq (H.layer_mass x).2
      have l₂ := (left S (H.boundaryMark_hits x).1 (H.boundaryMark_range x)).trans_eq (H.boundaryMark_hits x).2
      linarith only [l₁,l₂,H.layer_pos,hb]
    have h := shellCovariance_le H.layer_pos.le hb hv (hk.trans hb)
      (hn A S (H.layer_range x) (H.boundaryMark_range y))
      (hn S A (H.boundaryMark_range x) (H.layer_range y))
      (hn S S (H.boundaryMark_range x) (H.boundaryMark_range y)) hp hq sum
    rw [islandNearKernel,indicator_of_mem (mem_ball_zero_iff.mpr hr),← norm_sub_rev x y,← div_eq_mul_inv,← add_div]
    exact div_le_div_of_nonneg_right h (norm_nonneg _)
  · have zero (f g : IslandProfile Z) (hf : ∀ i, f x i ∈ Icc 0 (H.outer x i))
        (hg : ∀ i, g y i ∈ Icc 0 (H.outer y i)) : k f g = 0 := by
      have hz i := locality x y (le_of_not_gt hr) i
      apply integral_eq_zero_of_ae
      filter_upwards with i
      exact le_antisymm ((mul_le_mul (hf i).2 (hg i).2 (hg i).1 (H.outer_range x i).1).trans_eq (hz i))
        (mul_nonneg (hf i).1 (hg i).1)
    have a (z : Position) (i : Z) : A z i ∈ Icc 0 (H.outer z i) := ⟨(H.layer_range z i).1,H.layer_le_outer z i⟩
    have s (z : Position) (i : Z) : S z i ∈ Icc 0 (H.outer z i) :=
      ⟨(H.boundaryMark_range z i).1,sub_le_self _ (H.layer_range z i).1⟩
    rw [zero A A (a x) (a y),zero A S (a x) (s y),zero S A (s x) (a y),zero S S (s x) (s y),
      shellCovariance_far,zero_div,zero_add]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (islandNearKernel_pos _ _)

/-- Normalized overlap of the outer single-island bumps. This is the
kernel tested by Graf–Schenker in the exterior energy. -/
def outerOverlap (z : PairSpace) := (∫ i, H.outer z.1 i * H.outer z.2 i ∂intensity)/v

omit [IsProbabilityMeasure μ] in
theorem outerOverlap_measurable [SFinite intensity]
    (hm : Measurable (Function.uncurry (fun i x => H.outer x i))) : Measurable H.outerOverlap := by
  let f (p : PairSpace × Z) := H.outer p.1.1 p.2 * H.outer p.1.2 p.2
  have hf : Measurable f := (hm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
      (hm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable.div_const v

omit [IsProbabilityMeasure μ] in
theorem outerOverlap_range (hv : 0 < v) (z : PairSpace) : H.outerOverlap z ∈ Icc 0 1 := by
  refine ⟨div_nonneg (integral_nonneg fun i => mul_nonneg (H.outer_range z.1 i).1 (H.outer_range z.2 i).1) hv.le,
    (div_le_one hv).mpr ?_⟩
  exact (integral_mono (product_int (H.outer_mass z.1).1 (H.outer_mass z.2).1
    (H.outer_range z.1) (H.outer_range z.2)) (H.outer_mass z.1).1
    (fun i => mul_le_of_le_one_right (H.outer_range z.1 i).1 (H.outer_range z.2 i).2)).trans_eq (H.outer_mass z.1).2

omit [IsProbabilityMeasure μ] in
theorem outerOverlap_far {diam : ℝ}
    (locality : ∀ x y, diam ≤ ‖y-x‖ → ∀ i, H.outer x i*H.outer y i = 0)
    (z : PairSpace) (h : diam ≤ ‖z.2-z.1‖) : H.outerOverlap z = 0 := by
  simp [outerOverlap,locality z.1 z.2 h]

theorem outsidePairMoment (hv : 0 < v) (z : PairSpace) :
    (∫ ω, H.masks.outside ω z.1 * H.masks.outside ω z.2 ∂μ) =
    Real.exp (-(2*v))*Real.exp (v*H.outerOverlap z) := by
  have hp := H.mask_pair z.1 z.2 (H.outer_mass z.1).1 (H.outer_mass z.2).1
    (H.outer_mass z.1).2 (H.outer_mass z.2).2 (H.outer_range z.1) (H.outer_range z.2)
      (fun _ => le_rfl) (fun _ => le_rfl)
  apply hp.2.trans
  rw [← Real.exp_add,show -v + -v = -(2*v) by ring,outerOverlap,mul_div_cancel₀ _ hv.ne']
  rfl

end IslandProfiles
end TSGA.ManyBody
