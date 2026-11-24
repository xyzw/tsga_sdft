import TSGA.IslandLocalization
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Coulomb fluctuations of marked islands

The near/far split bounds the Coulomb potential of any single mark from
its height and mass. Averaging marks and applying the symmetric kernel
bound gives the electrostatic costs, including the thin shell.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Metric Set
open scoped ENNReal

/-- Cut off the Coulomb kernel at the chosen splitting radius. -/
def islandNearKernel (r : ℝ) := (ball (0 : Position) r).indicator (fun z => ‖z‖⁻¹)

theorem islandNearKernel_integrable (r : ℝ) : Integrable (islandNearKernel r) := by
  apply (integrable_indicator_iff measurableSet_ball).2
  apply integrableOn_ball_of_norm_le_rpow (α := 1) (C := 1)
    (by simp [finrank_euclideanSpace]) (by simp [finrank_euclideanSpace])
  · exact ae_of_all _ fun y => by simp [Real.rpow_neg_one]
  · exact continuous_norm.measurable.inv.aestronglyMeasurable

theorem islandNearKernel_pos (r : ℝ) (z : Position) : 0 ≤ islandNearKernel r z :=
  indicator_nonneg (fun y _ => inv_nonneg.mpr (norm_nonneg y)) z

def islandCoulombConstant := (∫ z, islandNearKernel 1 z) + 1

theorem islandCoulombConstant_one_le : 1 ≤ islandCoulombConstant := by
  unfold islandCoulombConstant
  have hn : 0 ≤ ∫ z, islandNearKernel 1 z := integral_nonneg fun z => islandNearKernel_pos 1 z
  linarith

theorem islandNearKernel_mass {r : ℝ} (hr : 0 < r) :
    ∫ y, islandNearKernel r y = r^2 * ∫ y, islandNearKernel 1 y := by
  have h (y : Position) : islandNearKernel r y = r⁻¹ * islandNearKernel 1 (r⁻¹ • y) := by
    have hb : r⁻¹ • y ∈ ball (0 : Position) 1 ↔ y ∈ ball (0 : Position) r := by
      simp [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        inv_mul_eq_div, div_lt_one hr]
    by_cases hy : y ∈ ball (0 : Position) r
    · simp [islandNearKernel, hy, hb.mpr hy, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_comm, hr.ne']
    · simp [islandNearKernel, hy, mt hb.mp hy]
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ hr.le]
  simp [finrank_euclideanSpace, smul_eq_mul, hr.ne', ← mul_assoc, pow_succ]

/-- Potential of a mark of mass at most m and height one. Splitting at
m^(1/3) gives the m^(2/3) bound uniformly in the observation point. -/
theorem island_potential_bound {f : Position → ℝ} {m : ℝ} (hm : 0 < m) (hf : Integrable f)
    (height : ∀ y, f y ∈ Icc 0 1) (mass : (∫ y, f y) ≤ m) (x : Position) :
    Integrable (fun y => f y / ‖x-y‖) ∧ (∫ y, f y / ‖x-y‖) ≤ islandCoulombConstant * m^(2/3:ℝ) := by
  let a := m^(1/3:ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hm _
  have h₂ : a^2 = m^(2/3:ℝ) := by rw [show a^2 = (m^(1/3:ℝ))^((2:ℕ):ℝ) by simp [a],← Real.rpow_mul hm.le]; norm_num
  have h₃ : m/a = a^2 := by
    apply (div_eq_iff ha.ne').mpr
    rw [h₂,show a = m^(1/3:ℝ) from rfl,← Real.rpow_add hm]
    norm_num
  have hi := ((islandNearKernel_integrable a).comp_sub_right x).add (hf.div_const a)
  have hn (y : Position) := div_nonneg (height y).1 (norm_nonneg (x-y))
  have bound (y : Position) : f y / ‖x-y‖ ≤ islandNearKernel a (y-x) + f y / a := by
    rw [norm_sub_rev x y]
    by_cases h : y-x ∈ ball (0:Position) a
    · rw [islandNearKernel,indicator_of_mem h]
      refine le_add_of_le_of_nonneg ?_ (div_nonneg (height y).1 ha.le)
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_right (height y).2 (inv_nonneg.mpr (norm_nonneg _))
    · rw [islandNearKernel,indicator_of_notMem h,zero_add]
      exact div_le_div_of_nonneg_left (height y).1 ha (le_of_not_gt (fun hn => h (mem_ball_zero_iff.mpr hn)))
  have hfa : Integrable (fun y => f y / ‖x-y‖) := hi.mono' (hf.1.aemeasurable.div (continuous_const.sub continuous_id).norm.aemeasurable).aestronglyMeasurable (ae_of_all _ fun y => by
    change ‖f y / ‖x-y‖‖ ≤ islandNearKernel a (y-x) + f y / a
    rw [Real.norm_of_nonneg (hn y)]; exact bound y)
  refine ⟨hfa,(integral_mono hfa hi bound).trans ?_⟩
  change (∫ y, islandNearKernel a (y-x)+f y/a) ≤ _
  rw [integral_add ((islandNearKernel_integrable a).comp_sub_right x) (hf.div_const a),
    integral_sub_right_eq_self,integral_div,islandNearKernel_mass ha]
  have hb := (div_le_div_of_nonneg_right mass ha.le).trans_eq h₃
  unfold islandCoulombConstant
  rw [← h₂]
  linarith only [hb]

/-- Row bounds for a nonnegative symmetric spatial kernel. -/
structure IslandSchurKernel (K : PairSpace → ℝ) (c : ℝ) : Prop where
  measurable : Measurable K
  nonneg : ∀ z, 0 ≤ K z
  symm : ∀ x y, K (x,y) = K (y,x)
  rows : ∀ x, Integrable (fun y => K (x,y)) ∧ (∫ y, K (x,y)) ≤ c

theorem IslandSchurKernel.charge_bound {K : PairSpace → ℝ} {c : ℝ} (h : IslandSchurKernel K c)
    {ρ : Position → ℝ} (hρ : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (h₂ : Integrable (fun x => ρ x^2)) :
    Integrable (fun z : PairSpace => (ρ z.1 * ρ z.2) * K z) pairVolume ∧
    (∫ z : PairSpace, (ρ z.1 * ρ z.2) * K z ∂pairVolume) ≤ c * ∫ x, ρ x^2 := by
  let f (z : PairSpace) := ρ z.1^2 * K z
  have hm : Measurable f := ((hρ.comp measurable_fst).pow_const 2).mul h.measurable
  have hn z : 0 ≤ f z := mul_nonneg (sq_nonneg _) (h.nonneg z)
  have hi : Integrable f pairVolume := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ fun x => (h.rows x).1.const_mul (ρ x^2)
    · apply (h₂.mul_const c).mono' (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      filter_upwards with x
      change ‖∫ y : Position, ‖f (x,y)‖‖ ≤ ρ x^2 * c
      simp_rw [Real.norm_of_nonneg (hn _)]
      rw [Real.norm_of_nonneg (integral_nonneg fun y => hn (x,y))]
      simp only [f,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (h.rows x).2 (sq_nonneg _)
  have hmass : (∫ z, f z ∂pairVolume) ≤ c * ∫ x, ρ x^2 := by
    rw [integral_prod _ hi,mul_comm c,← integral_mul_const]
    apply integral_mono hi.integral_prod_left (h₂.mul_const c)
    intro x
    simp only [f,integral_const_mul]
    exact mul_le_mul_of_nonneg_left (h.rows x).2 (sq_nonneg _)
  let g (z : PairSpace) := ρ z.1 * ρ z.2 * K z
  have bound (z : PairSpace) : g z ≤ (f z+f z.swap)/2 := by
    change ρ z.1*ρ z.2*K z ≤ (ρ z.1^2*K z+ρ z.2^2*K (z.2,z.1))/2
    rw [h.symm z.2 z.1]
    nlinarith only [mul_nonneg (sq_nonneg (ρ z.1 - ρ z.2)) (h.nonneg z)]
  have hs : Integrable (fun z : PairSpace => f z.swap) pairVolume := hi.swap
  have H := (hi.add hs).div_const 2
  have hg : Integrable g pairVolume := H.mono' (((hρ.comp measurable_fst).mul (hρ.comp measurable_snd)).mul h.measurable).aestronglyMeasurable
    (ae_of_all _ fun z => by
      change ‖g z‖ ≤ (f z+f z.swap)/2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hp z.1) (hp z.2)) (h.nonneg z) : 0 ≤ g z)]
      exact bound z)
  refine ⟨hg,(integral_mono hg H bound).trans ?_⟩
  change (∫ z : PairSpace, (f z+f z.swap)/2 ∂pairVolume) ≤ _
  rw [integral_div,integral_add hi hs,integral_prod_swap f]
  linarith only [hmass]

/-- A spatial cutoff attached to one mark. Spatial integration is over the
observation point; hit integration is over the intensity measure. -/
structure IslandMarkBound {Z : Type*} [MeasurableSpace Z] (intensity : Measure Z)
    (g : Z → Position → ℝ) (mass hit : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  height : ∀ i x, g i x ∈ Icc 0 1
  spatial : ∀ i, Integrable (g i) ∧ (∫ x, g i x) ≤ mass
  hits : ∀ x, Integrable (fun i => g i x) intensity ∧ (∫ i, g i x ∂intensity) ≤ hit

def markOverlap {Z : Type*} [MeasurableSpace Z] (intensity : Measure Z) (g h : Z → Position → ℝ) (z : PairSpace) :=
  ∫ i, g i z.1 * h i z.2 ∂intensity

/-- A mass m and hit rate h give a row bound C h m^(2/3).
This is the overlap estimate for the full cutoffs and for the difference
of the two nested cutoffs in the boundary shell. -/
theorem IslandMarkBound.schur {Z : Type*} [MeasurableSpace Z] {intensity : Measure Z} [SFinite intensity]
    {g : Z → Position → ℝ} {m a : ℝ} (h : IslandMarkBound intensity g m a) (hm : 0 < m) :
    IslandSchurKernel (fun z => markOverlap intensity g g z / ‖z.1-z.2‖) (islandCoulombConstant * m^(2/3:ℝ) * a) := by
  let c := islandCoulombConstant * m^(2/3:ℝ)
  have hc : 0 ≤ c := mul_nonneg (zero_le_one.trans islandCoulombConstant_one_le) (Real.rpow_nonneg hm.le _)
  have ho : Measurable (markOverlap intensity g g) := by
    let f (p : PairSpace × Z) := g p.2 p.1.1 * g p.2 p.1.2
    have hf : Measurable f := (h.measurable.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
      (h.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    exact hf.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨ho.div (measurable_fst.sub measurable_snd).norm, fun z => div_nonneg (integral_nonneg fun i =>
    mul_nonneg (h.height i z.1).1 (h.height i z.2).1) (norm_nonneg _), ?_, ?_⟩
  · intro x y
    simp only [markOverlap,norm_sub_rev x y,mul_comm]
  · intro x
    let f (p : Z × Position) := g p.1 x * (g p.1 p.2 / ‖x-p.2‖)
    have hf : Measurable f := (h.measurable.comp (measurable_fst.prodMk measurable_const)).mul
      (h.measurable.div (measurable_const.sub measurable_snd).norm)
    have hpos (p : Z × Position) : 0 ≤ f p :=
      mul_nonneg (h.height p.1 x).1 (div_nonneg (h.height p.1 p.2).1 (norm_nonneg _))
    have hp i := island_potential_bound hm (h.spatial i).1 (h.height i) (h.spatial i).2 x
    have he (i : Z) : (∫ y, f (i,y)) ≤ g i x*c := by
      simp only [f,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hp i).2 (h.height i x).1
    have hi : Integrable f (intensity.prod volume) := by
      apply (integrable_prod_iff hf.aestronglyMeasurable).2
      refine ⟨ae_of_all _ (fun i => (hp i).1.const_mul (g i x)),?_⟩
      apply ((h.hits x).1.mul_const c).mono' hf.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards with i
      simp only [Real.norm_of_nonneg (hpos _), Real.norm_of_nonneg (integral_nonneg fun y => hpos (i,y))]
      exact he i
    have hrow (y : Position) : (∫ i, f (i,y) ∂intensity) = markOverlap intensity g g (x,y) / ‖x-y‖ := by
      simp only [f,markOverlap,← mul_div_assoc,integral_div]
    refine ⟨hi.integral_prod_right.congr (ae_of_all _ hrow), ?_⟩
    simp_rw [← hrow]
    rw [← integral_integral_swap (f := fun i y => f (i,y)) hi]
    calc
      _ ≤ ∫ i, g i x*c ∂intensity := integral_mono hi.integral_prod_left ((h.hits x).1.mul_const c) he
      _ ≤ _ := by rw [integral_mul_const,mul_comm c]; exact mul_le_mul_of_nonneg_right (h.hits x).2 hc

/-- The ball kernel used for the independent-pair remainder. -/
theorem islandNearSchur {R : ℝ} (hR : 0 < R) : IslandSchurKernel
    (fun z => islandNearKernel R (z.2-z.1)) (islandCoulombConstant*R^2) := by
  constructor
  · exact ((continuous_norm.measurable.inv.indicator measurableSet_ball).comp (measurable_snd.sub measurable_fst))
  · exact fun z => islandNearKernel_pos R _
  · intro x y
    simp only [islandNearKernel,Set.indicator,mem_ball_zero_iff,norm_sub_rev y x]
  · intro x
    refine ⟨(islandNearKernel_integrable R).comp_sub_right x,?_⟩
    rw [integral_sub_right_eq_self,islandNearKernel_mass hR]
    unfold islandCoulombConstant
    nlinarith only [sq_nonneg R]

/-- Young bound for a bounded cutoff supported inside a radius R. -/
theorem island_truncated_direct_bound {R : ℝ} (hR : 0 < R) {h : PairSpace → ℝ}
    (range : ∀ z, h z ∈ Icc 0 1) (support : ∀ z, R ≤ ‖z.2-z.1‖ → h z = 0)
    {ρ : Position → ℝ} (hρ : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (h₂ : Integrable (fun x => ρ x^2)) :
    (∫ z, h z * (directKernel ρ ρ z / 2) ∂pairVolume) ≤
      islandCoulombConstant * R^2 * (∫ x, ρ x^2) / 2 := by
  have H := (islandNearSchur hR).charge_bound hρ hp h₂
  have hn z : 0 ≤ directKernel ρ ρ z := div_nonneg (mul_nonneg (hp _) (hp _)) (norm_nonneg _)
  have Hb z : h z * (directKernel ρ ρ z / 2) ≤ (ρ z.1*ρ z.2 * islandNearKernel R (z.2-z.1))/2 := by
    by_cases hh : ‖z.2-z.1‖ < R
    · rw [islandNearKernel, indicator_of_mem (mem_ball_zero_iff.mpr hh),← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [← norm_sub_rev z.1 z.2,← div_eq_mul_inv]
      exact mul_le_of_le_one_left (hn z) (range z).2
    · rw [support z (le_of_not_gt hh),zero_mul]
      exact div_nonneg (mul_nonneg (mul_nonneg (hp _) (hp _)) (islandNearKernel_pos _ _)) (by norm_num)
  calc
    _ ≤ ∫ z, (ρ z.1*ρ z.2 * islandNearKernel R (z.2-z.1))/2 ∂pairVolume :=
      integral_mono_of_nonneg (ae_of_all _ fun z => mul_nonneg (range z).1 (div_nonneg (hn z) (by norm_num)))
        (H.1.div_const 2) (ae_of_all _ Hb)
    _ ≤ _ := by rw [integral_div]; exact div_le_div_of_nonneg_right H.2 (by norm_num)

end TSGA.ManyBody
