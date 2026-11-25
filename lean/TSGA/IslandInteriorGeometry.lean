import TSGA.IslandInteriorTrial
import TSGA.IslandExteriorGeometry

/-! # Fisher intensity of the two occupied Poisson cutoffs

Each covered fraction is one minus a finite product. Its square-root
derivative is a sum of single-mark derivatives with coefficients in [0,1].
The factorial Campbell identity therefore bounds its second moment by the
single-mark Fisher intensity times one plus the intensity of the window.
-/

noncomputable section
namespace TSGA.ManyBody.IslandProfiles

open MeasureTheory TSGA.Islands
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ} (H : IslandProfiles P v)

/-- The coefficient of a single square-root derivative in the finite
union. Division by zero gives zero on the zero set of the covered fraction. -/
def unionCoeff (s : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ s.erase n, (1-f k))*Real.sqrt (f n)/Real.sqrt (1-∏ k ∈ s, (1-f k))

theorem unionCoeff_range (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ k, f k ∈ Set.Icc 0 1)
    {n : ℕ} (hn : n ∈ s) : unionCoeff s f n ∈ Set.Icc 0 1 := by
  let p := ∏ k ∈ s.erase n, (1-f k)
  have p₀ : 0 ≤ p := Finset.prod_nonneg fun k _ => sub_nonneg.mpr (hf k).2
  have p₁ : p ≤ 1 := Finset.prod_le_one₀ (fun k _ => sub_nonneg.mpr (hf k).2) (fun k _ => by linarith [(hf k).1])
  have lower : f n ≤ 1-(∏ k ∈ s, (1-f k)) := by
    rw [← Finset.prod_erase_mul s _ hn]
    change f n ≤ 1-p*(1-f n)
    linarith only [mul_le_of_le_one_left (sub_nonneg.mpr (hf n).2) p₁]
  have arg := (hf n).1.trans lower
  unfold unionCoeff
  refine ⟨div_nonneg (mul_nonneg p₀ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _),?_⟩
  by_cases h : Real.sqrt (1-∏ k ∈ s, (1-f k)) = 0
  · simp [h]
  · rw [div_le_one ((Real.sqrt_nonneg _).lt_of_ne' h)]
    exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) p₁).trans (Real.sqrt_le_sqrt lower)

def unionRootDerivative (f : IslandProfile Z) (G : Z → Position → Fin 3 → ℝ)
    (ω : Ω) (x : Position) (i : Fin 3) : ℝ :=
  ∑ n ∈ H.window ω x, unionCoeff (H.window ω x) (fun k => f x (P.mark ω k)) n * G (P.mark ω n) x i

omit [IsProbabilityMeasure μ] in
theorem union_fisher_le (f : IslandProfile Z) (hf : ∀ x k, f x k ∈ Set.Icc 0 1)
    (G : Z → Position → Fin 3 → ℝ) (ω : Ω) (x : Position) :
    maskFisher (H.unionRootDerivative f G ω) x ≤
      ((H.window ω x).card:ℝ)*(∑ n ∈ H.window ω x, maskFisher (G (P.mark ω n)) x) := by
  let s := H.window ω x
  let a := fun n => unionCoeff s (fun k => f x (P.mark ω k)) n
  have hsum : (∑ n ∈ s, (a n)^2) ≤ (s.card : ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
      (Finset.sum_le_sum (s := s) (fun n hn => pow_le_one₀
        (unionCoeff_range s _ (fun k => hf x (P.mark ω k)) hn).1
        (unionCoeff_range s _ (fun k => hf x (P.mark ω k)) hn).2 (n := 2)))
  have hcoord (i : Fin 3) : (H.unionRootDerivative f G ω x i)^2 ≤
      (s.card:ℝ)*(∑ n ∈ s, (G (P.mark ω n) x i)^2) :=
    (Finset.sum_mul_sq_le_sq_mul_sq s a (fun n => G (P.mark ω n) x i)).trans
      (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg fun n _ => sq_nonneg _))
  exact (Finset.sum_le_sum (s := Finset.univ) fun i _ => hcoord i).trans_eq (by
    simp only [maskFisher,← Finset.mul_sum]; rw [Finset.sum_comm])

/-- Differential data for one profile, its mark support and its spatial
regularity. The intensity bound tests a single mark. -/
structure UnionDifferential (f : IslandProfile Z) (singleFisher : ℝ) (region : Position → Set Z) where
  single : Z → Position → Fin 3 → ℝ
  energy_integrable : ∀ᵐ x, Integrable (fun z => maskFisher (single z) x) intensity
  energy_support : ∀ᵐ x, ∀ z, z ∉ region x → maskFisher (single z) x = 0
  energy_bound : ∀ᵐ x, (∫ z, maskFisher (single z) x ∂intensity) ≤ singleFisher
  measurable : Measurable (fun z : Ω × Position => 1 - P.uncovered f z.1 z.2)
  gradient_measurable : ∀ i, Measurable (fun z : Ω × Position => H.unionRootDerivative f single z.1 z.2 i)
  lip : ∀ᵐ ω ∂μ, LocallyLipschitz (fun x => Real.sqrt (1-P.uncovered f ω x))
  weak : ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (1-P.uncovered f ω x))
    (fun x => H.unionRootDerivative f single ω x i)

theorem union_multiplier {f : IslandProfile Z} {singleFisher hitRate upper : ℝ} {region : Position → Set Z}
    (hf : ∀ x k, f x k ∈ Set.Icc 0 1) (J : H.UnionDifferential f singleFisher region)
    (campbell : PoissonWindowCampbell P H.window region) (rate : ∀ᵐ x, intensity.real (region x) ≤ hitRate)
    (hmax : (1+hitRate)*singleFisher ≤ upper) :
    IslandMultiplier μ (fun ω x => maskFisher (H.unionRootDerivative f J.single ω) x) upper := by
  have hm : Measurable (fun z : Ω × Position => maskFisher (H.unionRootDerivative f J.single z.1) z.2) :=
    Finset.measurable_fun_sum _ fun i _ => (J.gradient_measurable i).pow_const _
  refine ⟨fun _ _ => Finset.sum_nonneg fun i _ => sq_nonneg _,hm.aestronglyMeasurable,?_⟩
  filter_upwards [rate,J.energy_integrable,J.energy_support,J.energy_bound] with x hx hi hs hb
  have c := campbell x _ hi (fun _ => Finset.sum_nonneg fun i _ => sq_nonneg _) hs
  have hi' : Integrable (fun ω => maskFisher (H.unionRootDerivative f J.single ω) x) μ := c.1.mono' (hm.comp measurable_prodMk_right).aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (show 0 ≤ maskFisher _ _ from Finset.sum_nonneg fun i _ => sq_nonneg _)]; exact H.union_fisher_le f hf J.single ω x)
  refine ⟨hi',(integral_mono hi' c.1 (H.union_fisher_le f hf J.single · x)).trans ?_⟩
  rw [c.2,← one_add_mul]
  exact (mul_le_mul (by linarith) hb (integral_nonneg fun z => Finset.sum_nonneg fun i _ => sq_nonneg _)
    (by linarith [measureReal_nonneg (μ:=intensity) (s:=region x)])).trans hmax

/-- Both masked derivatives and both normalization coefficients follow
from the two deterministic profile intensities and the factorial moment
identity on their common window. -/
def interiorMasks {ε r K θ s hitRate firstFisher coreFisher : ℝ} (H : IslandProfiles P (ε/2))
    (he : 0 < ε) (he' : ε ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1/2) (hθ : θ ≤ 1)
    (firstVolume : H.layerIntensity = (ε/2)*(1-s)^3) (coreVolume : H.innerIntensity = θ*(ε/2))
    (large : 13 ≤ K) (largeCore : 4 ≤ K*θ) (region : Position → Set Z)
    (campbell : PoissonWindowCampbell P H.window region) (rate : ∀ᵐ x, intensity.real (region x) ≤ hitRate)
    (A : H.UnionDifferential H.layer firstFisher region) (B : H.UnionDifferential H.inner coreFisher region)
    (firstBound : (1+hitRate)*firstFisher ≤ K*ε) (coreBound : (1+hitRate)*coreFisher ≤ K*ε*r⁻¹^2) :
    InteriorMaskData H.masks r K := by
  have hv : 0 < ε/2 := by linarith
  have fc := first_correction hv hs hs'
  change 1 ≤ coveredMean (ε/2) / coveredMean ((ε/2)*(1-s)^3) ∧ _ at fc
  have cq : H.masks.c₁ = coveredMean (ε/2) / coveredMean ((ε/2)*(1-s)^3) := by
    change _ / coveredMean H.layerIntensity = _; rw [firstVolume]; rfl
  have hi : H.innerIntensity ≤ 1 := by rw [coreVolume]; nlinarith only [mul_le_mul_of_nonneg_right hθ hv.le,he']
  have coreHalf := coveredMean_half H.inner_pos hi
  have ik : ε*H.masks.c₂ ≤ K := by
    change ε*(1/coveredMean H.innerIntensity) ≤ K
    rw [← div_eq_mul_one_div,div_le_iff₀ (show 0 < coveredMean H.innerIntensity from H.masks.core_pos)]
    rw [coreVolume] at coreHalf ⊢
    nlinarith only [mul_le_mul_of_nonneg_left coreHalf (show 0 ≤ K by linarith),
      mul_le_mul_of_nonneg_right largeCore he.le]
  refine ⟨by linarith,cq ▸ fc.1,cq ▸ fc.2.trans (by linarith),ik,?_,A.measurable.aestronglyMeasurable,
    B.measurable.aestronglyMeasurable,_,_,A.lip,B.lip,A.weak,B.weak,
    H.union_multiplier H.layer_range A campbell rate firstBound,
    H.union_multiplier H.inner_range B campbell rate coreBound⟩
  change coveredMean H.layerIntensity ≤ ε
  apply coveredMean_le.trans
  rw [firstVolume]
  have a : (1-s)^3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  nlinarith only [mul_le_mul_of_nonneg_left a hv.le,he]

end TSGA.ManyBody.IslandProfiles
