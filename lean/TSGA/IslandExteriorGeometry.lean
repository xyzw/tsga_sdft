import TSGA.IslandExteriorTrial
import TSGA.IslandMasks
import TSGA.IslandCoulombKernel

/-! # Fisher intensity of the exterior product

For a finite hit window the square root is the product of the single-mark
square roots. Cauchy–Schwarz costs the number of hits. The diagonal and
off-diagonal Campbell terms then cost one plus the single-window intensity.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ}

/-- The factorial Campbell identity for a finite spatial observation
window, tested against an arbitrary nonnegative mark supported there.
The diagonal term has one intensity integral and the off-diagonal
term has two independent intensity integrals. -/
def PoissonWindowCampbell (P : PoissonIslandProcess μ intensity) (W : Ω → Position → Finset ℕ)
    (region : Position → Set Z) : Prop :=
  ∀ x (f : Z → ℝ), Integrable f intensity → (∀ z, 0 ≤ f z) → (∀ z, z ∉ region x → f z = 0) →
    let total := fun ω => ((W ω x).card:ℝ) * ∑ n ∈ W ω x, f (P.mark ω n)
    Integrable total μ ∧
      (∫ ω, total ω ∂μ) = (∫ z, f z ∂intensity) + intensity.real (region x)*(∫ z, f z ∂intensity)

namespace IslandProfiles
variable (H : IslandProfiles P v)

/-- Finite product derivative of the exterior square root. -/
def outerRootDerivative (G : Z → Position → Fin 3 → ℝ) (ω : Ω) (x : Position) (i : Fin 3) : ℝ :=
  ∑ n ∈ H.window ω x, (∏ k ∈ (H.window ω x).erase n, Real.sqrt (1-H.outer x (P.mark ω k))) * G (P.mark ω n) x i

omit [IsProbabilityMeasure μ] in
theorem outerRootDerivative_fisher_le (G : Z → Position → Fin 3 → ℝ) (ω : Ω) (x : Position) :
    maskFisher (H.outerRootDerivative G ω) x ≤
      ((H.window ω x).card:ℝ) * ∑ n ∈ H.window ω x, maskFisher (G (P.mark ω n)) x := by
  let s := H.window ω x
  let a := fun n => ∏ k ∈ s.erase n, Real.sqrt (1-H.outer x (P.mark ω k))
  have ha (n) : a n ∈ Set.Icc 0 1 := ⟨Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _,
    Finset.prod_le_one₀ (fun _ _ => Real.sqrt_nonneg _) (fun k _ => Real.sqrt_le_one.mpr (by linarith [(H.outer_range x (P.mark ω k)).1]))⟩
  have hsum : (∑ n ∈ s, (a n)^2) ≤ (s.card : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul,mul_one] using
      (Finset.sum_le_sum (s := s) (fun n _ => pow_le_one₀ (ha n).1 (ha n).2 (n:=2)))
  have hcoord (i : Fin 3) : (H.outerRootDerivative G ω x i)^2 ≤
      (s.card:ℝ) * ∑ n ∈ s, (G (P.mark ω n) x i)^2 :=
    (Finset.sum_mul_sq_le_sq_mul_sq s a (fun n => G (P.mark ω n) x i)).trans
      (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg fun n _ => sq_nonneg _))
  exact (Finset.sum_le_sum (s := Finset.univ) fun i _ => hcoord i).trans_eq (by
    simp only [maskFisher,← Finset.mul_sum]
    rw [Finset.sum_comm])

/-- Locality and the usual weak Leibniz rule for a locally finite product
of bounded scalar Sobolev functions. At each observation point a finite
set contains every factor that differs from one in a neighborhood. -/
def WeakLocalProductRule : Prop :=
  ∀ (a : ℕ → Position → ℝ) (d : ℕ → Position → Fin 3 → ℝ) (W : Position → Finset ℕ),
    (∀ n x, a n x ∈ Set.Icc 0 1) → (∀ n i, WeakPartialOn Set.univ i (a n) (fun x => d n x i)) →
    (∀ x, ∀ᶠ y in nhds x, ∀ n, n ∉ W x → a n y = 1) →
    ∀ i, WeakPartialOn Set.univ i (fun x => ∏ n ∈ W x, a n x)
      (fun x => ∑ n ∈ W x, (∏ k ∈ (W x).erase n, a k x)*d n x i)

/-- Apply the ordinary weak product rule to the exterior square root,
using the derivatives of the single bump. -/
theorem weak_outerRootDerivative (leibniz : WeakLocalProductRule) (G : Z → Position → Fin 3 → ℝ)
    (single : ∀ z i, WeakPartialOn Set.univ i (fun x => Real.sqrt (1-H.outer x z)) (fun x => G z x i))
    (nearby : ∀ᵐ ω ∂μ, ∀ x, ∀ᶠ y in nhds x, ∀ n, n ∉ H.window ω x → H.outer y (P.mark ω n) = 0) :
    ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (H.masks.outside ω x))
      (fun x => H.outerRootDerivative G ω x i) := by
  filter_upwards [nearby] with ω hω
  have heq (x) : Real.sqrt (H.masks.outside ω x) =
      ∏ n ∈ H.window ω x, Real.sqrt (1-H.outer x (P.mark ω n)) := by
    change Real.sqrt (∏ᶠ n, (1-H.outer x (P.mark ω n))) = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := H.window ω x) (fun n => 1-H.outer x (P.mark ω n)) (by
      intro n hn
      by_contra hn'
      exact hn (by simp [H.outside_window ω x n hn']))]
    exact Real.sqrt_prod _ (fun n _ => sub_nonneg.mpr (H.outer_range x _).2)
  simp_rw [heq]
  apply leibniz _ _ (H.window ω)
  · intro n x
    exact ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (by linarith [(H.outer_range x (P.mark ω n)).1])⟩
  · exact fun n i => single (P.mark ω n) i
  · intro x
    exact (hω x).mono fun y hy n hn => by simp [hy n hn]

/-- Source data for the outside derivative. The two estimates concern
one mark in intensity space. Isotropy is expressed by rotating a
configuration about the observation point, reversing the given component. -/
structure ExteriorDifferential (H : IslandProfiles P v) (hitRate singleFisher : ℝ) where
  single : Z → Position → Fin 3 → ℝ
  region : Position → Set Z
  window_region : ∀ ω x n, n ∈ H.window ω x ↔ P.mark ω n ∈ region x
  campbell : PoissonWindowCampbell P H.window region
  hit_bound : ∀ᵐ x, intensity.real (region x) ≤ hitRate
  energy_integrable : ∀ᵐ x, Integrable (fun z => maskFisher (single z) x) intensity
  energy_support : ∀ᵐ x, ∀ z, z ∉ region x → maskFisher (single z) x = 0
  energy_bound : ∀ᵐ x, (∫ z, maskFisher (single z) x ∂intensity) ≤ singleFisher
  measurable : Measurable (Function.uncurry H.masks.outside)
  gradient_measurable : ∀ i, Measurable (fun z : Ω × Position => H.outerRootDerivative single z.1 z.2 i)
  weak_gradient : ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (H.masks.outside ω x))
    (fun x => H.outerRootDerivative single ω x i)
  rotation : ∀ᵐ x, ∀ i, ∃ T : Ω ≃ᵐ Ω, MeasurePreserving T μ μ ∧
    ∀ᵐ ω ∂μ, H.masks.outside (T ω) x = H.masks.outside ω x ∧
      H.outerRootDerivative single (T ω) x i = -H.outerRootDerivative single ω x i

/-- Derive the first, drift and Fisher moments of the particular exterior
cutoff. The first moment is the Poisson Laplace formula. -/
def exteriorMask {hitRate singleFisher : ℝ} (F : H.ExteriorDifferential hitRate singleFisher) :
    ExteriorMask μ H.masks.outside v ((1+hitRate)*singleFisher) := by
  let g := H.outerRootDerivative F.single
  have hf (ω x) : 0 ≤ maskFisher (g ω) x := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : Measurable (fun z : Ω × Position => maskFisher (g z.1) z.2) :=
    Finset.measurable_fun_sum _ fun i _ => (F.gradient_measurable i).pow_const _
  have moment : ∀ᵐ x, Integrable (fun ω => maskFisher (g ω) x) μ ∧
      (∫ ω, maskFisher (g ω) x ∂μ) ≤ (1+hitRate)*singleFisher := by
    filter_upwards [F.hit_bound,F.energy_integrable,F.energy_support,F.energy_bound] with x hx hi hs hb
    have hC := F.campbell x _ hi (fun _ => Finset.sum_nonneg fun i _ => sq_nonneg _) hs
    have hφ : Integrable (fun ω => maskFisher (g ω) x) μ :=
      hC.1.mono' (hm.comp measurable_prodMk_right).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (hf ω x)]
        exact H.outerRootDerivative_fisher_le F.single ω x)
    refine ⟨hφ, (integral_mono hφ hC.1 (fun ω => H.outerRootDerivative_fisher_le F.single ω x)).trans ?_⟩
    rw [hC.2,← one_add_mul]
    exact mul_le_mul (by linarith) hb (integral_nonneg fun z => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (by linarith [measureReal_nonneg (μ:=intensity) (s:=F.region x)])
  refine ⟨g,H.masks.outside_range,F.measurable,F.gradient_measurable,F.weak_gradient,
    ae_of_all _ (fun x => (H.masks.outside_mean x).2),?_,moment.mono fun _ h => h.1,moment.mono fun _ h => h.2⟩
  filter_upwards [F.rotation] with x hx
  intro i
  obtain ⟨T,hT,hs⟩ := hx i
  let d := fun ω => maskDrift (H.masks.outside ω) (g ω) i x
  have odd : ∀ᵐ ω ∂μ, d (T ω) = -d ω := hs.mono fun ω h => by simp [d,maskDrift,g,h.1,h.2]
  have e := (hT.integral_comp' d).symm.trans (integral_congr_ae odd)
  rw [integral_neg] at e
  change (∫ ω, d ω ∂μ) = 0
  linarith only [e]

end IslandProfiles

/-- Absorb the one-island shell estimate at the width selected in
`choose_island_width`. The same geometry constant bounds the hit
intensity by `L*v` and the single Fisher intensity by `L*v/(r*δ)`. -/
theorem island_exterior_fisher_le {ε r δ L D hit single : ℝ}
    (he : 0 ≤ ε) (he' : ε ≤ 1) (hr : 0 < r) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hh : hit ≤ L*(ε/2)) (hs : single ≤ L*(ε/2)/(r*δ))
    (hpos : 0 ≤ single) (scale : 1/r*(1+δ⁻¹) ≤ 1+D) :
    (1+hit)*single ≤ ((1+L)*L*(1+D))*ε := by
  have hv : ε/2 ≤ 1 := by linarith
  have hhit := hh.trans (mul_le_of_le_one_right hL hv)
  have hA : 0 ≤ 1+L := by linarith
  have factor : (r*δ)⁻¹ ≤ 1+D := by
    rw [mul_inv_rev,mul_comm δ⁻¹]
    rw [one_div,mul_add,mul_one] at scale
    linarith only [scale,inv_nonneg.mpr hr.le]
  have scale' : 0 ≤ 1+D := (inv_nonneg.mpr (mul_nonneg hr.le hδ.le)).trans factor
  calc
    _ ≤ (1+L)*(L*(ε/2)/(r*δ)) := mul_le_mul (by linarith) hs hpos hA
    _ = ((1+L)*L)*(ε/2)*(r*δ)⁻¹ := by ring
    _ ≤ ((1+L)*L)*(ε/2)*(1+D) := mul_le_mul_of_nonneg_left factor (by positivity)
    _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hA hL) scale') he]

/-- Use the finite spatial range of the normalized overlap in the
exterior comparison. The single-island diameter is at most `a*r`. -/
theorem island_exterior_direct_le {a r C : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hC : islandCoulombConstant*a^2/2 ≤ C) {h : PairSpace → ℝ} (range : ∀ z, h z ∈ Set.Icc 0 1)
    (support : ∀ z, a*r ≤ ‖z.2-z.1‖ → h z = 0) {B : Density}
    (charge : Measurable B.charge) (sq : Integrable (fun x => B.charge x^2)) :
    (∫ z, h z * (directKernel B.charge B.charge z/2) ∂pairVolume) ≤ C*r^2*(∫ x, B.charge x^2) := by
  refine (island_truncated_direct_bound (mul_pos ha hr) range support charge B.charge_nonneg sq).trans ?_
  have hm : 0 ≤ ∫ x, B.charge x^2 := integral_nonneg fun x => sq_nonneg _
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sq_nonneg r)) hm]

end TSGA.ManyBody
