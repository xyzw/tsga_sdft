import TSGA.IslandLocalization
import Mathlib.Algebra.BigOperators.Finprod

/-! # The three cutoffs of the marked Poisson island trial

The Poisson generating functional is stated for integrable tests with almost
surely finitely many nonunit factors, so that `∏ᶠ` gives the realization's
product. The three cutoffs use the same realization and have finite windows.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Islands
open scoped ComplexOrder MatrixOrder

/-- A marked process satisfying the Poisson generating functional on tests
with almost surely finitely many nonunit factors. -/
structure PoissonIslandProcess {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) (intensity : Measure Z) where
  mark : Ω → ℕ → Z
  laplace : ∀ f : Z → ℝ, Integrable f intensity → (∀ z, f z ∈ Set.Icc 0 1) →
    (∀ᵐ ω ∂μ, (Function.mulSupport (fun i => 1 - f (mark ω i))).Finite) →
    Integrable (fun ω => ∏ᶠ i, (1 - f (mark ω i))) μ ∧
      (∫ ω, ∏ᶠ i, (1 - f (mark ω i)) ∂μ) = Real.exp (-(∫ z, f z ∂intensity))

/-- A single profile evaluated at a point for a given island centre and frame. -/
abbrev IslandProfile (Z : Type*) := Position → Z → ℝ

def PoissonIslandProcess.uncovered {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} {intensity : Measure Z} (P : PoissonIslandProcess μ intensity)
    (f : IslandProfile Z) (ω : Ω) (x : Position) : ℝ := ∏ᶠ i, (1 - f x (P.mark ω i))

/-- Nested single-island test functions. The intensities are the single-hit
means, before taking the Poisson union. A finite window contains all marks
that influence a given point. -/
structure IslandProfiles {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} {intensity : Measure Z} (P : PoissonIslandProcess μ intensity) (v : ℝ) where
  outer : IslandProfile Z
  layer : IslandProfile Z
  inner : IslandProfile Z
  outer_range : ∀ x z, outer x z ∈ Set.Icc 0 1
  layer_range : ∀ x z, layer x z ∈ Set.Icc 0 1
  inner_range : ∀ x z, inner x z ∈ Set.Icc 0 1
  layer_support : ∀ x z, layer x z ≠ 0 → outer x z = 1
  inner_support : ∀ x z, inner x z ≠ 0 → layer x z = 1
  window : Ω → Position → Finset ℕ
  outside_window : ∀ ω x i, i ∉ window ω x → outer x (P.mark ω i) = 0
  layerIntensity : ℝ
  innerIntensity : ℝ
  layer_pos : 0 < layerIntensity
  inner_pos : 0 < innerIntensity
  outer_mass : ∀ x, Integrable (outer x) intensity ∧ (∫ z, outer x z ∂intensity) = v
  layer_mass : ∀ x, Integrable (layer x) intensity ∧ (∫ z, layer x z ∂intensity) = layerIntensity
  inner_mass : ∀ x, Integrable (inner x) intensity ∧ (∫ z, inner x z ∂intensity) = innerIntensity

/-- Random masks and scalar normalizations, common to the two Fock states. -/
structure IslandMasks {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : ℝ) where
  outside : Ω → Position → ℝ
  first : Ω → Position → ℝ
  core : Ω → Position → ℝ
  meanFirst : ℝ
  meanCore : ℝ
  first_pos : 0 < meanFirst
  core_pos : 0 < meanCore
  outside_range : ∀ ω x, outside ω x ∈ Set.Icc 0 1
  first_range : ∀ ω x, first ω x ∈ Set.Icc 0 1
  core_range : ∀ ω x, core ω x ∈ Set.Icc 0 1
  separate : ∀ ω x, first ω x ≠ 0 → outside ω x = 0
  nested : ∀ ω x, core ω x ≠ 0 → first ω x = 1
  outside_mean : ∀ x, Integrable (fun ω => outside ω x) μ ∧ (∫ ω, outside ω x ∂μ) = Real.exp (-v)
  first_mean : ∀ x, Integrable (fun ω => first ω x) μ ∧ (∫ ω, first ω x ∂μ) = meanFirst
  core_mean : ∀ x, Integrable (fun ω => core ω x) μ ∧ (∫ ω, core ω x ∂μ) = meanCore

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ}

/-- The two-point generating functional, also for two different profiles.
Finite locality permits multiplying the two products in each realization. -/
theorem PoissonIslandProcess.pair_laplace (P : PoissonIslandProcess μ intensity) (f g : Z → ℝ)
    (hf : Integrable f intensity) (hg : Integrable g intensity) (hfg : Integrable (fun z => f z*g z) intensity)
    (rf : ∀ z, f z ∈ Set.Icc 0 1) (rg : ∀ z, g z ∈ Set.Icc 0 1)
    (lf : ∀ ω, (Function.mulSupport (fun i => 1-f (P.mark ω i))).Finite)
    (lg : ∀ ω, (Function.mulSupport (fun i => 1-g (P.mark ω i))).Finite) :
    let K := fun ω => (∏ᶠ i, (1-f (P.mark ω i))) * (∏ᶠ i, (1-g (P.mark ω i)))
    Integrable K μ ∧ (∫ ω, K ω ∂μ) =
      Real.exp (-((∫ z, f z ∂intensity)+(∫ z, g z ∂intensity))) * Real.exp (∫ z, f z*g z ∂intensity) := by
  intro K
  let h := fun z => (f z + g z) - f z*g z
  have hr (z) : h z ∈ Set.Icc 0 1 := by
    obtain ⟨a,b⟩ := rf z
    obtain ⟨c,d⟩ := rg z
    dsimp [h]; constructor <;> nlinarith [mul_nonneg a (sub_nonneg.mpr d),mul_nonneg (sub_nonneg.mpr b) (sub_nonneg.mpr d)]
  have factor (z) : 1 - h z = (1 - f z) * (1 - g z) := by
    dsimp [h]
    ring
  have he (ω) : K ω = ∏ᶠ i, (1-h (P.mark ω i)) := by
    dsimp only [K]
    simp only [factor, finprod_mul_distrib (lf ω) (lg ω)]
  obtain ⟨hi,hm⟩ := P.laplace h ((hf.add hg).sub hfg) hr (ae_of_all _ fun ω => by
    simp only [factor]
    exact ((lf ω).union (lg ω)).subset (Function.mulSupport_mul _ _))
  refine ⟨hi.congr (ae_of_all _ fun ω => (he ω).symm),?_⟩
  rw [integral_congr_ae (ae_of_all _ he),hm,← Real.exp_add]
  congr 1
  dsimp only [h]
  erw [integral_sub (hf.add hg) hfg,integral_add hf hg]; ring

namespace IslandProfiles
variable (H : IslandProfiles P v)

section
omit [IsProbabilityMeasure μ]

private theorem mulSupport_subset_window (f : IslandProfile Z) (ω : Ω) (x : Position)
    (h : ∀ z, f x z ≠ 0 → H.outer x z ≠ 0) :
    Function.mulSupport (fun i => 1 - f x (P.mark ω i)) ⊆ H.window ω x := by
  intro i hi
  by_contra hn
  have hzero : f x (P.mark ω i) = 0 := by
    by_contra hf
    exact h _ hf (H.outside_window ω x i hn)
  exact hi (by simp [hzero])

/-- Only marks in the profile window can contribute a nonunit factor. -/
theorem finite_mulSupport (f : IslandProfile Z) (ω : Ω) (x : Position)
    (h : ∀ z, f x z ≠ 0 → H.outer x z ≠ 0) :
    (Function.mulSupport (fun i => 1 - f x (P.mark ω i))).Finite :=
  (H.window ω x).finite_toSet.subset (H.mulSupport_subset_window f ω x h)

private theorem window_prod (f : IslandProfile Z) (ω : Ω) (x : Position)
    (h : ∀ z, f x z ≠ 0 → H.outer x z ≠ 0) : P.uncovered f ω x =
    ∏ i ∈ H.window ω x, (1 - f x (P.mark ω i)) :=
  finprod_eq_prod_of_mulSupport_subset _ (H.mulSupport_subset_window f ω x h)

private theorem prod_range (f : IslandProfile Z) (ω : Ω) (x : Position)
    (hf : ∀ z, f x z ∈ Set.Icc 0 1) (h : ∀ z, f x z ≠ 0 → H.outer x z ≠ 0) :
    P.uncovered f ω x ∈ Set.Icc 0 1 := by
  rw [H.window_prod f ω x h]
  exact ⟨Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hf _).2),
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (hf _).2) (fun i _ => by linarith [(hf (P.mark ω i)).1])⟩

private theorem product_separate (f g : IslandProfile Z) (ω : Ω) (x : Position)
    (hf : ∀ z, f x z ≠ 0 → H.outer x z ≠ 0) (hg : ∀ z, g x z ≠ 0 → H.outer x z ≠ 0)
    (sep : ∀ z, g x z ≠ 0 → f x z = 1) (hn : 1 - P.uncovered g ω x ≠ 0) :
    P.uncovered f ω x = 0 := by
  rw [H.window_prod g ω x hg] at hn
  have hit : ∃ i ∈ H.window ω x, g x (P.mark ω i) ≠ 0 := by
    by_contra! hz
    have hone : (∏ i ∈ H.window ω x, (1-g x (P.mark ω i))) = 1 :=
      Finset.prod_eq_one (fun i hi => by rw [hz i hi,sub_zero])
    exact hn (sub_eq_zero.mpr hone.symm)
  obtain ⟨i,hi,hn⟩ := hit
  rw [H.window_prod f ω x hf]
  exact Finset.prod_eq_zero hi (by simp [sep _ hn])

end

private theorem mean_hit (f : IslandProfile Z) (x : Position) (m : ℝ)
    (hf : ∀ z, f x z ∈ Set.Icc 0 1) (hi : Integrable (f x) intensity) (hm : (∫ z, f x z ∂intensity) = m)
    (hs : ∀ z, f x z ≠ 0 → H.outer x z ≠ 0) :
    Integrable (fun ω => 1 - P.uncovered f ω x) μ ∧
    (∫ ω, 1 - P.uncovered f ω x ∂μ) = coveredMean m := by
  obtain ⟨h,e⟩ := P.laplace _ hi hf (ae_of_all _ fun ω => H.finite_mulSupport f ω x hs)
  exact ⟨(integrable_const (1:ℝ)).sub h, by
    change (∫ ω, 1 - ∏ᶠ i, (1 - f x (P.mark ω i)) ∂μ) = _
    rw [integral_sub (integrable_const _) h,integral_const,e,hm]; simp [coveredMean]⟩

def masks (H : IslandProfiles P v) : IslandMasks μ v := by
  let h₁ : ∀ x z, H.layer x z ≠ 0 → H.outer x z ≠ 0 := fun x z h => by rw [H.layer_support x z h]; norm_num
  let h₂ : ∀ x z, H.inner x z ≠ 0 → H.layer x z ≠ 0 := fun x z h => by rw [H.inner_support x z h]; norm_num
  refine ⟨P.uncovered H.outer,(fun ω x => 1 - P.uncovered H.layer ω x),
    (fun ω x => 1 - P.uncovered H.inner ω x), coveredMean H.layerIntensity,coveredMean H.innerIntensity,
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr H.layer_pos)),sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr H.inner_pos)),
    fun ω x => H.prod_range _ ω x (H.outer_range x) (fun _ h => h),?_,?_,?_,?_,?_,?_,?_⟩
  · intro ω x
    obtain ⟨a,b⟩ := H.prod_range _ ω x (H.layer_range x) (h₁ x)
    exact ⟨by linarith,by linarith⟩
  · intro ω x
    obtain ⟨a,b⟩ := H.prod_range _ ω x (H.inner_range x) (fun z h => h₁ x z (h₂ x z h))
    exact ⟨by linarith,by linarith⟩
  · exact fun ω x => H.product_separate _ _ ω x (fun _ h => h) (h₁ x) (H.layer_support x)
  · intro ω x hx
    rw [H.product_separate H.layer H.inner ω x (h₁ x) (fun z h => h₁ x z (h₂ x z h)) (H.inner_support x) hx,sub_zero]
  · intro x
    simpa only [PoissonIslandProcess.uncovered,(H.outer_mass x).2] using
      P.laplace _ (H.outer_mass x).1 (H.outer_range x)
        (ae_of_all _ fun ω => H.finite_mulSupport H.outer ω x (fun _ h => h))
  · exact fun x => H.mean_hit _ _ _ (H.layer_range x) (H.layer_mass x).1 (H.layer_mass x).2 (h₁ x)
  · exact fun x => H.mean_hit _ _ _ (H.inner_range x) (H.inner_mass x).1 (H.inner_mass x).2
      (fun z h => h₁ x z (h₂ x z h))

end IslandProfiles

namespace IslandMasks
variable (m : IslandMasks μ v)

def c₁ : ℝ := (1-Real.exp (-v))/m.meanFirst
def c₂ : ℝ := 1/m.meanCore

theorem normalized : Real.exp (-v) + m.c₁*m.meanFirst = 1 ∧ m.c₂*m.meanCore = 1 :=
  corrected_mean m.first_pos.ne' m.core_pos.ne'

def outsideMatrix (B : Density) (ω : Ω) (x : Position) : SpinMatrix := m.outside ω x • B.matrix x

def insideMatrix (B D : Density) (ω : Ω) (x : Position) : SpinMatrix :=
  (m.c₁*m.first ω x) • B.matrix x + (m.c₂*m.core ω x) • D.matrix x

theorem disjoint (B D : Density) (ω : Ω) : Disjoint (Function.support (m.outsideMatrix B ω))
    (Function.support (m.insideMatrix B D ω)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have ha : m.outside ω x ≠ 0 := fun h => hx (by simp [outsideMatrix,h])
  have hb : m.first ω x = 0 := by by_contra hn; exact ha (m.separate ω x hn)
  have hc : m.core ω x = 0 := by by_contra hn; have := m.nested ω x hn; linarith
  exact hy (by simp [insideMatrix,hb,hc])

theorem mean_scalar (x : Position) (a b : ℝ) :
    Integrable (fun ω => m.outside ω x*a + ((m.c₁*m.first ω x)*a + (m.c₂*m.core ω x)*b)) μ ∧
    (∫ ω, m.outside ω x*a + ((m.c₁*m.first ω x)*a + (m.c₂*m.core ω x)*b) ∂μ) = a+b := by
  have A := (m.outside_mean x).1.mul_const a
  have B := ((m.first_mean x).1.const_mul m.c₁).mul_const a
  have D := ((m.core_mean x).1.const_mul m.c₂).mul_const b
  refine ⟨A.add (B.add D),?_⟩
  erw [integral_add A (B.add D),integral_add B D]
  simp only [integral_mul_const,integral_const_mul,(m.outside_mean x).2,(m.first_mean x).2,(m.core_mean x).2,m.normalized.2,one_mul]
  linear_combination a * m.normalized.1

def outerCharge (B : Density) (ω : Ω) (x : Position) := m.outside ω x * B.charge x

def innerCharge (B D : Density) (ω : Ω) (x : Position) :=
  (m.c₁ * m.first ω x) * B.charge x + (m.c₂ * m.core ω x) * D.charge x

def firstFluct (B : Density) (ω : Ω) (x : Position) :=
  ((m.c₁-1)*(m.first ω x-m.meanFirst))*B.charge x

def shellFluct (B : Density) (ω : Ω) (x : Position) :=
  ((1-Real.exp (-v)-m.meanFirst) - (1-m.outside ω x-m.first ω x))*B.charge x

def coreFluct (D : Density) (ω : Ω) (x : Position) :=
  (m.c₂*(m.core ω x-m.meanCore))*D.charge x

theorem fluctuation_split (B D : Density) (ω : Ω) (x : Position) :
    (m.outerCharge B ω x + m.innerCharge B D ω x) - (B.charge x + D.charge x) =
      m.firstFluct B ω x + m.shellFluct B ω x + m.coreFluct D ω x := by
  simp only [outerCharge,innerCharge,firstFluct,shellFluct,coreFluct]
  linear_combination (B.charge x) * m.normalized.1 + D.charge x * m.normalized.2

end IslandMasks
end TSGA.ManyBody
