import TSGA.IslandInteriorGeometry

/-! # Weak derivative of the occupied union

The finite product rule is applied to the complements of the squared
amplitudes. The scalar square-root chain rule is evaluated with the zero
representative on the zero set.
-/

noncomputable section
namespace TSGA.ManyBody.IslandProfiles
open MeasureTheory Filter
open scoped Topology

/-- Local scalar Sobolev chain rules for a square and its complement. The
second rule includes the usual zero derivative on a level set. -/
structure WeakScalarRootRules : Prop where
  square : ∀ (a : Position → ℝ) (d : Position → Fin 3 → ℝ), LocallyLipschitz a →
    (∀ i, WeakPartialOn Set.univ i a (fun x => d x i)) →
    ∀ i, WeakPartialOn Set.univ i (fun x => 1-(a x)^2) (fun x => -(2*a x*d x i))
  complement : ∀ (a : Position → ℝ) (d : Position → Fin 3 → ℝ), (∀ x, a x ∈ Set.Icc 0 1) →
    LocallyLipschitz (fun x => Real.sqrt (1-a x)) →
    (∀ i, WeakPartialOn Set.univ i a (fun x => d x i)) →
    ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (1-a x)) (fun x => -(d x i)/(2*Real.sqrt (1-a x)))

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ} (H : IslandProfiles P v)

/-- Differentiate either occupied cutoff of Appendix C by ordinary scalar
product and chain rules; the derivative formula holds across its zero set. -/
theorem weak_unionRootDerivative (product : WeakLocalProductRule) (chain : WeakScalarRootRules)
    (f : IslandProfile Z) (G : Z → Position → Fin 3 → ℝ) (rf : ∀ x z, f x z ∈ Set.Icc 0 1)
    (nearby : ∀ᵐ ω ∂μ, ∀ x, ∀ᶠ y in 𝓝 x, ∀ n, n ∉ H.window ω x → f y (P.mark ω n) = 0)
    (singleLip : ∀ z, LocallyLipschitz (fun x => √(f x z)))
    (single : ∀ z i, WeakPartialOn Set.univ i (fun x => √(f x z)) (fun x => G z x i))
    (unionLip : ∀ᵐ ω ∂μ, LocallyLipschitz (fun x => √(1-P.uncovered f ω x))) :
    ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i (fun x => √(1-P.uncovered f ω x))
      (fun x => H.unionRootDerivative f G ω x i) := by
  filter_upwards [nearby,unionLip] with ω hw hl
  let W := H.window ω
  let b := fun n x => f x (P.mark ω n)
  let d := fun n x i => -(2*√(b n x)*G (P.mark ω n) x i)
  let p := fun x => ∏ n ∈ W x, (1-b n x)
  have mark (z : Z) (i : Fin 3) := chain.square _ _ (singleLip z) (single z) i
  simp only [Real.sq_sqrt (rf _ _).1] at mark
  have eq (x) : P.uncovered f ω x = p x := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro n hn
    by_contra nx
    exact hn (by simp [(hw x).self_of_nhds n nx])
  have range (n x) : 1-b n x ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr (rf x _).2,sub_le_self _ (rf x _).1⟩
  have mk := product (fun n x => 1-b n x) d W range (fun n i => mark (P.mark ω n) i)
    (fun x => (hw x).mono (fun y hy n hn => by simp [b,hy n hn]))
  have rp (x) : p x ∈ Set.Icc 0 1 := ⟨Finset.prod_nonneg fun n _ => (range n x).1,
    Finset.prod_le_one₀ (fun n _ => (range n x).1) (fun n _ => (range n x).2)⟩
  simp_rw [eq] at hl ⊢
  intro i
  have hu := chain.complement p _ rp hl mk i
  have same : (fun x => H.unionRootDerivative f G ω x i) = fun x =>
      -(∑ n ∈ W x, (∏ k ∈ (W x).erase n, (1-b k x))*d n x i)/(2*√(1-p x)) := by
    funext x
    simp only [unionRootDerivative,unionCoeff,d,p,W,b,← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    rw [div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [same]
  exact hu

end TSGA.ManyBody.IslandProfiles
