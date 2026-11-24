import TSGA.IslandChargeDomain

/-! # Joint measurability of locally finite Poisson masks -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Filter Set

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω}
variable {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ}

namespace IslandProfiles
variable (H : IslandProfiles P v)

/-- Each prefix product is jointly measurable. At each configuration and
point the prefix stabilizes as soon as it contains the finite hit window. -/
theorem uncovered_measurable (f : IslandProfile Z)
    (marks : ∀ n, Measurable (fun ω => P.mark ω n))
    (profile : Measurable (Function.uncurry (fun i x => f x i)))
    (support : ∀ x i, f x i ≠ 0 → H.outer x i ≠ 0) :
    Measurable (Function.uncurry (P.uncovered f)) := by
  let term (n : ℕ) (z : Ω × Position) := 1 - f z.2 (P.mark z.1 n)
  let prod (n : ℕ) (z : Ω × Position) := ∏ k ∈ Finset.range n, term k z
  have hm (n : ℕ) : Measurable (term n) :=
    measurable_const.sub (profile.comp (((marks n).comp measurable_fst).prodMk measurable_snd))
  apply measurable_of_tendsto_metrizable (f := prod) (fun n => Finset.measurable_fun_prod _ fun k _ => hm k)
  apply tendsto_pi_nhds.mpr
  intro z
  obtain ⟨N,hN⟩ := (H.window z.1 z.2).exists_nat_subset_range
  apply (tendsto_congr' _).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  apply Eq.symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro i hi
  apply Finset.range_mono hn (hN ?_)
  by_contra h
  apply hi
  have hz : f z.2 (P.mark z.1 i) = 0 := by
    by_contra h'
    exact support z.2 _ h' (H.outside_window z.1 z.2 i h)
  simp [hz]

theorem measurableFields [IsProbabilityMeasure μ] (marks : ∀ n, Measurable (fun ω => P.mark ω n))
    (outer : Measurable (Function.uncurry (fun i x => H.outer x i)))
    (layer : Measurable (Function.uncurry (fun i x => H.layer x i)))
    (core : Measurable (Function.uncurry (fun i x => H.inner x i))) : H.masks.MeasurableFields := by
  have h₁ (x i) (h : H.layer x i ≠ 0) : H.outer x i ≠ 0 := by rw [H.layer_support x i h]; norm_num
  have h₂ (x i) (h : H.inner x i ≠ 0) : H.outer x i ≠ 0 := h₁ x i (by rw [H.inner_support x i h]; norm_num)
  refine ⟨H.uncovered_measurable H.outer marks outer (fun _ _ h => h),?_,?_⟩
  · exact measurable_const.sub (H.uncovered_measurable H.layer marks layer h₁)
  · exact measurable_const.sub (H.uncovered_measurable H.inner marks core h₂)

/-- A finite hit window determined by a measurable region in mark-position
space is jointly measurable. -/
theorem window_measurable (marks : ∀ n, Measurable (fun ω => P.mark ω n))
    (region : Set (Z × Position)) (hr : MeasurableSet region)
    (hits : ∀ ω x n, n ∈ H.window ω x ↔ (P.mark ω n,x) ∈ region) :
    Measurable (Function.uncurry H.window) := by
  apply measurable_finset_iff.mpr
  intro n
  have hm : Measurable (fun z : Ω × Position => (P.mark z.1 n,z.2) ∈ region) :=
    (hr.preimage (((marks n).comp measurable_fst).prodMk measurable_snd)).mem
  convert hm using 1
  funext z
  exact propext (hits z.1 z.2 n)

/-- Evaluating a measurable formula at the random finite window is measurable
when the window enumeration itself is measurable. -/
theorem window_evaluation {F : Finset ℕ → Ω × Position → ℝ}
    (hW : Measurable (Function.uncurry H.window)) (hF : ∀ s, Measurable (F s)) :
    Measurable (fun z : Ω × Position => F (H.window z.1 z.2) z) := by
  have h : Measurable (fun z : Finset ℕ × (Ω × Position) => F z.1 z.2) :=
    measurable_from_prod_countable_right hF
  exact h.comp (hW.prodMk measurable_id)

/-- Joint measurability of a coordinate of the exterior square-root
gradient, expressed by the finite Leibniz sum. -/
theorem exteriorGradientMeasurable (G : Z → Position → ℝ)
    (marks : ∀ n, Measurable (fun ω => P.mark ω n))
    (hW : Measurable (Function.uncurry H.window))
    (outer : Measurable (Function.uncurry (fun i x => H.outer x i)))
    (grad : Measurable (Function.uncurry G)) :
    Measurable (fun z : Ω × Position =>
      ∑ n ∈ H.window z.1 z.2, (∏ k ∈ (H.window z.1 z.2).erase n, Real.sqrt (1-H.outer z.2 (P.mark z.1 k))) *
        G (P.mark z.1 n) z.2) := by
  let F (s : Finset ℕ) (z : Ω × Position) := ∑ n ∈ s, (∏ k ∈ s.erase n, Real.sqrt (1-H.outer z.2 (P.mark z.1 k))) *
        G (P.mark z.1 n) z.2
  apply H.window_evaluation (F := F) hW
  intro s
  apply Finset.measurable_fun_sum
  intro n _
  apply Measurable.mul _ (grad.comp (((marks n).comp measurable_fst).prodMk measurable_snd))
  apply Finset.measurable_fun_prod
  intro k _
  exact (measurable_const.sub (outer.comp (((marks k).comp measurable_fst).prodMk measurable_snd))).sqrt

/-- The same argument for a coordinate of the square-root gradient of
the covered layer or core uses measurability of square root and division. -/
theorem coveredGradientMeasurable (f : IslandProfile Z) (G : Z → Position → ℝ)
    (marks : ∀ n, Measurable (fun ω => P.mark ω n))
    (hW : Measurable (Function.uncurry H.window))
    (profile : Measurable (Function.uncurry (fun i x => f x i)))
    (grad : Measurable (Function.uncurry G)) :
    Measurable (fun z : Ω × Position =>
      ∑ n ∈ H.window z.1 z.2, ((∏ k ∈ (H.window z.1 z.2).erase n, (1-f z.2 (P.mark z.1 k))) *
        Real.sqrt (f z.2 (P.mark z.1 n)) / Real.sqrt (1-∏ k ∈ H.window z.1 z.2, (1-f z.2 (P.mark z.1 k)))) *
        G (P.mark z.1 n) z.2) := by
  let A (k : ℕ) (z : Ω × Position) := f z.2 (P.mark z.1 k)
  let F (s : Finset ℕ) (z : Ω × Position) := ∑ n ∈ s, ((∏ k ∈ s.erase n, (1-A k z)) *
    Real.sqrt (A n z) / Real.sqrt (1-∏ k ∈ s, (1-A k z))) * G (P.mark z.1 n) z.2
  have ha (n : ℕ) : Measurable (A n) := profile.comp (((marks n).comp measurable_fst).prodMk measurable_snd)
  have prod (s : Finset ℕ) : Measurable (fun z => ∏ k ∈ s, (1-A k z)) :=
    Finset.measurable_fun_prod s (fun k _ => measurable_const.sub (ha k))
  apply H.window_evaluation (F := F) hW
  intro s
  apply Finset.measurable_fun_sum
  intro n _
  have num := (prod (s.erase n)).mul (ha n).sqrt
  have den : Measurable (fun z => Real.sqrt (1-∏ k ∈ s, (1-A k z))) :=
    (measurable_const.sub (prod s)).sqrt
  exact (num.div den).mul (grad.comp (((marks n).comp measurable_fst).prodMk measurable_snd))

end IslandProfiles
end TSGA.ManyBody
