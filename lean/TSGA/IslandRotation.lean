import TSGA.IslandExteriorGeometry

/-! # Rotation of the exterior product at a fixed observation point -/

noncomputable section
namespace TSGA.ManyBody.IslandProfiles
open MeasureTheory

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Measure Z} {P : PoissonIslandProcess μ ι} {v : ℝ} (H : IslandProfiles P v)

/-- Isotropy of the configurations and covariance of a single mark under
a half-turn yield the sign law for the whole finite product derivative.
Relabeling the active marks does not affect either product. -/
theorem rotation_of_mark_half_turn (G : Z → Position → Fin 3 → ℝ)
    (rotate : ∀ᵐ x, ∀ i, ∃ T : Ω ≃ᵐ Ω, MeasurePreserving T μ μ ∧
      ∀ᵐ ω ∂μ, ∃ σ : Equiv.Perm ℕ, (H.window ω x).map σ.toEmbedding = H.window (T ω) x ∧
        ∀ n ∈ H.window ω x, H.outer x (P.mark (T ω) (σ n)) = H.outer x (P.mark ω n) ∧
          G (P.mark (T ω) (σ n)) x i = -G (P.mark ω n) x i) :
    ∀ᵐ x, ∀ i, ∃ T : Ω ≃ᵐ Ω, MeasurePreserving T μ μ ∧ ∀ᵐ ω ∂μ,
      H.masks.outside (T ω) x = H.masks.outside ω x ∧
        H.outerRootDerivative G (T ω) x i = -H.outerRootDerivative G ω x i := by
  filter_upwards [rotate] with x hx
  intro i
  obtain ⟨T,hT,ht⟩ := hx i
  refine ⟨T,hT,ht.mono ?_⟩
  rintro ω ⟨σ,hw,hm⟩
  have val (f : ℝ → ℝ) (s : Finset ℕ) (hs : s ⊆ H.window ω x) :
      (∏ k ∈ s.map σ.toEmbedding, f (H.outer x (P.mark (T ω) k))) =
        ∏ k ∈ s, f (H.outer x (P.mark ω k)) := by
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun n hn => congrArg f (hm n (hs hn)).1
  constructor
  · have h (ω') : H.masks.outside ω' x = ∏ n ∈ H.window ω' x, (1-H.outer x (P.mark ω' n)) := by
      apply finprod_eq_prod_of_mulSupport_subset
      intro n hn
      by_contra he
      exact hn (by simp [H.outside_window ω' x n he])
    rw [h (T ω),h ω,← hw]
    exact val (1-·) _ (fun _ h => h)
  · rw [outerRootDerivative,outerRootDerivative,← hw,Finset.sum_map,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.map_erase, val (fun t => Real.sqrt (1-t)) _ (Finset.erase_subset _ _)]
    change _ * G (P.mark (T ω) (σ n)) x i = _
    rw [(hm n hn).2,mul_neg]

end TSGA.ManyBody.IslandProfiles
