import TSGA.IslandMasks

/-! # Local Lipschitz regularity of the square root of a Poisson union -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set Filter
open scoped NNReal Topology

private def rootJoin (a b : ℝ) := Real.sqrt (1-(1-a^2)*(1-b^2))

private theorem rootJoin_comm (a b : ℝ) : rootJoin a b = rootJoin b a := by simp only [rootJoin,mul_comm]

/-- Varying one occupied amplitude changes the new amplitude by at most
the same amount, also at configurations of zero coverage. -/
private theorem rootJoin_dist_left {a q b : ℝ} (ha : a ∈ Icc 0 1) (hq : q ∈ Icc 0 1)
    (hb : b ∈ Icc 0 1) : dist (rootJoin a b) (rootJoin q b) ≤ dist a q := by
  let c := 1-b^2
  have hc : c ∈ Icc 0 1 := ⟨sub_nonneg.mpr (pow_le_one₀ hb.1 hb.2),sub_le_self _ (sq_nonneg _)⟩
  let F (x : ℝ) := Real.sqrt (1-c+c*x^2)
  have repr (x : ℝ) : rootJoin x b = F x := by dsimp [rootJoin,F,c]; congr 1; ring
  have step {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) (hxy : x ≤ y) : dist (F x) (F y) ≤ dist x y := by
    have hpos : 0 ≤ 1-c+c*x^2 := add_nonneg (sub_nonneg.mpr hc.2) (mul_nonneg hc.1 (sq_nonneg x))
    have eqn : (F x)^2 = 1-c+c*x^2 := Real.sq_sqrt hpos
    have lower : x ≤ F x := Real.le_sqrt_of_sq_le (by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2 (n:=2)))])
    have cl : c*x ≤ F x := (mul_le_of_le_one_left hx.1 hc.2).trans lower
    have mono : F x ≤ F y := Real.sqrt_le_sqrt (add_le_add_right
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hx.1 hy.1).mpr hxy) hc.1) _)
    have upper : F y ≤ F x+(y-x) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨add_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hxy),?_⟩
      nlinarith only [eqn,mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr cl),
        mul_nonneg (sub_nonneg.mpr hc.2) (sq_nonneg (y-x))]
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr mono),abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith only [upper]
  rw [repr,repr]
  rcases le_total a q with h | h
  · exact step ha hq h
  · rw [dist_comm (F a),dist_comm a]; exact step hq ha h

private theorem rootJoin_local {f g : Position → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
    (rf : ∀ x, f x ∈ Icc 0 1) (rg : ∀ x, g x ∈ Icc 0 1) :
    LocallyLipschitz (fun x => rootJoin (f x) (g x)) := by
  intro x
  obtain ⟨A,U,hU,fa⟩ := hf x
  obtain ⟨B,V,hV,gb⟩ := hg x
  refine ⟨A+B,U∩V,inter_mem hU hV,LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  have h₁ := rootJoin_dist_left (rf y) (rf z) (rg y)
  have h₂ := rootJoin_dist_left (rg y) (rg z) (rf z)
  have h := dist_triangle (rootJoin (f y) (g y)) (rootJoin (f z) (g y)) (rootJoin (f z) (g z))
  rw [rootJoin_comm (g y) (f z),rootJoin_comm (g z) (f z)] at h₂
  rw [NNReal.coe_add,add_mul]
  exact h.trans (add_le_add (h₁.trans (fa.dist_le_mul _ hy.1 _ hz.1)) (h₂.trans (gb.dist_le_mul _ hy.2 _ hz.2)))

private theorem finite_unionRoot (f : ℕ → Position → ℝ) (r : ∀ i x, f i x ∈ Icc 0 1)
    (h : ∀ i, LocallyLipschitz (fun x => Real.sqrt (f i x))) (s : Finset ℕ) :
    LocallyLipschitz (fun x => Real.sqrt (1-∏ i ∈ s, (1-f i x))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,sub_self,Real.sqrt_zero]
    exact (LipschitzWith.const (0:ℝ)).locallyLipschitz
  | @insert i s hi ih =>
    let p (x : Position) := ∏ j ∈ s, (1-f j x)
    have pp (x : Position) : p x ∈ Icc 0 1 :=
      ⟨Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (r j x).2),
        Finset.prod_le_one₀ (fun j _ => sub_nonneg.mpr (r j x).2) (fun j _ => sub_le_self _ (r j x).1)⟩
    have rh (x) : Real.sqrt (f i x) ∈ Icc 0 1 := ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (r i x).2⟩
    have ru (x) : Real.sqrt (1-p x) ∈ Icc 0 1 :=
      ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (sub_le_self _ (pp x).1)⟩
    have heq (x : Position) : Real.sqrt (1-∏ j ∈ insert i s, (1-f j x)) =
        rootJoin (Real.sqrt (f i x)) (Real.sqrt (1-p x)) := by
      rw [Finset.prod_insert hi,rootJoin,Real.sq_sqrt (r i x).1,Real.sq_sqrt (sub_nonneg.mpr (pp x).2),sub_sub_cancel]
    simp_rw [heq]
    exact rootJoin_local (h i) ih rh ru

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω}
variable {intensity : Measure Z} {P : PoissonIslandProcess μ intensity} {v : ℝ}

/-- Local finiteness fixes the active prefix throughout a neighborhood,
where the finite-union Lipschitz estimate applies. -/
theorem IslandProfiles.unionRoot_locallyLipschitz (H : IslandProfiles P v) (f : IslandProfile Z)
    (rf : ∀ x z, f x z ∈ Icc 0 1)
    (nearby : ∀ᵐ ω ∂μ, ∀ x, ∀ᶠ y in 𝓝 x, ∀ n, n ∉ H.window ω x → f y (P.mark ω n) = 0)
    (singleLip : ∀ z, LocallyLipschitz (fun x => Real.sqrt (f x z))) :
    ∀ᵐ ω ∂μ, LocallyLipschitz (fun x => Real.sqrt (1-P.uncovered f ω x)) := by
  filter_upwards [nearby] with ω hω
  intro x
  let W := H.window ω x
  let p (y : Position) := ∏ n ∈ W, (1-f y (P.mark ω n))
  have hi := finite_unionRoot (fun k y => f y (P.mark ω k)) (fun _ y => rf y _) (fun k => singleLip (P.mark ω k)) W
  obtain ⟨K,V,hV,hK⟩ := hi x
  have heq : ∀ᶠ y in 𝓝 x, P.uncovered f ω y = p y := by
    filter_upwards [hω x] with y hy
    apply finprod_eq_prod_of_mulSupport_subset
    intro n hn
    by_contra h
    exact hn (by simp [hy n h])
  refine ⟨K,V∩{y | P.uncovered f ω y = p y},inter_mem hV heq,LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  change dist (Real.sqrt (1-P.uncovered f ω y)) (Real.sqrt (1-P.uncovered f ω z)) ≤ _
  rw [hy.2,hz.2]
  exact hK.dist_le_mul _ hy.1 _ hz.1

end TSGA.ManyBody
