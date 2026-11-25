import TSGA.IslandHartree
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.BigOperators.Intervals

/-! # The two-particle marginal of a Coulomb ensemble

Integrating the ordered pair density against half the Coulomb kernel
recovers the interaction in every particle sector and countable ensemble.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

/-- Spin-summed two-particle marginal, counting ordered pairs. -/
def Wave.pairDensity {n : ℕ} (ψ : Wave (n+2)) (x y : Position) : ℝ :=
  ((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)*∑ s : Spins (n+2), ∫ z : Space n, ‖ψ.value s (Fin.cons x (Fin.cons y z))‖^2

def PureState.pairDensity : PureState → Position → Position → ℝ
  | .vacuum, _, _ => 0
  | .occupied (n := 0) _, _, _ => 0
  | .occupied (n := _n+1) ψ, x, y => ψ.pairDensity x y

theorem PureState.pairDensity_nonneg (s : PureState) (x y : Position) : 0 ≤ s.pairDensity x y := by
  cases s with
  | vacuum => exact le_rfl
  | @occupied n ψ =>
    cases n with
    | zero => exact le_rfl
    | succ n => exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

def MixedState.pairKernel (Γ : MixedState) (z : PairSpace) : ℝ :=
  (∑' n, Γ.weight n * (Γ.component n).pairDensity z.1 z.2)/(2*‖z.1-z.2‖)

theorem MixedState.pairKernel_nonneg (Γ : MixedState) (z : PairSpace) : 0 ≤ Γ.pairKernel z :=
  div_nonneg (tsum_nonneg fun n => mul_nonneg (Γ.weight_nonneg n) ((Γ.component n).pairDensity_nonneg _ _))
    (mul_nonneg (by norm_num) (norm_nonneg _))

private def pairTerm {n : ℕ} (ψ : Wave n) (s : Spins n) (i j : Fin n) (x : Space n) : ℝ :=
  (‖x i - x j‖)⁻¹ * ‖ψ.value s x‖^2

private theorem pairTerm_integrable {n : ℕ} (ψ : Wave n) (s : Spins n) (i j : Fin n) (h : j < i) :
    Integrable (pairTerm ψ s i j) := by
  apply (ψ.interaction_integrable s).mono' ((((continuous_apply i).sub (continuous_apply j)).norm.measurable.inv.aestronglyMeasurable).mul
    ((ψ.square_integrable s).aestronglyMeasurable.norm.pow 2))
  filter_upwards with x
  change ‖pairTerm ψ s i j x‖ ≤ coulomb x * ‖ψ.value s x‖ ^ 2
  rw [Real.norm_of_nonneg (show 0 ≤ pairTerm ψ s i j x from mul_nonneg (by positivity) (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (Finset.single_le_sum (fun k _ => inv_nonneg.mpr (norm_nonneg (x i - x k))) (Finset.mem_Iio.mpr h)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => inv_nonneg.mpr (norm_nonneg (x k-x l))) (Finset.mem_univ i))

private theorem pairExpectation_perm {n : ℕ} (ψ : Wave n) (i j : Fin n) (π : Equiv.Perm (Fin n)) :
    (∑ s, ∫ x, pairTerm ψ s (π i) (π j) x) = ∑ s, ∫ x, pairTerm ψ s i j x := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => Position) π.symm
  have he : MeasurePreserving e := volume_measurePreserving_piCongrLeft _ _
  have heq (z : Space n) : e z = z ∘ π := by
    funext k
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  let r := Equiv.arrowCongr π.symm (Equiv.refl (Fin 2))
  have hr (s : Spins n) : r s = s ∘ π := rfl
  rw [← r.sum_comp (fun s => ∫ x, pairTerm ψ s i j x)]
  apply Finset.sum_congr rfl
  intro s _
  rw [← he.integral_comp' (pairTerm ψ (r s) i j)]
  apply integral_congr_ae
  filter_upwards [ψ.antisymmetric π s] with x hx
  simp only [pairTerm,hr,heq,Function.comp_apply,hx,norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

private theorem pairExpectation_eq {n : ℕ} (ψ : Wave (n+2)) (i j : Fin (n+2)) (h : j < i) :
    (∑ s, ∫ x, pairTerm ψ s i j x) = ∑ s, ∫ x, pairTerm ψ s 1 0 x := by
  let a := Equiv.swap (0 : Fin (n+2)) j
  let b := Equiv.swap (a 1) i
  have h10 : (1 : Fin (n+2)) ≠ 0 := by simp
  have haj : a 1 ≠ j := by simpa only [show a 0 = j from Equiv.swap_apply_left _ _] using a.injective.ne h10
  have hb : b j = j := Equiv.swap_apply_of_ne_of_ne (Ne.symm haj) (ne_of_lt h)
  simpa only [Equiv.trans_apply,show a 0 = j from Equiv.swap_apply_left _ _,hb,
    show b (a 1) = i from Equiv.swap_apply_left _ _] using pairExpectation_perm ψ 1 0 (a.trans b)

private theorem firstPair_interaction {n : ℕ} (ψ : Wave (n+2)) :
    ψ.interaction = ((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)/2 * (∑ s, ∫ x, pairTerm ψ s 1 0 x) := by
  have h (s : Spins (n+2)) : (∫ x, coulomb x*‖ψ.value s x‖^2) =
      ∑ i, ∑ j ∈ Finset.Iio i, ∫ x, pairTerm ψ s i j x := by
    simp only [coulomb,Finset.sum_mul]
    change (∫ x, ∑ i, ∑ j ∈ Finset.Iio i, pairTerm ψ s i j x) = _
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j hj => pairTerm_integrable ψ s i j (Finset.mem_Iio.mp hj))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j hj => pairTerm_integrable ψ s i j (Finset.mem_Iio.mp hj)
  simp only [Wave.interaction,sectorIntegral,h]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.Iio _)]
  have c : ∀ i : Fin (n+2), (∑ j ∈ Finset.Iio i, ∑ s, ∫ x, pairTerm ψ s i j x) =
      (i.val:ℝ)*(∑ s, ∫ x, pairTerm ψ s 1 0 x) := by
    intro i
    rw [Finset.sum_congr rfl (fun j hj => pairExpectation_eq ψ i j (Finset.mem_Iio.mp hj))]
    simp [Fin.card_Iio]
  simp_rw [c]
  rw [← Finset.sum_mul]
  congr 1
  have hc := Finset.sum_range_id_mul_two (n+2)
  have hr : (∑ i : Fin (n+2), (i.val:ℝ)) * 2 = ((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i:ℝ))]
    have hc' : (∑ i ∈ Finset.range (n+2), i)*2 = (n+2)*(n+1) := hc
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ℝ)) hc'
  linarith

/-- Disintegrate over the first two positions while keeping the order of
the remaining particle coordinates. -/
private theorem pairSlice {n : ℕ} {f : Space (n+2) → ℝ} (hf : Integrable f) :
    let g := fun z : PairSpace => ∫ y : Space n, f (Fin.cons z.1 (Fin.cons z.2 y))
    Integrable g pairVolume ∧ (∫ z, g z ∂pairVolume) = ∫ x, f x := by
  let u := fun k => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => Position) 0
  let e : PairSpace × Space n ≃ᵐ Space (n+2) :=
    (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl Position).prodCongr (u n).symm)).trans (u (n+1)).symm
  have hu (k) : MeasurePreserving (u k).symm := (volume_preserving_piFinSuccAbove _ 0).symm
  have he : MeasurePreserving e :=
    (hu (n+1)).comp (((MeasurePreserving.id (μ := (volume : Measure Position))).prod (hu n)).comp volume_preserving_prodAssoc)
  have hu' (k : ℕ) (z : Position × Space k) : (u k).symm z = Fin.cons z.1 z.2 := by
    simp [u,MeasurableEquiv.piFinSuccAbove_symm_apply]
  have heq (z : PairSpace × Space n) : e z = Fin.cons z.1.1 (Fin.cons z.1.2 z.2) := by
    change (u _).symm (z.1.1,(u _).symm (z.1.2,z.2)) = _
    simp only [hu']
  have h := (he.integrable_comp_emb e.measurableEmbedding).2 hf
  have hi := h.integral_prod_left
  have hm := (integral_prod (f ∘ e) h).symm.trans (he.integral_comp' f)
  dsimp only
  rw [show pairVolume = (volume : Measure PairSpace) from (Measure.volume_eq_prod Position Position).symm]
  simpa only [Function.comp_def, heq] using And.intro hi hm

private theorem wave_pair_trace {n : ℕ} (ψ : Wave (n+2)) :
    let k := fun z : PairSpace => ψ.pairDensity z.1 z.2 / (2*‖z.1-z.2‖)
    Integrable k pairVolume ∧ (∫ z, k z ∂pairVolume) = ψ.interaction := by
  let g := fun (s : Spins (n+2)) (z : PairSpace) => ∫ y : Space n, pairTerm ψ s 1 0 (Fin.cons z.1 (Fin.cons z.2 y))
  have h (s : Spins (n+2)) : Integrable (g s) pairVolume ∧ (∫ z, g s z ∂pairVolume) = ∫ x, pairTerm ψ s 1 0 x :=
    pairSlice (pairTerm_integrable ψ s 1 0 (by show (0 : ℕ) < 1; decide))
  let c := ((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)/2
  have he (z : PairSpace) : ψ.pairDensity z.1 z.2 / (2*‖z.1-z.2‖) = c*∑ s, g s z := by
    have hp (s : Spins (n+2)) : g s z = (‖z.1-z.2‖)⁻¹ * ∫ y : Space n, ‖ψ.value s (Fin.cons z.1 (Fin.cons z.2 y))‖^2 := by
      have hj (y : Space n) : (Fin.cons z.1 (Fin.cons z.2 y) : Space (n+2)) 1 = z.2 := rfl
      simp only [g,pairTerm,hj,Fin.cons_zero,norm_sub_rev z.2 z.1,integral_const_mul]
    simp only [Wave.pairDensity,hp,← Finset.mul_sum,c,div_eq_mul_inv,mul_inv_rev]
    ring
  refine ⟨by simpa only [he] using (integrable_finsetSum _ fun s _ => (h s).1).const_mul c,?_⟩
  simp only [he,integral_const_mul,integral_finsetSum _ (fun s _ => (h s).1),fun s => (h s).2,firstPair_interaction,c]

theorem PureState.integral_pairDensity (s : PureState) :
    let k := fun z : PairSpace => s.pairDensity z.1 z.2 / (2*‖z.1-z.2‖)
    Integrable k pairVolume ∧ (∫ z, k z ∂pairVolume) = s.interaction := by
  cases s with
  | vacuum => simp [pairDensity,interaction]
  | @occupied n ψ =>
    cases n with
    | zero =>
      have he : Finset.Iio (0 : Fin 1) = ∅ := Finset.ext fun j => by simp [Finset.mem_Iio]
      have h0 (x : Space 1) : coulomb x = 0 := by simp [coulomb,he]
      simp [pairDensity,interaction,Wave.interaction,sectorIntegral,h0]
    | succ n => exact wave_pair_trace ψ

theorem MixedState.integral_pairKernel (Γ : MixedState) :
    Integrable Γ.pairKernel pairVolume ∧ (∫ z, Γ.pairKernel z ∂pairVolume) = Γ.interaction := by
  let f := fun m (z : PairSpace) => Γ.weight m * ((Γ.component m).pairDensity z.1 z.2 / (2*‖z.1-z.2‖))
  have hi (m : ℕ) : Integrable (f m) pairVolume := ((Γ.component m).integral_pairDensity.1).const_mul _
  have hp (m : ℕ) (z : PairSpace) : 0 ≤ f m z := mul_nonneg (Γ.weight_nonneg m)
    (div_nonneg ((Γ.component m).pairDensity_nonneg _ _) (mul_nonneg (by norm_num) (norm_nonneg _)))
  have ht (m : ℕ) : (∫ z, f m z ∂pairVolume) = Γ.weight m * (Γ.component m).interaction := by
    simp [f, integral_const_mul, (Γ.component m).integral_pairDensity.2]
  have hn : Summable fun m => ∫ z, ‖f m z‖ ∂pairVolume := by
    simpa only [Real.norm_of_nonneg (hp _ _),ht] using Γ.interaction_summable
  have he (z : PairSpace) : Γ.pairKernel z = ∑' m, f m z := by
    simp only [f,pairKernel,div_eq_mul_inv,← mul_assoc,tsum_mul_right]
  have hm : (∫ z, Γ.pairKernel z ∂pairVolume) = Γ.interaction := by
    simp only [he,← integral_tsum_of_summable_integral_norm hi hn,ht,MixedState.interaction]
  refine ⟨?_,hm⟩
  by_cases hz : Γ.interaction = 0
  · have h0 (m : ℕ) : f m =ᵐ[pairVolume] 0 := by
      have hle := Γ.interaction_summable.le_tsum m fun i _ => mul_nonneg (Γ.weight_nonneg i) (Γ.component i).interaction_nonneg
      exact (integral_eq_zero_iff_of_nonneg (hp m) (hi m)).1
        (le_antisymm ((ht m).le.trans (hle.trans_eq hz)) (integral_nonneg (hp m)))
    apply (integrable_zero _ _ _).congr
    filter_upwards [ae_all_iff.mpr h0] with z hz'
    simp [he,hz']
  · exact Integrable.of_integral_ne_zero (hm.trans_ne hz)

end TSGA.ManyBody
