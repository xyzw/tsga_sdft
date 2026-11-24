import TSGA.CoulombCutoffArea
import TSGA.CoulombLowerTiling
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Rough Coulomb energies of boundary tiles and the skeleton

For the product of the outer taper with an inner window the two
square-root derivatives give separate convolution costs. On the boundary
one keeps the restricted center volume for the mass term and integrates the
two nonnegative kinetic terms over all centers.
-/

noncomputable section
namespace TSGA.ManyBody
open SSW TSGA.Localization MeasureTheory Set Metric
open scoped ComplexOrder Convolution

/-- Scalar weak Leibniz rule for bounded Sobolev functions and the weak
chain rule for the pullback by a Euclidean rigid motion. -/
structure WindowSobolevRules : Prop where
  product : ∀ {u v : Position → ℝ} {g h : Position → Position},
    (∀ x, u x ∈ Icc 0 1) → (∀ x, v x ∈ Icc 0 1) →
    (∀ i, WeakPartialOn univ i u (fun x => g x i)) →
    (∀ i, WeakPartialOn univ i v (fun x => h x i)) → ∀ i,
    WeakPartialOn univ i (fun x => u x*v x) (fun x => u x*h x i+v x*g x i)
  rigid : ∀ {u : Position → ℝ} {g : Position → Position},
    (∀ i, WeakPartialOn univ i u (fun x => g x i)) →
    ∀ (R : Position ≃ₗᵢ[ℝ] Position) (z : Position) (i : Fin 3),
    WeakPartialOn univ i (fun x => u (R (x-z))) (fun x => (R.symm (g (R (x-z)))) i)

/-- The constants in the rough finite trial, grouped by physical dimension. -/
def windowMassCost (H : FiniteEnergyInputs) (ρ : ℝ) (q : Position) : ℝ :=
  H.cTF*(1+H.κ₁)*ρ^(5/3:ℝ)+‖q‖^2/4*ρ

def windowFisherCost (H : FiniteEnergyInputs) (ρ : ℝ) : ℝ := 16*(1+H.κ₂)*ρ

private theorem massCost_nonneg (H : FiniteEnergyInputs) {ρ : ℝ} (hr : 0 ≤ ρ) (q : Position) :
    0 ≤ windowMassCost H ρ q := by
  dsimp [windowMassCost]
  positivity [H.cTF_nonneg,H.κ₁_nonneg,Real.rpow_nonneg hr (5/3:ℝ)]

private theorem fisherCost_nonneg (H : FiniteEnergyInputs) {ρ : ℝ} (hr : 0 ≤ ρ) :
    0 ≤ windowFisherCost H ρ := by dsimp [windowFisherCost]; positivity [H.κ₂_nonneg]

/-- Product-window estimate for a finite spin spiral, including the
representing state required before tensoring localized blocks. The inner
window is allowed to be periodic. Only its product with the physical
density and the weighted square of its derivative need finite integrals. -/
theorem FiniteEnergyInputs.product_window_upper (H : FiniteEnergyInputs) (rules : WindowSobolevRules)
    {f w : Position → ℝ} (hf : ∀ x, f x ∈ Icc 0 1) (hw : ∀ x, w x ∈ Icc 0 1)
    (fm : AEStronglyMeasurable f volume) (wm : AEStronglyMeasurable w volume)
    (g h : Position → Position) (gm : AEStronglyMeasurable g volume)
    (hm : AEStronglyMeasurable h volume)
    (df : ∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i))
    (dw : ∀ i, WeakPartialOn univ i (fun x => √(w x)) (fun x => h x i))
    (mass : Integrable (fun x => f x*w x))
    (gh : Integrable (fun x => f x*‖h x‖^2)) (gg : Integrable (fun x => w x*‖g x‖^2))
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    let F := cutoffSpiral (fun x => f x*w x) M q
    (∃ Γ : MixedState, feasible F Γ) ∧ energy F ≤
      windowMassCost H M.trace.re q*(∫ x, f x*w x) +
        windowFisherCost H M.trace.re*((∫ x, f x*‖h x‖^2)+(∫ x, w x*‖g x‖^2)) := by
  let W := fun x => f x*w x
  let V := fun x => √(f x) • h x + √(w x) • g x
  have funit (x : Position) : √(f x) ∈ Icc 0 1 := ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (hf x).2⟩
  have wunit (x : Position) : √(w x) ∈ Icc 0 1 := ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (hw x).2⟩
  have du (i : Fin 3) : WeakPartialOn univ i (fun x => √(W x)) (fun x => V x i) := by
    have eqn (x : Position) : √(W x) = √(f x)*√(w x) := Real.sqrt_mul (hf x).1 _
    simpa only [eqn,V,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] using rules.product funit wunit df dw i
  have Vm : AEStronglyMeasurable V volume := ((Real.continuous_sqrt.comp_aestronglyMeasurable fm).smul hm).add
    ((Real.continuous_sqrt.comp_aestronglyMeasurable wm).smul gm)
  have vb (x : Position) : ‖V x‖^2 ≤ 2*(f x*‖h x‖^2+w x*‖g x‖^2) := by
    let a := √(f x)*‖h x‖
    let b := √(w x)*‖g x‖
    have e : ‖V x‖ ≤ a+b := by
      simpa [V,a,b,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using norm_add_le (√(f x) • h x) (√(w x) • g x)
    have ha : a^2 = f x*‖h x‖^2 := by rw [show a = _ from rfl,mul_pow,Real.sq_sqrt (hf x).1]
    have hb : b^2 = w x*‖g x‖^2 := by rw [show b = _ from rfl,mul_pow,Real.sq_sqrt (hw x).1]
    nlinarith only [pow_le_pow_left₀ (norm_nonneg (V x)) e 2,sq_nonneg (a-b),ha,hb]
  have major : Integrable (fun x => 2*(f x*‖h x‖^2+w x*‖g x‖^2)) := (gh.add gg).const_mul 2
  have L2 : MemLp V 2 := (memLp_two_iff_integrable_sq_norm Vm).2
    (major.mono' (Vm.norm.pow 2) (ae_of_all _ fun x => by
      change ‖‖V x‖^2‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖V x‖)]
      exact vb x))
  have hcost := integral_mono (L2.integrable_norm_pow (p := 2) (by norm_num)) major vb
  rw [integral_const_mul,integral_add gh gg] at hcost
  have Wunit (x : Position) : W x ∈ Icc 0 1 :=
    ⟨mul_nonneg (hf x).1 (hw x).1,mul_le_one₀ (hf x).2 (hw x).1 (hw x).2⟩
  obtain ⟨Γ,hΓ⟩ := H.representable_cutoff (fun x => (Wunit x).1) mass V du L2 hM
  have hfΓ : feasible (fun x => (W x : ℂ) • M) Γ := hΓ
  let Λ := cutoffRotation W M q ⟨Γ,hfΓ⟩
  refine ⟨⟨Λ.val,Λ.property⟩,?_⟩
  have he := H.spiral_window_upper Wunit mass V du L2 hM q
  have hr : 0 ≤ M.trace.re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have h := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 8*(1+H.κ₂)*M.trace.re by positivity [H.κ₂_nonneg])
  change energy (cutoffSpiral W M q) ≤ _ at he ⊢
  dsimp only [windowMassCost,windowFisherCost,W] at *
  linarith only [he,h]

private theorem translated_cost {a b : Position → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun z => ∫ x, a x*b (x-z)) ∧
    (∫ z, ∫ x, a x*b (x-z)) = (∫ x, a x)*(∫ x, b x) := by
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let c := fun x => b (-x)
  have hc : Integrable c := hb.comp_neg
  have e : (fun z => ∫ x, a x*b (x-z)) = cutoffAverage c a := by
    funext z
    change (∫ x, a x*b (x-z)) = (∫ x, a x*b (-(z-x)))
    simp only [neg_sub]
  rw [e]
  refine ⟨cutoffAverage_integrable hc ha,?_⟩
  rw [integral_cutoffAverage hc ha,show (∫ x, c x) = ∫ x, b x from integral_neg_eq_self b volume]
  ring

/-- Integration over boundary centers. The windows are pulled back by the
same rigid motion as the physical tiling. All their gradient costs can be
integrated over the full space of centers. -/
theorem FiniteEnergyInputs.boundary_windows_upper (H : FiniteEnergyInputs) (rules : WindowSobolevRules)
    {f w : Position → ℝ} (hf : ∀ x, f x ∈ Icc 0 1) (hw : ∀ x, w x ∈ Icc 0 1)
    (fi : Integrable f) (wi : Integrable w) (g h : Position → Position)
    (gf : MemLp g 2) (gw : MemLp h 2)
    (df : ∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i))
    (dw : ∀ i, WeakPartialOn univ i (fun x => √(w x)) (fun x => h x i))
    {B : Set Position} (fin : volume B ≠ ⊤) (R : Position ≃ₗᵢ[ℝ] Position)
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    let E := fun z => energy (cutoffSpiral (fun x => f x*w (R (x-z))) M q)
    (∀ z, ∃ Γ : MixedState, feasible (cutoffSpiral (fun x => f x*w (R (x-z))) M q) Γ) ∧
    (∀ z, E z ≤ windowMassCost H M.trace.re q*(∫ x, w x) +
      windowFisherCost H M.trace.re*((∫ x, ‖h x‖^2)+(∫ x, ‖g x‖^2))) ∧
    (∫ z in B, E z) ≤
      windowMassCost H M.trace.re q * (∫ x, w x)*regionVolume B +
        windowFisherCost H M.trace.re * ((∫ x, f x)*(∫ x, ‖h x‖^2)+(∫ x, ‖g x‖^2)*(∫ x, w x)) := by
  intro E
  let a := fun x => w (R x)
  let b := fun x => ‖h (R x)‖^2
  let G := fun x => ‖g x‖^2
  let A := fun z => ∫ x, f x*b (x-z)
  let D := fun z => ∫ x, G x*a (x-z)
  let m := ∫ x, w x
  let u := windowMassCost H M.trace.re q
  let v := windowFisherCost H M.trace.re
  have hr : 0 ≤ M.trace.re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hu : 0 ≤ u := massCost_nonneg H hr q
  have hv : 0 ≤ v := fisherCost_nonneg H hr
  have ai : Integrable a := R.measurePreserving.integrable_comp_of_integrable wi
  have gi : Integrable G := gf.integrable_norm_pow (p := 2) (by norm_num)
  have bi : Integrable b := R.measurePreserving.integrable_comp_of_integrable
    (gw.integrable_norm_pow (p := 2) (by norm_num))
  have am : (∫ x, a x) = m := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding _
  have bm : (∫ x, b x) = ∫ x, ‖h x‖^2 := R.measurePreserving.integral_comp
    R.toHomeomorph.measurableEmbedding (fun x => ‖h x‖^2)
  have h₁ := translated_cost fi bi
  have h₂ := translated_cost gi ai
  have spec (z : Position) :
      (∃ Γ : MixedState, feasible (cutoffSpiral (fun x => f x*w (R (x-z))) M q) Γ) ∧
        E z ≤ u*m + v*(A z + D z) := by
    let W := fun x => a (x-z)
    let V := fun x => R.symm (h (R (x-z)))
    have wunit (x : Position) : W x ∈ Icc 0 1 := hw _
    have wm : Integrable W := ai.comp_sub_right z
    have Vm : MemLp V 2 := by
      apply (memLp_two_iff_integrable_sq_norm ?_).2
      · simpa only [V,R.symm.norm_map] using bi.comp_sub_right z
      · exact R.symm.continuous.comp_aestronglyMeasurable
          ((gw.comp_measurePreserving R.measurePreserving).comp_measurePreserving (measurePreserving_sub_right volume z)).aestronglyMeasurable
    have mass : Integrable (fun x => f x*W x) := wm.bdd_mul fi.aestronglyMeasurable
      (c := 1) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hf x).1] using (hf x).2)
    have kin : Integrable (fun x => f x*‖V x‖^2) :=
      (Vm.integrable_norm_pow (p := 2) (by norm_num)).bdd_mul fi.aestronglyMeasurable
        (c := 1) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hf x).1] using (hf x).2)
    have kin' : Integrable (fun x => W x*‖g x‖^2) := gi.bdd_mul wm.aestronglyMeasurable
      (c := 1) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (wunit x).1] using (wunit x).2)
    have prod := H.product_window_upper rules hf wunit fi.aestronglyMeasurable wm.aestronglyMeasurable
      g V gf.aestronglyMeasurable Vm.aestronglyMeasurable df (rules.rigid dw R z) mass kin kin' hM q
    have hmass := integral_mono mass wm (fun x => mul_le_of_le_one_left (wunit x).1 (hf x).2)
    have hh : (∫ x, W x) = m := (integral_sub_right_eq_self a z).trans am
    have ex : (∫ x, W x*‖g x‖^2) = D z := integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    have ey : (∫ x, f x*‖V x‖^2) = A z := by simp only [V,A,b,R.symm.norm_map]
    exact ⟨prod.1,prod.2.trans (by rw [ex,ey]; gcongr; exact hmass.trans_eq hh)⟩
  refine ⟨fun z => (spec z).1,?_,?_⟩
  · intro z
    have ax : A z ≤ ∫ x, b (x-z) := integral_mono_of_nonneg
      (ae_of_all _ fun x => mul_nonneg (hf x).1 (sq_nonneg _)) (bi.comp_sub_right z)
      (ae_of_all _ fun x => mul_le_of_le_one_left (sq_nonneg _) (hf x).2)
    have dx : D z ≤ ∫ x, G x := integral_mono_of_nonneg
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (hw _).1) gi
      (ae_of_all _ fun x => mul_le_of_le_one_right (sq_nonneg _) (hw _).2)
    rw [integral_sub_right_eq_self, bm] at ax
    exact (spec z).2.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (add_le_add ax dx) hv))
  have hA : Integrable A := h₁.1
  have hD : Integrable D := h₂.1
  have Apos (z : Position) : 0 ≤ A z := integral_nonneg fun x => mul_nonneg (hf x).1 (sq_nonneg _)
  have Dpos (z : Position) : 0 ≤ D z := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw _).1
  have hsum : IntegrableOn (fun z => u*m+v*(A z+D z)) B :=
    (integrableOn_const fin).add ((hA.add hD).integrableOn.const_mul v)
  have cmp : (∫ z in B, E z) ≤ ∫ z in B, u*m+v*(A z+D z) := by
    by_cases hi : IntegrableOn E B
    · exact integral_mono hi hsum (fun z => (spec z).2)
    · rw [integral_undef hi]
      exact integral_nonneg fun z => add_nonneg (mul_nonneg hu (integral_nonneg fun x => (hw x).1))
        (mul_nonneg hv (add_nonneg (Apos z) (Dpos z)))
  have bound := setIntegral_le_integral (s := B) (hA.add hD) (ae_of_all _ fun z => add_nonneg (Apos z) (Dpos z))
  have full : (∫ z, A z+D z) = (∫ x, f x)*(∫ x, ‖h x‖^2)+(∫ x, ‖g x‖^2)*m := by
    rw [integral_add hA hD,show (∫ z, A z) = _ from h₁.2,show (∫ z, D z) = _ from h₂.2,bm,am]
  have Bconst : Integrable (fun _ : Position => u*m) (volume.restrict B) := integrableOn_const fin
  have BI : Integrable (fun z => v*(A z+D z)) (volume.restrict B) := (hA.add hD).integrableOn.const_mul v
  rw [integral_add Bconst BI,
    setIntegral_const, integral_const_mul, smul_eq_mul] at cmp
  dsimp only [regionVolume]
  apply cmp.trans
  rw [mul_comm (volume.real B)]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (bound.trans_eq full) hv)

/-- Fubini for a nonnegative random profile bounded only in expectation.
The bound applies equally to a window and to its squared gradient. -/
theorem weighted_profile_average {P : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ]
    {a : Position → ℝ} (ha : Integrable a) (a₀ : ∀ x, 0 ≤ a x) {w : P → Position → ℝ}
    (hm : AEStronglyMeasurable (fun z : P × Position => w z.1 z.2) (μ.prod volume))
    (w₀ : ∀ j x, 0 ≤ w j x) {m : ℝ} (_m₀ : 0 ≤ m)
    (av : ∀ᵐ x ∂volume, Integrable (fun j => w j x) μ ∧ (∫ j, w j x ∂μ) ≤ m) :
    Integrable (fun z : P × Position => a z.2*w z.1 z.2) (μ.prod volume) ∧
      (∫ j, ∫ x, a x*w j x ∂volume ∂μ) ≤ m*(∫ x, a x) := by
  let F := fun z : P × Position => a z.2*w z.1 z.2
  have F₀ (z : P × Position) : 0 ≤ F z := mul_nonneg (a₀ _) (w₀ _ _)
  have Fm : AEStronglyMeasurable F (μ.prod volume) := ha.aestronglyMeasurable.comp_snd.mul hm
  have avg : ∀ᵐ x ∂volume, (∫ j, F (j,x) ∂μ) ≤ m*a x := by
    filter_upwards [av] with x hx
    change (∫ j, a x*w j x ∂μ) ≤ _
    rw [integral_const_mul,mul_comm m]
    exact mul_le_mul_of_nonneg_left hx.2 (a₀ x)
  have normAj (x : Position) : (∫ j, ‖F (j,x)‖ ∂μ) = ∫ j, F (j,x) ∂μ := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (F₀ _)]
  have FI : Integrable F (μ.prod volume) := by
    refine (integrable_prod_iff' Fm).2 ⟨?_,?_⟩
    · filter_upwards [av] with x hx
      exact hx.1.const_mul (a x)
    · apply (ha.const_mul m).mono' (Fm.norm.prod_swap.integral_prod_right')
      filter_upwards [avg] with x hx
      change ‖∫ j, ‖F (j,x)‖ ∂μ‖ ≤ m*a x
      rw [normAj,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun j => F₀ (j,x))]
      exact hx
  refine ⟨FI,?_⟩
  change (∫ j, ∫ x, F (j,x) ∂volume ∂μ) ≤ _
  rw [integral_integral_swap FI,← integral_const_mul]
  exact integral_mono_ae FI.integral_prod_right (ha.const_mul m) avg

/-- Averaged skeleton energy for the normalized skeleton window (half of the
physical skeleton). Multiply the constant matrix by two when using this
estimate for an upper tiling. The two pointwise averages are precisely the
cell mass and cell Fisher bounds in the skeleton construction. -/
theorem FiniteEnergyInputs.skeleton_windows_upper (H : FiniteEnergyInputs) (rules : WindowSobolevRules)
    {P : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ] {f : Position → ℝ}
    (hf : ∀ x, f x ∈ Icc 0 1) (fi : Integrable f) (g : Position → Position) (gf : MemLp g 2)
    (df : ∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i))
    (w : P → Position → ℝ) (h : P → Position → Position)
    (wh : ∀ j x, w j x ∈ Icc 0 1)
    (wm : AEStronglyMeasurable (fun z : P × Position => w z.1 z.2) (μ.prod volume))
    (hm : AEStronglyMeasurable (fun z : P × Position => h z.1 z.2) (μ.prod volume))
    (dw : ∀ᵐ j ∂μ, ∀ i, WeakPartialOn univ i (fun x => √(w j x)) (fun x => h j x i))
    {m s : ℝ} (m₀ : 0 ≤ m) (s₀ : 0 ≤ s)
    (wavg : ∀ᵐ x ∂volume, Integrable (fun j => w j x) μ ∧ (∫ j, w j x ∂μ) ≤ m)
    (havg : ∀ᵐ x ∂volume, Integrable (fun j => ‖h j x‖^2) μ ∧ (∫ j, ‖h j x‖^2 ∂μ) ≤ s)
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    let F := fun j => cutoffSpiral (fun x => f x*w j x) M q
    (∀ᵐ j ∂μ, ∃ Γ, feasible (F j) Γ) ∧
    (∃ G : P → ℝ, Integrable G μ ∧ ∀ᵐ j ∂μ, energy (F j) ≤ G j) ∧
    (∫ j, energy (F j) ∂μ) ≤ windowMassCost H M.trace.re q*(m*∫ x, f x) +
      windowFisherCost H M.trace.re*(s*(∫ x, f x)+m*(∫ x, ‖g x‖^2)) := by
  intro F
  let wt := fun z : P × Position => w z.1 z.2
  let n := fun z : P × Position => ‖h z.1 z.2‖^2
  have nm : AEStronglyMeasurable n (μ.prod volume) := hm.norm.pow 2
  have Gint := gf.integrable_norm_pow (p := 2) (by norm_num)
  have first := weighted_profile_average fi (fun x => (hf x).1) wm (fun j x => (wh j x).1) m₀ wavg
  have inner := weighted_profile_average fi (fun x => (hf x).1) nm (fun j x => sq_nonneg _) s₀ havg
  have outer := weighted_profile_average Gint (fun x => sq_nonneg _) wm (fun j x => (wh j x).1) m₀ wavg
  let mass := fun j => ∫ x, f x*w j x
  let grad := fun j => ∫ x, f x*‖h j x‖^2
  let outerGrad := fun j => ∫ x, ‖g x‖^2*w j x
  let u := windowMassCost H M.trace.re q
  let v := windowFisherCost H M.trace.re
  have hr : 0 ≤ M.trace.re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have u₀ := massCost_nonneg H hr q
  have v₀ := fisherCost_nonneg H hr
  have hprod : ∀ᵐ j ∂μ, (∃ Γ, feasible (F j) Γ) ∧ energy (F j) ≤ u*mass j+v*(grad j+outerGrad j) := by
    filter_upwards [dw,wm.prodMk_left,hm.prodMk_left,first.1.prod_right_ae,inner.1.prod_right_ae,
      outer.1.prod_right_ae] with j hweak hj hgj hmass hkin houter
    have hflip : (fun x => w j x*‖g x‖^2) = (fun x => ‖g x‖^2*w j x) := funext fun x => mul_comm _ _
    simpa only [hflip] using H.product_window_upper rules hf (wh j) fi.aestronglyMeasurable hj
      g (h j) gf.aestronglyMeasurable hgj df hweak hmass hkin (hflip ▸ houter) hM q
  have ma : Integrable mass μ := first.1.integral_prod_left
  have ga : Integrable grad μ := inner.1.integral_prod_left
  have oa : Integrable outerGrad μ := outer.1.integral_prod_left
  refine ⟨hprod.mono fun j hj => hj.1,⟨_,(ma.const_mul u).add ((ga.add oa).const_mul v),
    hprod.mono fun j hj => hj.2⟩,?_⟩
  by_cases hi : Integrable (fun j => energy (F j)) μ
  · have hh := integral_mono_ae hi ((ma.const_mul u).add ((ga.add oa).const_mul v))
      (hprod.mono fun j hj => hj.2)
    change _ ≤ ∫ j, u*mass j+v*(grad j+outerGrad j) ∂μ at hh
    have sumI : Integrable (fun j => grad j+outerGrad j) μ := ga.add oa
    rw [integral_add (ma.const_mul u) (sumI.const_mul v),integral_const_mul,integral_const_mul,integral_add ga oa] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left first.2 u₀)
      (mul_le_mul_of_nonneg_left (add_le_add inner.2 outer.2) v₀))
  · rw [integral_undef hi]
    exact add_nonneg (mul_nonneg u₀ (mul_nonneg m₀ (integral_nonneg fun x => (hf x).1)))
      (mul_nonneg v₀ (add_nonneg (mul_nonneg s₀ (integral_nonneg fun x => (hf x).1))
        (mul_nonneg m₀ (integral_nonneg fun x => sq_nonneg ‖g x‖))))

/-- At a fixed cell size and thickness the energies of the product windows
are uniformly bounded above over every translation and rotation. -/
theorem FiniteEnergyInputs.centered_window_bounded_above (H : FiniteEnergyInputs)
    (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients) (η : Mollifier)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d) {f : Position → ℝ}
    (hf : ∀ x, f x ∈ Icc 0 1) (fi : Integrable f) (g : Position → Position) (gf : MemLp g 2)
    (df : ∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i))
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    ∃ C : ℝ, ∀ (R : Position ≃ₗᵢ[ℝ] Position) (z : Position),
      energy (cutoffSpiral (fun x => f x*centeredWindow η a d R z x) M q) ≤ C := by
  have hv : volume (tetrahedron a) ≠ ⊤ := (isBounded_closedBall.subset (tetrahedron_subset ha)).measure_lt_top.ne
  obtain ⟨h,dh,L⟩ := smoothedIndicator_sqrt_sobolev sob (tetrahedron_open a).measurableSet hv η hd
  have wi := Integrable.of_integral_ne_zero ((tile_cutoff_mass η ha hd).trans_ne (tetrahedron_volume_pos ha).ne')
  exact ⟨_,fun R => (H.boundary_windows_upper W hf (smoothedIndicator_bounds _ η hd) fi wi
    g h gf L df dh (B := ∅) (by simp) R hM q).2.1⟩

/-- Uniform bound for the boundary centers at every orientation and
dilation in the averaging interval. Both the trial energy and the center
intensity use the same unshrunk tile volume. -/
theorem FiniteEnergyInputs.boundary_tetrahedron_upper (H : FiniteEnergyInputs) (rules : WindowSobolevRules)
    (sob : SobolevDifferenceQuotients) (diff : SobolevDifferenceBounds) (η : Mollifier) :
    ∃ c ≥ 0, ∀ {ℓ δ t : ℝ}, 0 < δ → δ ≤ ℓ/2 → t ∈ scaleInterval →
    ∀ {f : Position → ℝ}, (∀ x, f x ∈ Icc 0 1) → Integrable f →
    ∀ (g : Position → Position), MemLp g 2 →
    (∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i)) →
    ∀ {B : Set Position}, volume B ≠ ⊤ → ∀ (R : Position ≃ₗᵢ[ℝ] Position),
    ∀ {M : SpinMatrix}, M.PosSemidef → ∀ q : Position,
    let F := fun z => cutoffSpiral (fun x => f x*centeredWindow η (t*(ℓ-δ)) (t*δ) R z x) M q
    let V := regionVolume (tetrahedron (t*ℓ))
    (∀ z, ∃ Γ, feasible (F z) Γ) ∧
      (∫ z in B, energy (F z)/V) ≤ windowMassCost H M.trace.re q * regionVolume B +
        windowFisherCost H M.trace.re*(c/(ℓ*δ)*(∫ x, f x)+(∫ x, ‖g x‖^2)) := by
  obtain ⟨c,hc,area⟩ := tileCutoffAreaBound_of_sobolev sob diff η
  refine ⟨8*c,by positivity,?_⟩
  intro ℓ δ t hd hs ht f hf fi g gf df B fin R M hM q F V
  have he : 0 < ℓ := by linarith
  have ht' : 0 < t := by linarith [ht.1]
  have hl := mul_pos ht' (show 0 < ℓ-δ by linarith)
  have hδ := mul_pos ht' hd
  have hV : 0 < V := tetrahedron_volume_pos (mul_pos ht' he)
  let m := regionVolume (tetrahedron (t*(ℓ-δ)))
  let w := smoothedIndicator (tetrahedron (t*(ℓ-δ))) η (t*δ)
  have hm : (∫ x, w x) = m := tile_cutoff_mass η hl hδ
  have mpos : 0 < m := tetrahedron_volume_pos hl
  have mV : m ≤ V := measureReal_mono (μ := volume)
    (tetrahedron_mono (mul_le_mul_of_nonneg_left (sub_le_self ℓ hd.le) ht'.le))
    (ENNReal.toReal_pos_iff.mp hV).2.ne
  obtain ⟨h,hweak,L,hh⟩ := area _ _ hl hδ
  have hg := H.boundary_windows_upper rules hf (smoothedIndicator_bounds _ η hδ) fi
    (Integrable.of_integral_ne_zero (hm.trans_ne mpos.ne')) g h gf L df hweak fin R hM q
  refine ⟨hg.1,?_⟩
  let A := t*(ℓ-δ)*(t*δ)
  have hA : 0 < A := mul_pos hl hδ
  have small : ℓ*δ ≤ 8*A := by
    have ht2 : 1 ≤ 4*t^2 := by nlinarith only [sq_nonneg (t-1/2),ht.1]
    have hab := mul_le_mul_of_nonneg_right ht2 (mul_nonneg (show 0 ≤ ℓ-δ by linarith) hd.le)
    have hsum := mul_le_mul_of_nonneg_right hs hd.le
    dsimp [A]
    nlinarith only [hab,hsum]
  have kin : (∫ x, ‖h x‖^2) ≤ (8*c/(ℓ*δ))*V := by
    apply hh.trans
    change c*m/A ≤ _
    apply (div_le_iff₀ hA).2
    have eqn : (8*c/(ℓ*δ)*V)*A = c*V*(8*A)/(ℓ*δ) := by ring
    rw [eqn]
    apply (le_div_iff₀ (mul_pos he hd)).2
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left mV hc) (mul_nonneg he.le hd.le)).trans
      (mul_le_mul_of_nonneg_left small (mul_nonneg hc hV.le))
  let u := windowMassCost H M.trace.re q
  let v := windowFisherCost H M.trace.re
  have hr : 0 ≤ M.trace.re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have um := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left mV (massCost_nonneg H hr q))
    (show 0 ≤ regionVolume B from ENNReal.toReal_nonneg)
  have fint : 0 ≤ ∫ x, f x := integral_nonneg fun x => (hf x).1
  have gint : 0 ≤ ∫ x, ‖g x‖^2 := integral_nonneg fun x => sq_nonneg _
  have vg := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left kin fint)
    (mul_le_mul_of_nonneg_left mV gint)) (fisherCost_nonneg H hr)
  rw [integral_div]
  apply (div_le_iff₀ hV).2
  have bound := hg.2.2
  change (∫ z in B, energy (F z)) ≤ u*(∫ x, w x)*regionVolume B +
    v*((∫ x, f x)*(∫ x, ‖h x‖^2)+(∫ x, ‖g x‖^2)*(∫ x, w x)) at bound
  rw [hm] at bound
  apply bound.trans ((add_le_add um vg).trans_eq ?_)
  ring

/-- One constant controls the mass and kinetic coefficients for both the
ordinary windows and the skeleton whose height is at most two. -/
theorem FiniteEnergyInputs.window_constants (H : FiniteEnergyInputs) :
    ∃ C ≥ 0, ∀ {ρ : ℝ}, 0 ≤ ρ → ∀ q : Position,
      windowMassCost H ρ q ≤ C*(ρ*rateGrowth ρ q) ∧
      windowMassCost H (2*ρ) q ≤ C*(ρ*rateGrowth ρ q) ∧
      windowFisherCost H ρ ≤ C*ρ ∧ windowFisherCost H (2*ρ) ≤ C*ρ := by
  let u := H.cTF*(1+H.κ₁)
  let v := 16*(1+H.κ₂)
  let C := 1+(2:ℝ)^(5/3:ℝ)*u+2*v
  have hu : 0 ≤ u := by dsimp [u]; positivity [H.cTF_nonneg,H.κ₁_nonneg]
  have hv : 0 ≤ v := by dsimp [v]; positivity [H.κ₂_nonneg]
  have h2 : 1 ≤ (2:ℝ)^(5/3:ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hC : 1 ≤ C := by dsimp [C]; linarith only [mul_nonneg (zero_le_one.trans h2) hu,hv]
  have uC : u ≤ C := by dsimp [C]; nlinarith only [mul_le_mul_of_nonneg_right h2 hu,hv]
  have u2C : 2^(5/3:ℝ)*u ≤ C := by dsimp [C]; linarith only [hv]
  have vC : 2*v ≤ C := by dsimp [C]; linarith only [mul_nonneg (by positivity : (0:ℝ) ≤ 2^(5/3:ℝ)) hu]
  refine ⟨C,zero_le_one.trans hC,?_⟩
  intro ρ hr q
  have p : ρ^(5/3:ℝ)=ρ*ρ^(2/3:ℝ) := by
    calc
      _ = ρ^((1:ℝ)+2/3) := by norm_num
      _ = _ := by rw [Real.rpow_add' hr (by norm_num),Real.rpow_one]
  have arm : 0 ≤ ρ*ρ^(2/3:ℝ) := mul_nonneg hr (Real.rpow_nonneg hr _)
  have qt := mul_nonneg hr (sq_nonneg ‖q‖)
  have large : ρ*ρ^(2/3:ℝ)+ρ*‖q‖^2 ≤ ρ*rateGrowth ρ q := by
    dsimp [rateGrowth]
    nlinarith only [mul_nonneg hr (Real.rpow_nonneg hr (1/3:ℝ))]
  have hq := mul_le_mul_of_nonneg_right hC qt
  have unit := mul_le_mul_of_nonneg_right uC arm
  have twice := mul_le_mul_of_nonneg_right u2C arm
  have ul := mul_le_mul_of_nonneg_left large (zero_le_one.trans hC)
  refine ⟨?_,?_,?_,?_⟩
  · change u*ρ^(5/3:ℝ)+_ ≤ _
    rw [p]
    nlinarith only [unit,hq,ul,qt]
  · change u*(2*ρ)^(5/3:ℝ)+_ ≤ _
    rw [Real.mul_rpow (by norm_num) hr,p]
    nlinarith only [twice,hq,ul,qt]
  · exact mul_le_mul_of_nonneg_right (by linarith only [hv,vC] : v ≤ C) hr
  · change v*(2*ρ) ≤ _
    linarith only [mul_le_mul_of_nonneg_right vC hr]

/-- The square-integrability estimate for any given weak gradient of the
physical outer cutoff follows from uniqueness of distributional derivatives. -/
theorem smoothedIndicator_gradient_memLp (sob : SobolevDifferenceQuotients)
    {Ω : Set Position} (hm : MeasurableSet Ω) (hv : volume Ω ≠ ⊤) (η : Mollifier)
    {d : ℝ} (hd : 0 < d) (g : Position → Position)
    (hw : ∀ i, WeakPartialOn univ i (fun x => √(smoothedIndicator Ω η d x)) (fun x => g x i)) :
    MemLp g 2 := by
  obtain ⟨g₀,h₀,L⟩ := smoothedIndicator_sqrt_sobolev sob hm hv η hd
  have eqi (i : Fin 3) : (fun x => g₀ x i) =ᵐ[volume] fun x => g x i := by
    apply ae_eq_of_integral_contDiff_smul_eq (locallyIntegrableOn_univ.mp (h₀ i).2.1)
      (locallyIntegrableOn_univ.mp (hw i).2.1)
    intro ψ hψ hcompact
    have he := ((h₀ i).2.2 ψ hψ hcompact (subset_univ _)).symm.trans
      ((hw i).2.2 ψ hψ hcompact (subset_univ _))
    simpa only [Measure.restrict_univ,neg_inj] using he
  exact L.ae_eq ((ae_all_iff.mpr eqi).mono fun x hx => by ext i; exact hx i)

/-- At a fixed frame and dilation integrate the full Coulomb energies of the
centers. Interior centers have their exact energy, exterior centers contribute
vacuum, and only the boundary centers use the rough product-window estimate. -/
theorem FiniteEnergyInputs.all_centers_upper (H : FiniteEnergyInputs) (rules : WindowSobolevRules)
    (sob : SobolevDifferenceQuotients) (diff : SobolevDifferenceBounds) (η : Mollifier) :
    ∃ c ≥ 0, ∀ χ : Mollifier, ∃ a > 0, ∀ {Ω : Set Position}, IsOpen Ω → Bornology.IsBounded Ω →
    0 < regionVolume Ω → ∀ {d : ℝ}, 0 < d → ∀ (g : Position → Position),
    (∀ i, WeakPartialOn univ i (fun x => √(smoothedIndicator Ω χ d x)) (fun x => g x i)) →
    ∀ {ℓ δ t : ℝ}, 0 < δ → δ ≤ ℓ/2 → t ∈ scaleInterval → ∀ R : Position ≃ₗᵢ[ℝ] Position,
    ∀ {M : SpinMatrix}, M.PosSemidef → ∀ q : Position,
    let ξ := centeredWindow η (t*(ℓ-δ)) (t*δ) R
    let f := smoothedIndicator Ω χ d
    let B := thickening (a*(ℓ+δ+d)) (frontier Ω)
    let V := regionVolume (tetrahedron (t*ℓ))
    let E := fun z => energy (cutoffSpiral (fun x => f x*ξ z x) M q)/V
    Integrable E →
    (∫ z, E z) ≤ (∫ z in Ω \ B, energy (cutoffSpiral (ξ z) M q)/V) +
      (windowMassCost H M.trace.re q * regionVolume B +
        windowFisherCost H M.trace.re*(c/(ℓ*δ)*regionVolume Ω+(∫ x, ‖g x‖^2))) := by
  obtain ⟨c,hc,raw⟩ := H.boundary_tetrahedron_upper rules sob diff η
  refine ⟨c,hc,?_⟩
  intro χ
  obtain ⟨a,ha,inside⟩ := centeredWindow_boundary η χ
  refine ⟨2*a,by positivity,?_⟩
  intro Ω hop hbd hv d hd g hg ℓ δ t hδ hs ht R M hM q ξ f B V E hi
  have he : 0 < ℓ := by linarith
  have htpos : 0 < t := by linarith [ht.1]
  have hfinite : volume B ≠ ⊤ :=
    (hbd.closure.subset frontier_subset_closure).thickening.measure_lt_top.ne
  have G := smoothedIndicator_gradient_memLp sob hop.measurableSet hbd.measure_lt_top.ne χ hd g hg
  have mass : (∫ x, f x) = regionVolume Ω := by
    classical
    have hc : Integrable (Ω.indicator (fun _ => (1:ℝ))) :=
      (integrable_indicator_iff hop.measurableSet).2 (integrableOn_const hbd.measure_lt_top.ne)
    change (∫ x, smoothedIndicator Ω χ d x) = regionVolume Ω
    rw [smoothedIndicator,integral_convolution _ hc (χ.scaled_integrable hd),
      χ.scaled_mass hd,integral_indicator hop.measurableSet]
    simp [regionVolume]
  have fi := Integrable.of_integral_ne_zero (mass.trans_ne hv.ne')
  have outer : ∀ z ∉ B, ∀ x, f x*ξ z x = ξ z x*Ω.indicator (fun _ => (1:ℝ)) z := by
    intro z hz x
    have hsize : t*(ℓ-δ)+t*δ+d ≤ 2*(ℓ+δ+d) := by
      nlinarith only [mul_le_mul_of_nonneg_right ht.2 he.le,hδ,hd,he]
    have hm : a*(t*(ℓ-δ)+t*δ+d) ≤ (2*a)*(ℓ+δ+d) := by
      linarith only [mul_le_mul_of_nonneg_left hsize ha.le]
    have hz' : z ∉ thickening (a*(t*(ℓ-δ)+t*δ+d)) (frontier Ω) := fun h => hz (thickening_mono hm _ h)
    rw [mul_comm]
    exact inside hop (mul_pos htpos (by linarith)) (mul_pos htpos hδ) hd R z hz' x
  have full (z : Position) (hz : z ∈ Ω \ B) : E z = energy (cutoffSpiral (ξ z) M q)/V := by
    have eqn : (fun x => f x*ξ z x) = ξ z := funext fun x => by simpa [hz.1] using outer z hz.2 x
    simp only [E,eqn]
  have vacuum (z : Position) (hz : z ∉ (Ω \ B) ∪ B) : E z = 0 := by
    have hB : z ∉ B := fun h => hz (Or.inr h)
    have hΩ : z ∉ Ω := fun h => hz (Or.inl ⟨h,hB⟩)
    have eqn : cutoffSpiral (fun x => f x*ξ z x) M q = 0 := by
      ext x i j
      simp [cutoffSpiral,outer z hB x,hΩ]
    simp only [E,eqn,energy_vacuum,zero_div]
  have bm := (raw hδ hs ht (smoothedIndicator_bounds Ω χ hd) fi g G hg hfinite R hM q).2
  change (∫ z in B, E z) ≤ windowMassCost H M.trace.re q*regionVolume B+
    windowFisherCost H M.trace.re*(c/(ℓ*δ)*(∫ x, f x)+(∫ x, ‖g x‖^2)) at bm
  rw [mass] at bm
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero vacuum,
    setIntegral_union (disjoint_left.mpr fun _ h => h.2) isOpen_thickening.measurableSet hi.integrableOn hi.integrableOn]
  have ie : (∫ z in Ω \ B, E z) = ∫ z in Ω \ B, energy (cutoffSpiral (ξ z) M q)/V :=
    setIntegral_congr_fun (hop.measurableSet.diff isOpen_thickening.measurableSet) full
  rw [ie]
  exact add_le_add (le_refl _) bm

end TSGA.ManyBody
