import TSGA.CoulombCutoffArea
import TSGA.DensityMeasurability
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! # Measurability of the finite Coulomb tiling energies

We use the Borel property of the grand-canonical constrained search on
integrable spin densities. The smearing kernel is only Lebesgue integrable.
Replacing it inside the convolution by its measurable representative makes
the density jointly Borel in the length, width, direction and position.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization Set
open scoped ComplexOrder InnerProductSpace

local instance : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace (Lp ℂ 1 (volume : Measure Position)) := borel _
local instance : BorelSpace (Lp ℂ 1 (volume : Measure Position)) := ⟨rfl⟩

local instance : SecondCountableTopology (Lp ℂ 1 (volume : Measure Position)) := Lp.SecondCountableTopology
local instance : OpensMeasurableSpace (Fin 2 → Lp ℂ 1 (volume : Measure Position)) := Pi.opensMeasurableSpace
local instance : SecondCountableTopology (Fin 2 → Lp ℂ 1 (volume : Measure Position)) := inferInstance
local instance : OpensMeasurableSpace (Fin 2 → Fin 2 → Lp ℂ 1 (volume : Measure Position)) := Pi.opensMeasurableSpace

/-- The standard DFT measurability input on the four complex entries in L¹.
The usual lower semicontinuity of the extended universal functional gives
this form by setting its value to zero on the infinite-energy locus, as in
the real-valued definition of `levyLieb`. -/
def LevyLiebBorel : Prop :=
  ∃ F : (Fin 2 → Fin 2 → Lp ℂ 1 (volume : Measure Position)) → ℝ,
    Measurable F ∧ ∀ (u : Position → SpinMatrix)
      (h : ∀ i j, MemLp (fun x => u x i j) 1 volume),
      F (fun i j => (h i j).toLp _) = levyLieb u

/-- The constrained search on L¹ with the value infinity at infeasible
densities. These are the usual conventions for lower semicontinuity. -/
def extendedL1ConstrainedSearch (v : Fin 2 → Fin 2 → Lp ℂ 1 (volume : Measure Position)) :
    WithTop ℝ := by
  classical
  let u := fun x i j => v i j x
  exact if ∃ Γ, feasible u Γ then ↑(levyLieb u) else ⊤

/-- Lower semicontinuity of the extended constrained search on L¹ suffices
for the measurability input, including the real functional's empty-search
convention. -/
theorem levyLiebBorel_of_lowerSemicontinuous (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch) :
    LevyLiebBorel := by
  classical
  refine ⟨fun v => (extendedL1ConstrainedSearch v).untopD 0,
    (WithTop.measurable_untopD 0).comp hlsc.measurable, ?_⟩
  intro u h
  let v := fun i j => (h i j).toLp _
  let w := fun x i j => v i j x
  have hae : w =ᵐ[volume] u := by
    have hentries (i j : Fin 2) : (fun x => w x i j) =ᵐ[volume] (fun x => u x i j) :=
      (h i j).coeFn_toLp
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (hentries i)] with x hx
    exact funext fun i => funext (hx i)
  have hval : levyLieb w = levyLieb u := by
    apply congrArg sInf
    ext e
    exact ⟨fun ⟨Γ,hΓ,hE⟩ => ⟨Γ,hΓ.trans hae,hE⟩, fun ⟨Γ,hΓ,hE⟩ => ⟨Γ,hΓ.trans hae.symm,hE⟩⟩
  rw [← hval]
  change (if ∃ Γ, feasible w Γ then (↑(levyLieb w) : WithTop ℝ) else ⊤).untopD 0 = levyLieb w
  split_ifs with hrep
  · rfl
  · have hempty : {e | ∃ Γ : MixedState, feasible w Γ ∧ e = Γ.kinetic + Γ.interaction} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro e ⟨Γ,hΓ,_⟩
      exact hrep ⟨Γ,hΓ⟩
    simp [levyLieb,hempty]

/-- A jointly Borel family with integrable slices defines a Borel map
into the separable space L¹. Distances to fixed elements are integrals. -/
private theorem measurable_L1_family {P : Type*} [MeasurableSpace P]
    {f : P → Position → ℂ} (hf : Measurable (Function.uncurry f))
    (h : ∀ s, MemLp (f s) 1 volume) : Measurable (fun s => (h s).toLp (f s)) := by
  classical
  let F := fun s => (h s).toLp (f s)
  have distM (g : Lp ℂ 1 (volume : Measure Position)) : Measurable (fun s => dist (F s) g) := by
    have hg := (Lp.stronglyMeasurable g).measurable
    have hm : Measurable (fun z : P × Position => ‖f z.1 z.2 - g z.2‖ₑ) :=
      (hf.sub (hg.comp measurable_snd)).enorm
    convert (hm.lintegral_prod_right' (ν := volume)).ennreal_toReal using 1
    funext s
    rw [dist_edist]
    congr 1
    conv_lhs => rhs; rw [← Lp.toLp_coeFn g (Lp.memLp g)]
    exact (Lp.edist_toLp_toLp _ _ _ _).trans
      (eLpNorm_one_eq_lintegral_eNorm ((h s).sub (Lp.memLp g)).aestronglyMeasurable)
  apply measurable_of_isOpen
  intro U hU
  choose r hr hsub using fun x : U => Metric.isOpen_iff.mp hU x x.property
  let B := fun x : U => Metric.ball x.val (r x)
  obtain ⟨T,hT,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable B fun _ => Metric.isOpen_ball
  have hfull : (⋃ x, B x) = U := by
    refine (iUnion_subset fun x => hsub x).antisymm ?_
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, Metric.mem_ball_self (hr _)⟩
  rw [← hfull, ← hcover, preimage_iUnion₂]
  exact MeasurableSet.biUnion hT fun x _ => measurableSet_lt (distM x) measurable_const

/-- Fubini supplies an integrable family in L¹ for jointly integrable Borel
slices. Each individual representative agrees almost everywhere with its
original scalar field. -/
theorem exists_integrable_L1_family {P : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ]
    {f : P → Position → ℂ} (hm : Measurable (Function.uncurry f))
    (h : ∀ s, Integrable (f s) volume) (hj : Integrable (Function.uncurry f) (μ.prod volume)) :
    ∃ v : P → Lp ℂ 1 (volume : Measure Position), Integrable v μ ∧ ∀ s, ⇑(v s) =ᵐ[volume] f s := by
  let v := fun s => (h s).toL1 (f s)
  have hm' := measurable_L1_family hm (fun s => memLp_one_iff_integrable.mpr (h s))
  have he (s : P) : ⇑(v s) =ᵐ[volume] f s := (h s).coeFn_toL1
  refine ⟨v, ?_, he⟩
  apply (hj.integral_norm_prod_left).mono' hm'.aestronglyMeasurable
  filter_upwards with s
  rw [L1.norm_eq_integral_norm]
  exact (integral_congr_ae ((he s).mono fun _ hx => congrArg norm hx)).le

private theorem measurable_tileCutoff {P : Type*} [MeasurableSpace P]
    (η : Mollifier) {a b : P → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hpos : ∀ s, 0 < b s) :
    Measurable (fun z : P × Position => smoothedIndicator (tetrahedron (a z.1)) η (b z.1) z.2) := by
  classical
  let η' := η.integrable.aestronglyMeasurable.mk η.kernel
  have hη : Measurable η' := η.integrable.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  let region : Set ((P × Position) × Position) := {z | z.2 ∈ tetrahedron (a z.1.1)}
  have hreg : MeasurableSet region := by
    let R := (P × Position) × Position
    have hc (i : Fin 3) : Measurable (fun z : R => z.2 i) := by
      exact (show Continuous (fun x : Position => x i) by fun_prop).measurable.comp measurable_snd
    have he : Measurable (fun z : R => a z.1.1) := ha.comp (measurable_fst.comp measurable_fst)
    have hfirst := (hc 1).add (he.div_const 4)
    have hsecond := (hc 0).add ((he.const_mul 3).div_const 8)
    exact (measurableSet_lt (continuous_abs.measurable.comp (hc 2)) hfirst).inter
      ((measurableSet_lt hfirst hsecond).inter (measurableSet_lt hsecond (he.div_const 2)))
  let g := fun z : (P × Position) × Position =>
    region.indicator (fun _ => (1:ℝ)) z *
      ((b z.1.1 ^ 3)⁻¹ * η' ((b z.1.1)⁻¹ • (z.1.2-z.2)))
  have hg : Measurable g := by
    have hscale : Measurable (fun z : (P × Position) × Position => b z.1.1) :=
      hb.comp (measurable_fst.comp measurable_fst)
    have harg : Measurable (fun z : (P × Position) × Position => (b z.1.1)⁻¹ • (z.1.2 - z.2)) :=
      hscale.inv.smul ((measurable_snd.comp measurable_fst).sub measurable_snd)
    have hind : Measurable (region.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hreg
    convert hind.mul ((hscale.pow_const (3 : ℕ)).inv.mul (hη.comp harg)) using 1
    funext z
    simp only [g, Pi.mul_apply, Pi.inv_apply, Function.comp_apply]
  convert hg.stronglyMeasurable.integral_prod_right' (ν := volume) |>.measurable using 1
  funext z
  apply integral_congr_ae
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  have hmap := (Measure.quasiMeasurePreserving_smul (volume : Measure Position)
    (inv_ne_zero (hpos z.1).ne')).comp (volume.measurePreserving_sub_left z.2).quasiMeasurePreserving
  filter_upwards [hmap.ae_eq_comp η.integrable.aestronglyMeasurable.ae_eq_mk] with y hy
  change _ * (_ * η.kernel ((b z.1)⁻¹ • (z.2-y))) = _
  change η.kernel ((b z.1)⁻¹ • (z.2-y)) = η' _ at hy
  dsimp only [g]
  rw [hy]
  rfl

theorem measurable_smoothedTetrahedron (η : Mollifier) (ℓ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (smoothedIndicator (tetrahedron ℓ) η δ) := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  have h : Measurable (fun z : Position × Position => f z.2) :=
    measurable_tileCutoff (P := Position) η (a := fun _ => ℓ) (b := fun _ => δ)
      measurable_const measurable_const (fun _ => hδ)
  change Measurable ((fun z : Position × Position => f z.2) ∘ (Prod.mk (0 : Position)))
  exact h.comp measurable_prodMk_left

theorem measurable_coulomb_energy_family {P : Type*} [MeasurableSpace P]
    (borel : LevyLiebBorel) (u : P → Position → SpinMatrix)
    (hm : ∀ i j, Measurable (fun z : P × Position => u z.1 z.2 i j))
    (h1 : ∀ s i j, MemLp (fun x => u s x i j) 1 volume) :
    Measurable (fun s => energy (u s)) := by
  obtain ⟨F,hF,hval⟩ := borel
  have hll : Measurable (fun s => levyLieb (u s)) := by
    have aux := hF.comp (Measurable.of_eval fun i => Measurable.of_eval fun j =>
      measurable_L1_family (f := fun s x => u s x i j) (hm i j) (fun s => h1 s i j))
    simpa only [Function.comp_def, hval] using aux
  let r := fun z : P × Position => (u z.1 z.2).trace.re
  have hr : Measurable r := Complex.measurable_re.comp (Finset.measurable_fun_sum _ fun i _ => hm i i)
  have hh : Measurable (fun z : (P × Position) × Position =>
      r z.1 * r (z.1.1,z.2) / ‖z.1.2-z.2‖) := by fun_prop (disch := assumption)
  exact hll.sub ((hh.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable).div_const 2)

/-- Angular averaging preserves Borel dependence on the length and width. -/
theorem measurable_averagedTile_family {P : Type*} [MeasurableSpace P]
    (borel : LevyLiebBorel) (η : Mollifier) (M : SpinMatrix) (q : Position)
    {a b : P → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hap : ∀ s, 0 < a s) (hbp : ∀ s, 0 < b s) :
    Measurable (fun s => averagedTile energy η M q (a s) (b s)) := by
  let S := Metric.sphere (0 : Position) 1
  let u := fun (p : P × S) (x : Position) =>
    cutoffSpiral (smoothedIndicator (tetrahedron (a p.1)) η (b p.1)) M (‖q‖ • (p.2 : Position)) x
  have hf := measurable_tileCutoff η (ha.comp (measurable_fst (β := S)))
    (hb.comp measurable_fst) (fun z => hbp z.1)
  have hu (i j : Fin 2) : Measurable (fun z : (P × S) × Position => u z.1 z.2 i j) := by
    dsimp only [u,cutoffSpiral,Matrix.smul_apply,smul_eq_mul]
    simp_rw [rotate_by_entry]
    apply (Complex.measurable_ofReal.comp hf).mul
    unfold phaseFactor
    fun_prop
  have h1 (s : P × S) (i j : Fin 2) : MemLp (fun x => u s x i j) 1 volume := by
    let f := smoothedIndicator (tetrahedron (a s.1)) η (b s.1)
    have hi : Integrable f := Integrable.of_integral_ne_zero
      ((tile_cutoff_mass η (hap s.1) (hbp s.1)).trans_ne (tetrahedron_volume_pos (hap s.1)).ne')
    apply memLp_one_iff_integrable.mpr
    apply (hi.mul_const ‖M i j‖).mono' ((hu i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    filter_upwards with x
    simp [u,cutoffSpiral,rotate_by_entry,phaseFactor,Complex.norm_exp, f,
      abs_of_nonneg (smoothedIndicator_bounds _ η (hbp s.1) x).1]
  have he := measurable_coulomb_energy_family borel u hu h1
  have hvol : Measurable (fun p : P × S => regionVolume (tetrahedron (a p.1))) := by
    simp_rw [tetrahedron_volume (hap _)]
    fun_prop (disch := assumption)
  exact (he.div hvol).stronglyMeasurable.integral_prod_right' |>.measurable

theorem coulomb_dilation_aeMeasurable (borel : LevyLiebBorel) (η : Mollifier)
    (M : SpinMatrix) (q : Position) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) :
    AEStronglyMeasurable (fun t => averagedTile energy η M q (t * ℓ) (t * δ))
      (volume.restrict scaleInterval) := by
  let f := fun t : ℝ => max (1/2 : ℝ) t
  have hm : Measurable f := measurable_const.max measurable_id
  have hp (t : ℝ) : 0 < f t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (le_max_left _ _)
  apply (measurable_averagedTile_family borel η M q (hm.mul_const ℓ) (hm.mul_const δ)
    (fun s => mul_pos (hp s) hℓ) (fun s => mul_pos (hp s) hδ)).aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
  change averagedTile _ _ _ _ (max (1/2 : ℝ) t * ℓ) (max (1/2 : ℝ) t * δ) = _
  rw [max_eq_right ht.1]

theorem coulomb_tetrahedronDilationMeasurable (borel : LevyLiebBorel) (η : Mollifier)
    (M : SpinMatrix) (q : Position) : TetrahedronDilationMeasurable energy η M q := by
  intro ℓ hℓ
  simpa using coulomb_dilation_aeMeasurable borel η M q (show 0 < ℓ-1 by linarith) zero_lt_one

/-- The rough Coulomb bounds are uniform on the compact scale interval.
The dilation integrability therefore needs no separate finite tiling input. -/
theorem coulomb_tileDilationIntegrable (borel : LevyLiebBorel) (η : Mollifier)
    (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (K : ℝ) : TileDilationIntegrable energy η K := by
  intro M hM q ℓ δ hℓ hδ _
  obtain ⟨B,hB,rough⟩ := H.exists_rough_constant diff quant η
  let ρ := M.trace.re
  let floor := B * (ρ * ρ^(1/3:ℝ))
  let C := |floor| + |B * (ρ * rateGrowth ρ q + ρ / ((ℓ/2)*(δ/2)))|
  have hb : 0 ≤ B := zero_le_one.trans hB
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hf : 0 ≤ floor := mul_nonneg hb (mul_nonneg hr (Real.rpow_nonneg hr _))
  apply (scaleWeight_integrableOn.const_mul C).mono'
    ((coulomb_dilation_aeMeasurable borel η M q hℓ hδ).mul scaleWeight_integrableOn.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
  have ht0 : (1/2:ℝ) ≤ t := ht.1
  have hp : 0 < t := by linarith
  have hd : (ℓ/2)*(δ/2) ≤ (t*ℓ)*(t*δ) := by
    apply mul_le_mul <;> nlinarith [mul_le_mul_of_nonneg_right ht0 hℓ.le,
      mul_le_mul_of_nonneg_right ht0 hδ.le, mul_pos hp hℓ]
  have hrdiv := div_le_div_of_nonneg_left hr (by positivity : 0 < (ℓ/2)*(δ/2)) hd
  obtain ⟨hlo,hhi⟩ := rough B le_rfl M hM q (t*ℓ) (t*δ) (mul_pos hp hℓ) (mul_pos hp hδ)
  have htop := mul_le_mul_of_nonneg_left (add_le_add_right hrdiv (ρ * rateGrowth ρ q)) hb
  have hbound : |averagedTile energy η M q (t*ℓ) (t*δ)| ≤ C := by
    change -B * (ρ * ρ^(1/3:ℝ)) ≤ _ at hlo
    change _ + floor ≤ B*(ρ*rateGrowth ρ q + ρ/((t*ℓ)*(t*δ))) at hhi
    have hv := le_abs_self (B * (ρ * rateGrowth ρ q + ρ / ((ℓ/2)*(δ/2))))
    dsimp only [C]
    rw [abs_of_nonneg hf,abs_le]
    constructor
    · dsimp only [floor] at *
      linarith [abs_nonneg (B * (ρ * rateGrowth ρ q + ρ / ((ℓ/2)*(δ/2))))]
    · linarith
  have hw : 0 ≤ scaleWeight t := inv_nonneg.mpr (pow_nonneg hp.le _)
  change ‖averagedTile energy η M q (t*ℓ) (t*δ) * scaleWeight t‖ ≤ C * scaleWeight t
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right hbound hw

end TSGA.ManyBody
