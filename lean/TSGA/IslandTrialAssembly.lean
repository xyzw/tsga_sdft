import TSGA.IslandFockTrial
import TSGA.IslandChargeL2
import TSGA.IslandInteriorTrial
import TSGA.IslandPairMoment
import TSGA.IslandExteriorGeometry
import TSGA.IslandOverlapTrial
import TSGA.CoulombReplacement

/-! # The Coulomb island trial and the two ordered additions -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped NNReal MatrixOrder ComplexOrder

universe u
variable {Ω : Type u} {Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Measure Z} [SFinite ι] {P : PoissonIslandProcess μ ι}

/-- Measurable selection in the graph of the density and the two energy
observables on normal states. Only the scalar energies of the selected
family enter the subsequent barycenter. -/
def FockEnergySelection (μ : Measure Ω) : Prop :=
  ∀ (U : Ω → Position → SpinMatrix) (k w : Ω → ℝ),
    (∀ i j, Integrable (fun z : Ω × Position => U z.1 z.2 i j) (μ.prod volume)) →
    Integrable k μ → Integrable w μ →
    (∀ᵐ ω ∂μ, ∃ Γ, feasible (U ω) Γ ∧ Γ.kinetic ≤ k ω ∧ Γ.interaction ≤ w ω) →
    ∃ s : Ω → MixedState, AEStronglyMeasurable (fun ω => (s ω).kinetic + (s ω).interaction) μ ∧
      ∀ᵐ ω ∂μ, feasible (U ω) (s ω) ∧ (s ω).kinetic ≤ k ω ∧ (s ω).interaction ≤ w ω

/-- One-body and Fock-space facts used for both ordered pairs and all radii. -/
structure IslandFockInputs (μ : Measure Ω) where
  tensor : DisjointFockTensorization
  barycenter : FockBarycenterRealization μ
  selection : FockEnergySelection μ
  oneBody : FiniteEnergyInputs
  fisher : FisherSobolevCalculus.{u}
  minimizer : ∀ (B : Density) (S : MatrixGradient), SqrtRegular B S → MemLp B.charge 2 →
    ∃ Γ, feasible B.matrix Γ ∧ Γ.kinetic+Γ.interaction = levyLieb B.matrix
  restriction : ∀ (Γ : MixedState) (B : Density), SpatialFockRestriction Γ B
  coulomb_pos : ∀ u, Integrable (directKernel u u) pairVolume → 0 ≤ hartree u

/-- The deterministic analytic domain of the ordered density addition. -/
structure IslandDensityDomain (B D : Density) extends IslandChargeDomain B D where
  background_entries : ∀ i j, Integrable (fun x => B.matrix x i j)
  added_entries : ∀ i j, Integrable (fun x => D.matrix x i j)
  background_square : MemLp B.charge 2
  added_mass : Integrable D.charge
  added_square : Integrable (fun x => D.charge x^2)
  added_tf : Integrable (fun x => D.charge x^(5/3:ℝ))

/-- L¹∩L² charges and measurable spin entries suffice for every deterministic
form-domain condition in the island construction. -/
theorem IslandDensityDomain.of_L1_L2 {B D : Density} (b : Measurable B.charge) (d : Measurable D.charge)
    (bm : ∀ i j, AEStronglyMeasurable (fun x => B.matrix x i j) volume)
    (dm : ∀ i j, AEStronglyMeasurable (fun x => D.matrix x i j) volume)
    (bi : Integrable B.charge) (di : Integrable D.charge) (b₂ : MemLp B.charge 2) (d₂ : MemLp D.charge 2) :
    IslandDensityDomain B D := by
  have entries (N : Density) (hn : Integrable N.charge)
      (hm : ∀ i j, AEStronglyMeasurable (fun x => N.matrix x i j) volume) (i j : Fin 2) :
      Integrable (fun x => N.matrix x i j) := hn.mono' (hm i j) (ae_of_all _ fun x =>
    (SSW.norm_entry_le_hs _ i j).trans (SSW.hilbertSchmidt_le_trace (N.positive x)))
  exact ⟨IslandChargeDomain.of_L1_L2 b d bi di b₂.integrable_sq d₂.integrable_sq,entries _ bi bm,
    entries _ di dm,b₂,di,d₂.integrable_sq,island_moment_integrable d D.charge_nonneg di d₂.integrable_sq
      (by norm_num) (by norm_num)⟩

private theorem background_direct {B D : Density} (h : IslandChargeDomain B D) :
    Integrable (directKernel B.charge B.charge) pairVolume := by
  apply h.direct.mono' (((h.background.comp measurable_fst).mul (h.background.comp measurable_snd)).div
    (measurable_fst.sub measurable_snd).norm).aestronglyMeasurable
  apply ae_of_all
  rintro ⟨x,y⟩
  change ‖B.charge x*B.charge y/‖x-y‖‖ ≤ _
  rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg (B.charge_nonneg _) (B.charge_nonneg _)) (norm_nonneg _))]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul (le_add_of_nonneg_right (D.charge_nonneg x)) (le_add_of_nonneg_right (D.charge_nonneg y))
    (B.charge_nonneg y) (add_nonneg (B.charge_nonneg x) (D.charge_nonneg x))

namespace IslandMasks
variable {ε r K : ℝ} (m : IslandMasks μ (ε/2))

/-- Select the interior one-body trials measurably. Their nonnegative energies
are integrably dominated by the two independently calculated ceilings. -/
theorem select_interior (A : IslandFockInputs μ) (L : InteriorMaskData m r K)
    {B D : Density} (G : IslandGradients B D ε) (M : m.MeasurableFields) (h : IslandDensityDomain B D)
    (he : 0 < ε) :
    ∃ s : Ω → MixedState, Integrable (fun ω => (s ω).kinetic+(s ω).interaction) μ ∧
      ∀ᵐ ω ∂μ, feasible (L.localDensity B D ω).matrix (s ω) ∧
        (s ω).kinetic ≤ A.oneBody.interiorConstant*(chargeMoment (L.localDensity B D ω) (5/3)+
          sqrtKinetic (A.fisher.gradient (L.localDensity B D ω))) ∧
        (s ω).interaction ≤ hartree (L.localDensity B D ω).charge := by
  let N := L.localDensity B D
  let k := fun ω => A.oneBody.interiorConstant*(chargeMoment (N ω) (5/3) + sqrtKinetic (A.fisher.gradient (N ω)))
  let w := fun ω => hartree (N ω).charge
  have tf := L.charge_estimate G he h.background_square h.added_tf
  have kin := L.kinetic_estimate A.fisher G he.le h.background_square h.added_mass
  have hk : Integrable k μ := (tf.2.1.add kin.1).const_mul _
  have ic := (m.controls M h.toIslandChargeDomain).2.1
  have hw : Integrable w μ := by
    have hh := integrable_hartree_of_joint (ic.joint (μ := μ) ic
      (fun x => add_nonneg (B.charge_nonneg x) (D.charge_nonneg x)) h.direct)
    apply hh.congr
    refine ae_of_all _ fun ω => congrArg hartree (funext fun x => ?_)
    change m.innerCharge B D ω x = (m.insideMatrix B D ω x).trace.re
    exact (m.trace_inner B D ω x).symm
  have realizable : ∀ᵐ ω ∂μ, ∃ Γ, feasible (N ω).matrix Γ ∧ Γ.kinetic ≤ k ω ∧ Γ.interaction ≤ w ω := by
    filter_upwards [L.field_regular A.fisher G he.le h.added_mass,tf.1] with ω reg hint
    exact A.oneBody.exists_island_state _ _ reg.1 hint
  obtain ⟨s,sm,chosen⟩ := A.selection (fun ω => (N ω).matrix) k w
    (fun i j => m.inner_matrix_integrable B D M i j (h.background_entries i j) (h.added_entries i j)) hk hw realizable
  refine ⟨s,(hk.add hw).mono' sm ?_,chosen⟩
  filter_upwards [chosen] with ω hh
  rw [Real.norm_of_nonneg (add_nonneg (s ω).kinetic_nonneg (s ω).interaction_nonneg)]
  exact add_le_add hh.2.1 hh.2.2

end IslandMasks

/-- The inputs for a single radius describe the scalar masks, the geometry of
one mark, and the universal smeared Graf–Schenker form inequality. They are
independent of both spin densities. -/
structure IslandRadiusData {ε : ℝ} (H : IslandProfiles P (ε/2)) (r C : ℝ) where
  width : ℝ
  denominator : ℝ
  denominator_ge : 1 ≤ denominator
  width_eq : width = r^(-(1/5:ℝ))/denominator
  K : ℝ
  L : ℝ
  L_ge : 1 ≤ L
  masks : H.masks.MeasurableFields
  inside : InteriorMaskData H.masks r K
  hitRate : ℝ
  singleFisher : ℝ
  outside : H.ExteriorDifferential hitRate singleFisher
  geo : IslandOverlapGeometry H ((L*r)^3) (L^3*r^2*width) (L*(ε/2)*width/r) (L*r)
  outer_measurable : Measurable (Function.uncurry (fun z x => H.outer x z))
  first_correction : |H.masks.c₁-1| ≤ L*width/r
  core_correction : |H.masks.c₂| ≤ L/(ε/2)
  gsConstant : ℝ
  gs_nonneg : 0 ≤ gsConstant
  gs_small : gsConstant*width/r ≤ 1/2
  gs_bound : gsConstant ≤ C
  fisher_bound : (1+hitRate)*singleFisher ≤ C*ε
  interior_bound : 16*K^2 ≤ C
  overlap_bound : overlapScale L ≤ C
  diameter_bound : islandCoulombConstant*L^2/2 ≤ C

namespace IslandRadiusData
variable {ε r C : ℝ} {H : IslandProfiles P (ε/2)}

/-- Build both mixed states, antisymmetrize them at fixed marks and average.
The covariance in the output is the energy of the very same densities. -/
theorem trial (J : IslandRadiusData H r C) (A : IslandFockInputs μ)
    {B D : Density} (G : IslandGradients B D ε) (h : IslandDensityDomain B D)
    (he : 0 < ε) (he' : ε ≤ 1) (hr : 1 ≤ r) (hmax : ε*r^2 ≤ 1)
    (hE : exteriorFormConstant A.oneBody ≤ C) (hI : A.oneBody.interiorConstant ≤ C)
    (gs : IslandSmearedGrafSchenker H.outerOverlap r J.width J.gsConstant) :
    ∃ t : IslandTrial μ (B.matrix+D.matrix), Nonempty (ExteriorLocalization t G.background islandFairCoin ε r C) ∧
      Nonempty (IslandInterior t G r C) ∧ t.fluctuation ≤
        12*C*ε*islandBackground B G.background+6*C*(r^2/ε)*(∫ x, D.charge x^2) := by
  let m := H.masks
  let o := H.exteriorMask J.outside
  have hv : 0 < ε/2 := by linarith
  let p := ExteriorOverlap.of_pair_moment hv.le (H.outerOverlap_measurable J.outer_measurable)
    (ae_of_all _ (H.outerOverlap_range hv)) (ae_of_all _ (H.outsidePairMoment hv))
  obtain ⟨Γ,hΓ,hopt⟩ := A.minimizer B G.background G.background_regular h.background_square
  let R := A.restriction Γ B
  have mass := G.background_regular.charge
  have sq := h.background_square.integrable_sq
  obtain ⟨ins,hi,chosen⟩ := m.select_interior A J.inside G J.masks h he
  let out := fun ω => R.state (m.outside ω)
  have ho := (o.kinetic_integrable R hΓ mass).add (o.interaction_integrable R hΓ mass)
  let t := m.fockTrial B D A.tensor A.barycenter J.masks h.toIslandChargeDomain
    h.background_entries h.added_entries out ins ((o.restrict_ae R hΓ mass).mono fun _ q => q.1)
    (chosen.mono fun _ q => q.1) ho hi
  have ht : ∀ ω, t.outside ω = out ω := fun _ => rfl
  have hc := Islands.choose_island_width he he' hr hmax J.denominator_ge
  rw [← J.width_eq] at hc
  have hw : J.width ≤ 1 := by
    rw [J.width_eq]
    exact (div_le_self (Real.rpow_nonneg (zero_le_one.trans hr) _) J.denominator_ge).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num))
  have direct := island_exterior_direct_le (zero_lt_one.trans_le J.L_ge) (zero_lt_one.trans_le hr) J.diameter_bound
    (H.outerOverlap_range hv) (H.outerOverlap_far J.geo.diameter) h.background sq
  refine ⟨t,⟨o.toLocalization p A.oneBody G.background_regular sq hΓ hopt (background_direct h.toIslandChargeDomain)
    R t (ae_of_all _ ht) he.le hr hc.2.2.1.le hw J.gs_nonneg J.gs_bound J.gs_small J.fisher_bound hE gs direct⟩,
    ⟨J.inside.interior A.fisher A.oneBody G t he h.background_square h.added_mass h.added_tf J.interior_bound hI chosen⟩,?_⟩
  have fl := H.fluctuation_scaled G.background J.geo J.L_ge he he' hr hmax rfl J.denominator_ge J.width_eq
    J.first_correction J.core_correction J.masks h.toIslandChargeDomain mass sq h.added_square A.coulomb_pos
  have eqn : t.fluctuation = ∫ ω, hartree (m.centered B D ω) ∂μ := by
    unfold IslandTrial.fluctuation
    apply integral_congr_ae
    apply ae_of_all
    intro ω
    apply congrArg hartree
    funext x
    change m.outerCharge B ω x + m.innerCharge B D ω x - ((B.matrix+D.matrix) x).trace.re = _
    simp [IslandMasks.centered,Density.charge]
  rw [eqn]
  have b₀ : 0 ≤ ε*islandBackground B G.background := mul_nonneg he.le (add_nonneg
    (integral_nonneg fun x => add_nonneg (B.charge_nonneg x) (sq_nonneg _)) (integral_nonneg fun _ => sq_nonneg _))
  have d₀ : 0 ≤ r^2/ε*(∫ x, D.charge x^2) := mul_nonneg (div_nonneg (sq_nonneg _) he.le) (integral_nonneg fun _ => sq_nonneg _)
  linarith only [fl,mul_le_mul_of_nonneg_right J.overlap_bound b₀,mul_le_mul_of_nonneg_right J.overlap_bound d₀]

end IslandRadiusData

/-- A common choice of scalar Poisson geometry and Graf–Schenker theorem at
every admissible radius. It is reused for both density additions. -/
def CoulombIslandRadii (μ : Measure Ω) [IsProbabilityMeasure μ] (ι : Measure Z) [SFinite ι] (ε C : ℝ) :=
  ∀ r : ℝ, 1 ≤ r → ε*r^2 ≤ 1 → ∃ (rate : ℝ) (P : PoissonIslandProcess μ (ENNReal.ofReal rate • ι)) (H : IslandProfiles P (ε/2))
    (J : IslandRadiusData H r C), IslandSmearedGrafSchenker H.outerOverlap r J.width J.gsConstant

/-- Lemma C.1 with the exterior, interior and fluctuations derived on the
same Poisson configuration space. -/
theorem subadditivity_from_poisson {ε r C : ℝ} {B D : Density} (A : IslandFockInputs μ)
    (radii : CoulombIslandRadii μ ι ε C) (G : IslandGradients B D ε) (h : IslandDensityDomain B D)
    (he : 0 < ε) (he' : ε ≤ 1) (hr : 1 ≤ r) (hmax : ε*r^2 ≤ 1)
    (hE : exteriorFormConstant A.oneBody ≤ C) (hI : A.oneBody.interiorConstant ≤ C) :
    energy (B.matrix+D.matrix) ≤ energy B.matrix +
      (12*C+2*C^2)*(3*ε*islandBackground B G.background+sqrtKinetic G.mixed+islandAdded D ε r) := by
  obtain ⟨rate,P,H,J,gs⟩ := radii r hr hmax
  obtain ⟨t,⟨out⟩,⟨ins⟩,fl⟩ := J.trial A G h he he' hr hmax hE hI gs
  exact subadditivity_from_fluctuation_bound G t out ins fl he he' (A.oneBody.interiorConstant_nonneg.trans hI) hmax

/-- Construct the ordered comparison used on each side of the aligned
density in Proposition 4.16. The only density-dependent data are its order,
oscillation, and deterministic form-domain hypotheses. -/
def OrderedSpiralAddition.of_poisson {K : Set Position} {ε η C : ℝ} (A : IslandFockInputs μ)
    (radii : CoulombIslandRadii μ ι ε C) (t : SpiralTaper K) (B D : Density)
    (order : ∀ x ∈ K, B.matrix x ≤ D.matrix x)
    (distance : ∀ x ∈ K, hilbertSchmidt (D.matrix x-B.matrix x) ≤ η)
    (G : IslandGradients (t.field B) (t.residual B D order) ε)
    (h : IslandDensityDomain (t.field B) (t.residual B D order))
    (he : 0 < ε) (he' : ε ≤ 1) (hE : exteriorFormConstant A.oneBody ≤ C) (hI : A.oneBody.interiorConstant ≤ C) :
    OrderedSpiralAddition μ islandFairCoin t B D ε η C where
  order := order
  distance := distance
  gradients := G
  mass := h.added_mass
  trials r hr hmax := by
    obtain ⟨rate,P,H,J,gs⟩ := radii r hr hmax
    obtain ⟨u,out,ins,fl⟩ := J.trial A G h he he' hr hmax hE hI gs
    exact ⟨u,out,ins,.estimate fl⟩

/-- Supply both ordered additions of Proposition 4.16 from one family of
islands. The gauge comparisons refer to the actual tapered spin fields. -/
def CoulombTileReplacement.of_poisson {K : Set Position} {ε η C L : ℝ} (A : IslandFockInputs μ)
    (radii : CoulombIslandRadii μ ι ε C) (M aligned : Density) (φ : Phase) (t : SpiralTaper K)
    (lo hi : SpinMatrix) (hl : lo.PosSemidef) (hh : hi.PosSemidef)
    (ol : ∀ x ∈ K, (constantSpinDensity lo hl).matrix x ≤ aligned.matrix x)
    (ou : ∀ x ∈ K, aligned.matrix x ≤ (constantSpinDensity hi hh).matrix x)
    (dl : ∀ x ∈ K, hilbertSchmidt (aligned.matrix x-(constantSpinDensity lo hl).matrix x) ≤ η)
    (du : ∀ x ∈ K, hilbertSchmidt ((constantSpinDensity hi hh).matrix x-aligned.matrix x) ≤ η)
    (gl : IslandGradients (t.field (constantSpinDensity lo hl)) (t.residual (constantSpinDensity lo hl) aligned ol) ε)
    (gu : IslandGradients (t.field aligned) (t.residual aligned (constantSpinDensity hi hh) ou) ε)
    (hlD : IslandDensityDomain (t.field (constantSpinDensity lo hl)) (t.residual (constantSpinDensity lo hl) aligned ol))
    (huD : IslandDensityDomain (t.field aligned) (t.residual aligned (constantSpinDensity hi hh) ou))
    (gauge : GaugeComparison (t.field aligned) (t.field M) L)
    (phaseGauge : GaugeComparison (t.field M) (t.phaseField M φ) L)
    (he : 0 < ε) (he' : ε ≤ 1) (hE : exteriorFormConstant A.oneBody ≤ C) (hI : A.oneBody.interiorConstant ≤ C) :
    CoulombTileReplacement μ islandFairCoin M φ t lo hi ε η C L :=
  ⟨aligned,hl,hh,.of_poisson A radii t _ _ ol dl gl hlD he he' hE hI,
    .of_poisson A radii t _ _ ou du gu huD he he' hE hI,gauge,phaseGauge⟩

end TSGA.ManyBody
