import TSGA.IslandTrialAssembly
import TSGA.IslandInteriorGeometry
import TSGA.IslandTetraGeometry

/-! # Radius-uniform constants for the tetrahedral Poisson trial -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Islands Set Metric
open scoped NNReal

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Measure Z} [SFinite ι] {P : PoissonIslandProcess μ ι}

/-- Constants fixed by the reference tetrahedron, its smooth profiles, and
the Graf–Schenker inequality. The single-mark Fisher coefficient multiplies
v/(rδ) at the two faces and v/r² in the core. -/
structure IslandShapeConstants where
  gs : ℝ
  hit : ℝ
  fisher : ℝ
  gs_nonneg : 0 ≤ gs
  hit_nonneg : 0 ≤ hit
  fisher_nonneg : 0 ≤ fisher

namespace IslandShapeConstants
variable (a : IslandShapeConstants)
def denominator := 2+2*a.gs
def width (r : ℝ) := r^(-(1/5:ℝ))/a.denominator
def K := max (max 13 (4/islandCoreFraction)) ((1+a.hit)*a.fisher*(1+a.denominator))
def L := max 24 a.K
def constant (A : IslandFockInputs μ) := max (max (exteriorFormConstant A.oneBody) A.oneBody.interiorConstant)
  (max (max a.gs (16*a.K^2)) (max (overlapScale a.L) (islandCoulombConstant*a.L^2/2)))

theorem den_ge : 2 ≤ a.denominator := by unfold denominator; linarith [a.gs_nonneg]
theorem K_ge : 13 ≤ a.K := (le_max_left _ _).trans (le_max_left _ _)
theorem core_size : 4 ≤ a.K*islandCoreFraction := (div_le_iff₀ islandCoreFraction_pos).mp
  ((le_max_right _ _).trans (le_max_left _ _))
theorem L_ge : 24 ≤ a.L := le_max_left _ _
theorem L_K : a.K ≤ a.L := le_max_right _ _
theorem costs (A : IslandFockInputs μ) :
    exteriorFormConstant A.oneBody ≤ a.constant A ∧ A.oneBody.interiorConstant ≤ a.constant A ∧
    a.gs ≤ a.constant A ∧ 16*a.K^2 ≤ a.constant A ∧ overlapScale a.L ≤ a.constant A ∧
    islandCoulombConstant*a.L^2/2 ≤ a.constant A := by
  unfold constant
  exact ⟨(le_max_left _ _).trans (le_max_left _ _),(le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

theorem scales {ε r : ℝ} (he : 0 < ε) (he' : ε ≤ 1) (hr : 1 ≤ r) (hm : ε*r^2 ≤ 1) :
    0 < a.width r ∧ a.width r ≤ r/2 ∧ a.gs*a.width r/r ≤ 1/2 ∧
    (1+a.hit)*(a.fisher*(ε/2)/(r*a.width r)) ≤ a.K*ε ∧
    (1+a.hit)*(a.fisher*(ε/2)*r⁻¹^2) ≤ a.K*ε*r⁻¹^2 := by
  have den := a.den_ge
  have hr' := zero_lt_one.trans_le hr
  obtain ⟨_,_,w,sh,bound,_⟩ := choose_island_width he he' hr hm (by linarith : 1 ≤ a.denominator)
  change 0 < a.width r at w
  change a.width r ≤ r/a.denominator at sh
  change 1/r*(1+(a.width r)⁻¹) ≤ 1+a.denominator at bound
  have hw := sh.trans (div_le_div_of_nonneg_left hr'.le (by norm_num) den)
  have collar : a.gs*a.width r/r ≤ 1/2 := by
    rw [div_le_iff₀ hr']
    have sh' := (le_div_iff₀ (by linarith : 0<a.denominator)).mp sh
    have gd : 2*a.gs ≤ a.denominator := by unfold denominator; linarith
    nlinarith only [sh',mul_le_mul_of_nonneg_left gd w.le]
  have ub : 1/(r*a.width r) ≤ 1+a.denominator := by
    rw [one_div,mul_inv_rev,mul_comm (a.width r)⁻¹]
    rw [one_div,mul_add,mul_one] at bound
    linarith only [bound,inv_nonneg.mpr hr'.le]
  let b := (1+a.hit)*a.fisher
  have b₀ : 0 ≤ b := mul_nonneg (by linarith [a.hit_nonneg]) a.fisher_nonneg
  have bk : b*(1+a.denominator) ≤ a.K := le_max_right _ _
  have bk' : b ≤ a.K := (le_mul_of_one_le_right b₀ (by linarith : 1 ≤ 1+a.denominator)).trans bk
  refine ⟨w,hw,collar,?_,?_⟩
  · calc
      _ = (b*(1/(r*a.width r)))*(ε/2) := by dsimp [b]; ring
      _ ≤ a.K*(ε/2) := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left ub b₀).trans bk) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by linarith [a.K_ge])
  · have h := mul_le_mul_of_nonneg_right (mul_le_mul bk' (by linarith : ε/2 ≤ ε) (by linarith) (by linarith [a.K_ge])) (sq_nonneg r⁻¹)
    dsimp [b] at h
    linarith only [h]

end IslandShapeConstants

/-- Differential identities of the finite products for a given marked
process. The three Fisher inputs test *one* mark against intensity. -/
structure TetraMaskDifferentials {ε r δ : ℝ} (H : IslandProfiles P (ε/2)) (a : IslandShapeConstants) where
  outside : H.ExteriorDifferential a.hit (a.fisher*(ε/2)/(r*δ))
  first : H.UnionDifferential H.layer (a.fisher*(ε/2)/(r*δ)) outside.region
  core : H.UnionDifferential H.inner (a.fisher*(ε/2)*r⁻¹^2) outside.region

/-- Turn the deterministic tetrahedral cutoffs, their transported derivatives
and the Poisson window formula into the scale data of the Fock trial. -/
def tetraIslandRadiusData (a : IslandShapeConstants) (A : IslandFockInputs μ)
    (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {ε r : ℝ} (he : 0 < ε) (he' : ε ≤ 1) (hr : 1 ≤ r) (hm : ε*r^2 ≤ 1)
    (T : StationaryIslandPlacements ι ((ε/2)/(r^3/24))) (window : Ω → Position → Finset ℕ)
    (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖)
    (diff : TetraMaskDifferentials (r := r) (δ := a.width r)
      (tetraIslandProfiles η hs (half_pos he) (a.scales he he' hr hm).1 (a.scales he he' hr hm).2.1 T window finite_hits) a) :
    IslandRadiusData (tetraIslandProfiles η hs (half_pos he) (a.scales he he' hr hm).1 (a.scales he he' hr hm).2.1 T window finite_hits)
      r (a.constant A) := by
  have scale := a.scales he he' hr hm
  have w := scale.1
  have sw := scale.2.1
  have col := scale.2.2.1
  have fb := scale.2.2.2.1
  have fc := scale.2.2.2.2
  let H := tetraIslandProfiles η hs (half_pos he) w sw T window finite_hits
  have hr' := zero_lt_one.trans_le hr
  have hs₀ := div_nonneg w.le hr'.le
  have hs₁ : a.width r/r ≤ 1/2 := (div_le_iff₀ hr').mpr (by linarith)
  have m₁ : H.layerIntensity = (ε/2)*(1-a.width r/r)^3 := rfl
  have m₂ : H.innerIntensity = islandCoreFraction*(ε/2) := rfl
  have θ := tetraIslandCoreFraction_le_one η hs (half_pos he) w sw T window finite_hits
  let L := H.interiorMasks he he' hs₀ hs₁ θ m₁ m₂ a.K_ge a.core_size diff.outside.region
    diff.outside.campbell diff.outside.hit_bound diff.first diff.core fb fc
  have corr := first_correction (half_pos he) hs₀ hs₁
  change 1 ≤ H.masks.c₁ ∧ H.masks.c₁ ≤ 1+24*(a.width r/r) at corr
  have costs := a.costs A
  have g := costs.2.2.1
  have c := costs.2.2.2.1
  have k := costs.2.2.2.2.1
  have d := costs.2.2.2.2.2
  have kg := a.K_ge
  have KL : a.K ≤ 16*a.K^2 := by nlinarith [sq_nonneg (a.K-1)]
  refine {
    width := a.width r
    denominator := a.denominator
    denominator_ge := (by norm_num : (1:ℝ) ≤ 2).trans a.den_ge
    width_eq := rfl
    K := a.K
    L := a.L
    L_ge := (by norm_num : (1:ℝ) ≤ 24).trans a.L_ge
    masks := ⟨diff.outside.measurable,diff.first.measurable,diff.core.measurable⟩
    inside := L
    hitRate := a.hit
    singleFisher := a.fisher*(ε/2)/(r*a.width r)
    outside := diff.outside
    geo := tetraIslandOverlapGeometry η hs (half_pos he) w sw T window finite_hits a.L_ge
    outer_measurable := (measurable_smoothedTetrahedron η r w).comp T.measurable
    first_correction := ?_
    core_correction := ?_
    gsConstant := a.gs
    gs_nonneg := a.gs_nonneg
    gs_small := col
    gs_bound := g
    fisher_bound := fb.trans (mul_le_mul_of_nonneg_right (KL.trans c) he.le)
    interior_bound := c
    overlap_bound := k
    diameter_bound := d }
  · rw [abs_of_nonneg (sub_nonneg.mpr corr.1),mul_div_assoc]
    linarith only [corr.2,mul_le_mul_of_nonneg_right a.L_ge hs₀]
  · rw [abs_of_pos (InteriorMaskData.c₂_pos (m := H.masks)),le_div_iff₀ (half_pos he)]
    have e := L.upper₂
    linarith only [e,a.L_K,mul_nonneg he.le (InteriorMaskData.c₂_pos (m := H.masks)).le]

/-- Realizations of the stationary marked Poisson process at the chosen
width. Only scalar cutoff calculus and the usual smeared Graf–Schenker
inequality are needed after the process has been placed. -/
def TetraIslandRealizations (μ : Measure Ω) [IsProbabilityMeasure μ] (ι : Measure Z) [SFinite ι]
    (a : IslandShapeConstants) (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (ε : ℝ) (he : 0 < ε) (he' : ε ≤ 1) : Prop :=
  ∀ (r : ℝ) (hr : 1 ≤ r) (hm : ε*r^2 ≤ 1),
    let v := ε/2
    let δ := a.width r
    let rate := ENNReal.ofReal (v/(r^3/24))
    ∃ (P : PoissonIslandProcess μ (rate • ι)) (T : StationaryIslandPlacements (rate • ι) (v/(r^3/24)))
      (window : Ω → Position → Finset ℕ) (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖),
      let H := tetraIslandProfiles η hs (half_pos he) (a.scales he he' hr hm).1 (a.scales he he' hr hm).2.1 T window finite_hits
      Nonempty (TetraMaskDifferentials (r := r) (δ := δ) H a) ∧ IslandSmearedGrafSchenker H.outerOverlap r δ a.gs

theorem TetraIslandRealizations.radii {a : IslandShapeConstants} {η : Mollifier} {hs} {ε : ℝ} {he he'}
    (h : TetraIslandRealizations μ ι a η hs ε he he') (A : IslandFockInputs μ) :
    CoulombIslandRadii μ ι ε (a.constant A) := by
  intro r hr hm
  obtain ⟨P,T,window,fh,⟨d⟩,gs⟩ := h r hr hm
  refine ⟨ε/2/(r^3/24),?_⟩
  let J := tetraIslandRadiusData (P := P) a A η hs he he' hr hm T window fh d
  exact ⟨P,_,J,gs⟩

/-- The tetrahedral construction gives Lemma C.1 with a constant independent
of both spin densities, the radius and the filling fraction. -/
theorem subadditivity_tetra_islands {a : IslandShapeConstants} {η : Mollifier} {hs} {ε r : ℝ} {he he'}
    (p : TetraIslandRealizations μ ι a η hs ε he he') (A : IslandFockInputs μ)
    {B D : Density} (G : IslandGradients B D ε) (h : IslandDensityDomain B D) (hr : 1 ≤ r) (hm : ε*r^2 ≤ 1) :
    let C := a.constant A
    energy (B.matrix+D.matrix) ≤ energy B.matrix +
      (12*C+2*C^2)*(3*ε*islandBackground B G.background+sqrtKinetic G.mixed+islandAdded D ε r) :=
  subadditivity_from_poisson A (p.radii A) G h he he' hr hm (a.costs A).1 (a.costs A).2.1

/-- The bounded-charge form chooses the radius after fixing the essential
upper bound of the added charge, using the same universal constant. -/
theorem subadditivity_bounded_tetra_islands {a : IslandShapeConstants} {η : Mollifier} {hs} {ε cap : ℝ} {he he'}
    (p : TetraIslandRealizations μ ι a η hs ε he he') (A : IslandFockInputs μ)
    {B D : Density} (G : IslandGradients B D ε) (h : IslandDensityDomain B D)
    (hc : 0 ≤ cap) (hcap : ∀ᵐ x, D.charge x ≤ cap) :
    let C := a.constant A
    energy (B.matrix+D.matrix) ≤ energy B.matrix + (12*C+2*C^2)*
      (3*ε*islandBackground B G.background+sqrtKinetic G.mixed+
        3*(ε+Real.sqrt (cap/ε)+cap/ε)*(∫ x, D.charge x)) := by
  have hC := A.oneBody.interiorConstant_nonneg.trans (a.costs A).2.1
  apply subadditivity_of_bounded_charge he he' (by positivity) hc hcap h.added_mass
  intro r hr hm
  exact subadditivity_tetra_islands p A G h hr hm

end TSGA.ManyBody
