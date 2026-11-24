import TSGA.IslandTetraTrial
import TSGA.IslandSingleFisher
import TSGA.IslandMaskMeasurability
import TSGA.IslandUnionDerivative
import TSGA.IslandUnionLipschitz
import TSGA.IslandRotation

/-! # From weak cutoff identities and Campbell's formula to Lemma C.1

The placement and differentiation hypotheses below contain no kinetic or
Coulomb error estimates. The three one-mark Fisher intensities are calculated
from the deterministic reference cutoffs before forming any Poisson product.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW Set Metric

universe u w
variable {Ω : Type u} {Z : Type w} [MeasurableSpace Ω] [MeasurableSpace Z]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {P : PoissonIslandProcess μ ι}
variable {v κ : ℝ}

/-- A transported weak derivative in orthogonal coordinates. The norm identity
is pointwise in the observation point and almost everywhere in the rigid mark. -/
structure IslandGradientTransport (T : StationaryIslandPlacements ι κ) (g : Position → Fin 3 → ℝ)
    (region : Position → Set Z) where
  single : Z → Position → Fin 3 → ℝ
  measurable : ∀ i, Measurable (Function.uncurry (fun z x => single z x i))
  norm_eq : ∀ x, ∀ᵐ z ∂ι, maskFisher (single z) x = maskFisher g (T.chart z x)
  off : ∀ᵐ x, ∀ z, z ∉ region x → maskFisher (single z) x = 0

/-- The finite-window weak calculus and the isotropy of its law. Every
differentiation rule is tested on an arbitrary representative of the weak
derivative. The window is the same for all three tests. -/
structure PoissonMaskCalculus (H : IslandProfiles P v) (T : StationaryIslandPlacements ι κ)
    (outer layer core : Position → ℝ) (r : ℝ) where
  region : Position → Set Z
  observation : ∀ x, region x = (fun z => T.chart z x) ⁻¹' closedBall 0 (3*r)
  window_region : ∀ ω x n, n ∈ H.window ω x ↔ P.mark ω n ∈ region x
  campbell : PoissonWindowCampbell P H.window region
  marks : ∀ n, Measurable (fun ω => P.mark ω n)
  leibniz : IslandProfiles.WeakLocalProductRule
  chain : IslandProfiles.WeakScalarRootRules
  exterior : ∀ g : Position → Fin 3 → ℝ,
    (∀ i, WeakPartialOn univ i outer (fun x => g x i)) →
    ∃ U : IslandGradientTransport T g region,
      (∀ z i, WeakPartialOn univ i (fun x => √(1-H.outer x z)) (fun x => U.single z x i)) ∧
      ∀ᵐ x, ∀ i, ∃ M : Ω ≃ᵐ Ω, MeasurePreserving M μ μ ∧
        ∀ᵐ ω ∂μ, ∃ σ : Equiv.Perm ℕ, (H.window ω x).map σ.toEmbedding = H.window (M ω) x ∧
          ∀ n ∈ H.window ω x, H.outer x (P.mark (M ω) (σ n)) = H.outer x (P.mark ω n) ∧
            U.single (P.mark (M ω) (σ n)) x i = -U.single (P.mark ω n) x i
  union_rule : ∀ (f : IslandProfile Z) (a : Position → ℝ), (f = H.layer ∧ a = layer ∨ f = H.inner ∧ a = core) →
    ∀ g : Position → Fin 3 → ℝ, (∀ i, WeakPartialOn univ i a (fun x => g x i)) →
    ∃ U : IslandGradientTransport T g region,
      (∀ z, LocallyLipschitz (fun x => √(f x z))) ∧
      ∀ z i, WeakPartialOn univ i (fun x => √(f x z)) (fun x => U.single z x i)

/-- Turn the derivative identities and three single-profile integrals into
the hypotheses of the tetrahedral construction. -/
theorem PoissonMaskCalculus.differentials {ε r δ : ℝ} {H : IslandProfiles P (ε/2)}
    {T : StationaryIslandPlacements ι κ} {a : IslandShapeConstants} {o l c : Position → ℝ}
    (S : PoissonMaskCalculus H T o l c r)
    (hit : ∀ x, ι.real (S.region x) ≤ a.hit)
    (locality : ∀ᵐ ω ∂μ, ∀ x, ∀ᶠ y in nhds x, ∀ n, n ∉ H.window ω x → H.outer y (P.mark ω n) = 0)
    (om : Measurable (Function.uncurry (fun i x => H.outer x i)))
    (lm : Measurable (Function.uncurry (fun i x => H.layer x i)))
    (cm : Measurable (Function.uncurry (fun i x => H.inner x i)))
    (E : PlacedProfileFisher T o (a.fisher*(ε/2)/(r*δ)))
    (I : PlacedProfileFisher T l (a.fisher*(ε/2)/(r*δ)))
    (J : PlacedProfileFisher T c (a.fisher*(ε/2)*r⁻¹^2)) :
    Nonempty (TetraMaskDifferentials (r := r) (δ := δ) H a) := by
  have masks := H.measurableFields S.marks om lm cm
  have rm : MeasurableSet {p : Z × Position | p.1 ∈ S.region p.2} := by
    have eq : {p : Z × Position | p.1 ∈ S.region p.2} =
        Function.uncurry T.chart ⁻¹' closedBall 0 (3*r) := by
      ext p
      change p.1 ∈ S.region p.2 ↔ T.chart p.1 p.2 ∈ closedBall 0 (3*r)
      simp only [S.observation,mem_preimage]
    rw [eq]
    exact measurableSet_closedBall.preimage T.measurable
  have wm := H.window_measurable S.marks _ rm S.window_region
  obtain ⟨U,wu,rot⟩ := S.exterior E.gradient E.weak
  have e := E.transported U.single U.norm_eq
  let outerDiff : H.ExteriorDifferential a.hit (a.fisher*(ε/2)/(r*δ)) :=
    ⟨U.single,S.region,S.window_region,S.campbell,ae_of_all _ hit,ae_of_all _ (fun x => (e x).1),U.off,
      ae_of_all _ (fun x => (e x).2),masks.outside,
      fun i => H.exteriorGradientMeasurable _ S.marks wm om (U.measurable i),H.weak_outerRootDerivative S.leibniz U.single wu locality,
      H.rotation_of_mark_half_turn U.single rot⟩
  have one (f : IslandProfile Z) (b : Position → ℝ) (F : ℝ)
      (sel : f = H.layer ∧ b = l ∨ f = H.inner ∧ b = c) (p : PlacedProfileFisher T b F)
      (pm : Measurable (Function.uncurry (fun i x => f x i)))
      (hm : Measurable (fun z : Ω × Position => 1-P.uncovered f z.1 z.2)) :
      Nonempty (H.UnionDifferential f F outerDiff.region) := by
    obtain ⟨V,singleLip,weak⟩ := S.union_rule f b sel p.gradient p.weak
    have range : ∀ x z, f x z ∈ Icc 0 1 := by
      rcases sel with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact H.layer_range
      · exact H.inner_range
    have off (x z) (hz : H.outer x z = 0) : f x z = 0 := by
      rcases sel with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact le_antisymm ((H.layer_le_outer x z).trans_eq hz) (H.layer_range x z).1
      · exact le_antisymm (((H.core_le_layer x z).trans (H.layer_le_outer x z)).trans_eq hz) (H.inner_range x z).1
    have nearby := locality.mono fun ω ho x => (ho x).mono fun y hy n hn => off y _ (hy n hn)
    have lip := H.unionRoot_locallyLipschitz f range nearby singleLip
    have ev := p.transported V.single V.norm_eq
    exact ⟨⟨V.single,ae_of_all _ (fun x => (ev x).1),V.off,ae_of_all _ (fun x => (ev x).2),
      hm,fun i => H.coveredGradientMeasurable f _ S.marks wm pm (V.measurable i),lip,
      H.weak_unionRootDerivative S.leibniz S.chain f _ range nearby singleLip weak lip⟩⟩
  exact ⟨⟨outerDiff,(one _ _ _ (.inl ⟨rfl,rfl⟩) I lm masks.first).some,
    (one _ _ _ (.inr ⟨rfl,rfl⟩) J cm masks.core).some⟩⟩

/-- Stochastic input for a fixed reference mollifier and a Haar frame law.
It provides the locally finite marked process, its weak derivative identities
and Graf–Schenker on its deterministic overlap kernel. -/
def TetraPoissonLaws (μ : Measure Ω) [IsProbabilityMeasure μ] (ι : Measure Z) [SFinite ι]
    (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (G : ℝ) : Prop :=
  ∀ {v r δ : ℝ}, (hv : 0 < v) → v ≤ 1/2 → 1 ≤ r → (hd : 0 < δ) → (hw : δ ≤ r/2) → G*δ/r ≤ 1/2 →
    let rate := ENNReal.ofReal (v/(r^3/24))
    ∃ (P : PoissonIslandProcess μ (rate • ι)) (T : StationaryIslandPlacements (rate • ι) (v/(r^3/24)))
      (window : Ω → Position → Finset ℕ) (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖),
      let H := tetraIslandProfiles η hs hv hd hw T window finite_hits
      Nonempty (PoissonMaskCalculus H T (fun x => √(1-smoothedIndicator (tetrahedron r) η δ x))
        (fun x => √(smoothedIndicator (tetrahedron (r-δ)) η δ x)) (fun x => √(islandCore r x)) r) ∧
        IslandSmearedGrafSchenker H.outerOverlap r δ G

/-- A single constant works for all filling fractions and radii. The source
assumptions use individual Sobolev rules, Poisson identities and the smeared
Graf–Schenker inequality. All island energy comparisons are conclusions. -/
theorem TetraPoissonLaws.radii {η : Mollifier} {hs} {G : ℝ} (laws : TetraPoissonLaws μ ι η hs G)
    (hg : 0 ≤ G) (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (A : IslandFockInputs μ) : ∃ C ≥ 0, exteriorFormConstant A.oneBody ≤ C ∧ A.oneBody.interiorConstant ≤ C ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → CoulombIslandRadii μ ι ε C := by
  obtain ⟨F,hF,fields⟩ := islandPlacedFisher sob quant η hs
  have hh : 0 ≤ tetraHitConstant := by unfold tetraHitConstant; positivity
  let a : IslandShapeConstants := ⟨G,tetraHitConstant,F,hg,hh,hF⟩
  obtain ⟨cE,cI,_⟩ := a.costs A
  refine ⟨a.constant A,A.oneBody.interiorConstant_nonneg.trans cI,cE,cI,?_⟩
  intro ε he he'
  apply TetraIslandRealizations.radii (a := a) (η := η) (hs := hs) (he := he) (he' := he') _ A
  intro r hr hm
  obtain ⟨hw,hsw,_⟩ := a.scales he he' hr hm
  obtain ⟨P,T,W,hW,⟨diff⟩,gs⟩ := laws (half_pos he) (by linarith) hr hw hsw (a.scales he he' hr hm).2.2.1
  obtain ⟨⟨e⟩,⟨i⟩,⟨j⟩⟩ := fields (half_pos he) hw hsw T
  have om := (measurable_smoothedTetrahedron η r hw).comp T.measurable
  have lm := (measurable_smoothedTetrahedron η (r-a.width r) hw).comp T.measurable
  have cm : Measurable (islandCore r) := ((islandCoreBump.continuous.comp (continuous_const_smul _)).pow 2).measurable
  have hit (x : Position) : (ENNReal.ofReal (ε/2/(r^3/24)) • ι).real (diff.region x) ≤ a.hit := by
    rw [diff.observation,T.tetra_hit_intensity (half_pos he).le (zero_lt_one.trans_le hr)]
    exact mul_le_of_le_one_right hh (by linarith)
  exact ⟨P,T,W,hW,diff.differentials (a := a) hit
    (ae_of_all _ (tetraIsland_nearby η hs (half_pos he) hw hsw T W hW)) om lm (cm.comp T.measurable) e i j,gs⟩

/-- Both statements of Lemma C.1 for the Coulomb functional from the same
microscopic and scalar inputs. The constant is chosen before either density,
the filling fraction, the island radius or the charge cap. -/
theorem coulomb_island_subadditivity {η : Mollifier} {hs} {G : ℝ} (laws : TetraPoissonLaws μ ι η hs G)
    (hg : 0 ≤ G) (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (A : IslandFockInputs μ) : ∃ C ≥ 0, ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∀ {B D : Density} (g : IslandGradients B D ε), IslandDensityDomain B D →
      (∀ r : ℝ, 1 ≤ r → ε*r^2 ≤ 1 → energy (B.matrix+D.matrix) ≤ energy B.matrix +
        C*(3*ε*islandBackground B g.background+sqrtKinetic g.mixed+islandAdded D ε r)) ∧
      (∀ cap : ℝ, 0 ≤ cap → (∀ᵐ x, D.charge x ≤ cap) → energy (B.matrix+D.matrix) ≤ energy B.matrix +
        C*(3*ε*islandBackground B g.background+sqrtKinetic g.mixed+
          3*(ε+Real.sqrt (cap/ε)+cap/ε)*(∫ x, D.charge x))) := by
  obtain ⟨c,hc,ce,ci,radii⟩ := laws.radii hg sob quant A
  have cp : 0 ≤ 12*c+2*c^2 := by positivity
  refine ⟨12*c+2*c^2,cp,?_⟩
  intro ε he he' B D g h
  have finite (r : ℝ) (hr : 1 ≤ r) (hm : ε*r^2 ≤ 1) :=
    subadditivity_from_poisson A (radii he he') g h he he' hr hm ce ci
  exact ⟨finite,fun _ hcap bound => subadditivity_of_bounded_charge he he' cp hcap bound h.added_mass finite⟩

end TSGA.ManyBody
