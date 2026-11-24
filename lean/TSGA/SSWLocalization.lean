import TSGA.SSWBoundary
import TSGA.TetrahedronLimit
import TSGA.ScaleAverage
import TSGA.DirectionAverage
import TSGA.SSWInterior

/-! # From finite localization estimates to the SSW thermodynamic limit

The inputs below are inequalities between finite energies. They identify the
tiling and boundary estimates used in Steps 1–3 of `thm:spiral_limit`. The gas
energy is constructed from the reference tetrahedron.
-/

noncomputable section

namespace TSGA.SSW

open Filter MeasureTheory
open scoped Topology

abbrev EnergyFunctional := (Position → SpinMatrix) → ℝ

/-- The open reference tetrahedron in the 24-tile cube decomposition. Before
centering, its vertices are the origin, the face center (1/2,0,0), and the two
cube vertices (1/2,1/2,±1/2). Its barycenter is (3/8,1/4,0). -/
def tetrahedron (ℓ : ℝ) : Set Position :=
  {x | |x 2| < x 1 + ℓ / 4 ∧ x 1 + ℓ / 4 < x 0 + 3 * ℓ / 8 ∧ x 0 + 3 * ℓ / 8 < ℓ / 2}

/-- Energy per unit volume of one smeared spiral tetrahedron. -/
def tileEnergy (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix)
    (ℓ δ : ℝ) (q : Position) : ℝ :=
  E (cutoffSpiral (smoothedIndicator (tetrahedron ℓ) η δ) M q) / regionVolume (tetrahedron ℓ)

def averagedTile (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix)
    (q : Position) (ℓ δ : ℝ) : ℝ := directionAverage (tileEnergy E η M ℓ δ) ‖q‖

/-- Reference value constructed before taking any large-domain limit. -/
def sswEnergy (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix) (q : Position) : ℝ :=
  tileLimit (averagedTile E η M q)

/-- The zero-spiral uniform gas, defined using unrotated finite spin fields. -/
def uniformEnergy (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix) : ℝ :=
  tileLimit (fun ℓ δ => E (fun x => ((smoothedIndicator (tetrahedron ℓ) η δ x : ℝ) : ℂ) • M) /
    regionVolume (tetrahedron ℓ))

@[simp] theorem sswEnergy_zero_wavevector (E : EnergyFunctional) (η : Mollifier)
    (M : SpinMatrix) : sswEnergy E η M 0 = uniformEnergy E η M := by
  apply tileLimit_congr
  have hfield (f : Position → ℝ) : cutoffSpiral f M 0 = fun x => (f x : ℂ) • M :=
    funext (cutoffSpiral_zero_wavevector f M)
  exact Eventually.of_forall fun ℓ => by simp [averagedTile, tileEnergy, hfield]

/-- The angular average is invariant under every change of direction. -/
theorem sswEnergy_isotropic (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix)
    {q k : Position} (h : ‖q‖ = ‖k‖) : sswEnergy E η M q = sswEnergy E η M k := by
  apply tileLimit_congr
  exact Eventually.of_forall fun _ => by simp only [averagedTile, h]

@[simp] theorem sswEnergy_vacuum {E : EnergyFunctional} (hE : E 0 = 0)
    (η : Mollifier) (q : Position) : sswEnergy E η 0 q = 0 := by
  have hfield (f : Position → ℝ) (k : Position) : cutoffSpiral f 0 k = 0 :=
    funext (cutoffSpiral_zero_matrix f k)
  have htile (ℓ δ : ℝ) : tileEnergy E η 0 ℓ δ = fun _ => 0 := by
    funext k
    simp [tileEnergy, hfield, hE]
  simp [sswEnergy, tileLimit, averagedTile, htile]

@[simp] theorem uniformEnergy_vacuum {E : EnergyFunctional} (hE : E 0 = 0)
    (η : Mollifier) : uniformEnergy E η 0 = 0 := by
  rw [← sswEnergy_zero_wavevector, sswEnergy_vacuum hE]

/-- A lower localization inequality before the interior directions are counted.
`w ω` is the interior fraction averaged over rotations with wavevector
direction `ω`. The tile energy is constant over these rotations. The parameter
`missing` bounds the lost fraction and `remainder` bounds the other costs. -/
def InteriorLower (f : Position → ℝ) (r missing floor remainder outer : ℝ) : Prop :=
  let μ := (volume : Measure Position).toSphere
  let T := fun ω : Metric.sphere (0 : Position) 1 => f (r • (ω : Position))
  ∃ w : Metric.sphere (0 : Position) 1 → ℝ,
    Integrable T μ ∧ AEStronglyMeasurable w μ ∧ 0 ≤ floor ∧
    (∀ᵐ ω ∂μ, 0 ≤ w ω ∧ 1 - missing ≤ w ω ∧ w ω ≤ 1) ∧
    (∀ᵐ ω ∂μ, -floor ≤ T ω) ∧ (⨍ ω, w ω * T ω ∂μ) - remainder ≤ outer

theorem InteriorLower.estimate {f : Position → ℝ} {r missing floor remainder outer : ℝ}
    (h : InteriorLower f r missing floor remainder outer) :
    directionAverage f r - missing * (directionAverage f r + floor) - remainder ≤ outer := by
  obtain ⟨w, hT, hw, ha, hfrac, hfloor, hloc⟩ := h
  let : NeZero (volume : Measure Position).toSphere := ⟨Measure.toSphere_ne_zero volume⟩
  exact (sub_le_sub_right (interior_average_bounds hT hw ha hfrac hfloor).1 _).trans hloc

/-- Square-root cutoff gradient and the finite Cauchy–Schwarz estimate for
a compactly supported mollifier. Its cost per unit volume is proved to vanish
from the two smoothing-scale hypotheses and boundary regularity. -/
structure CutoffGradient (D : DomainSequence) where
  grad : ℕ → Position → Position
  weak : ∀ n i, WeakPartialOn Set.univ i (fun x => Real.sqrt (D.cutoff n x)) (fun x => grad n x i)
  measurable : ∀ n, AEStronglyMeasurable (grad n) volume
  boundary_bound : ∃ b B : ℝ, 0 < b ∧ 0 ≤ B ∧ ∀ n, ∀ᵐ x ∂volume, ‖grad n x‖ ^ 2 ≤
    (Metric.thickening (b * D.delta n) (frontier (D.region n))).indicator
      (fun _ => B / D.delta n ^ 2) x

def CutoffGradient.cost {D : DomainSequence} (G : CutoffGradient D) (n : ℕ) : ℝ :=
  (∫ x, ‖G.grad n x‖ ^ 2) / D.vol n

theorem CutoffGradient.cost_tendsto_zero {D : DomainSequence} (G : CutoffGradient D) :
    Tendsto G.cost atTop (𝓝 0) := by
  obtain ⟨b, B, hb, hB, h⟩ := G.boundary_bound
  exact D.cutoffKinetic_tendsto_zero G.grad b B hb hB G.measurable h

/-- Tiling a larger tetrahedron by a fixed inner scale. -/
def TetrahedronTwoScale (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix) (q : Position) : Prop :=
  ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → ∃ c k d m : ℝ, 0 ≤ c ∧
    ∀ᶠ ℓ in atTop, ∀ᶠ L in atTop,
      InteriorLower (tileEnergy E η M ℓ δ) ‖q‖ (c * (δ / ℓ + (ℓ + δ + δ') / L)) k
        (d * ((ℓ + δ + δ') / L) + m / ℓ) (averagedTile E η M q L δ')

/-- Measurability of the finite tetrahedron energy under joint dilation. -/
def TetrahedronDilationMeasurable (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix) (q : Position) : Prop :=
  ∀ ℓ : ℝ, 3 ≤ ℓ → AEStronglyMeasurable
    (fun t => averagedTile E η M q (t * (ℓ - 1)) t) (volume.restrict scaleInterval)

/-- Lower tiling comparison on regular domains. -/
def DomainLowerTiling (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix) (q : Position) : Prop :=
  ∀ D : DomainSequence, ∃ a : ℝ, 0 < a ∧ ∃ c k d m : ℝ, ∀ᶠ n in atTop,
    InteriorLower (tileEnergy E η M (D.tileLength n) 1) ‖q‖
      (c * ((D.tileLength n)⁻¹ + D.tileBoundaryFraction a n)) k
      (d * D.tileBoundaryFraction a n + m / D.tileLength n) (D.energyDensity E M n q)

/-- Upper tiling comparison on regular domains, including the cutoff kinetic cost. -/
def DomainUpperTiling (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix) (q : Position) : Prop :=
  ∀ D : DomainSequence, ∃ G : CutoffGradient D, ∃ a : ℝ, 0 < a ∧ ∃ A B C : ℝ, ∀ᶠ n in atTop,
    D.energyDensity E M n q ≤
      scaleAverage (fun t => averagedTile E η M q (t * (D.tileLength n - 1)) t) +
      (A * ((D.tileLength n)⁻¹ + D.tileBoundaryFraction a n) +
        B * ((D.tileLength n)⁻¹ + G.cost n) + C / D.tileLength n)

/-- Finite-volume estimates at a fixed spin matrix and wavevector. The first
comparison is `eq:two_scales_spiral` after angular averaging. The last two
fields are the lower tiling bound and the dilation-averaged upper tiling bound
for a regular domain, with inner smoothing width one and ℓ = |Ω|^(1/6).
The layer fractions are actual volumes of neighborhoods of the boundary.
All coefficients are independent of N. -/
structure FiniteLocalization (E : EnergyFunctional) (η : Mollifier) (M : SpinMatrix)
    (q : Position) : Prop where
  bounds : TileBounds (averagedTile E η M q)
  twoScale : TetrahedronTwoScale E η M q
  measurable : TetrahedronDilationMeasurable E η M q
  lower : DomainLowerTiling E η M q
  upper : DomainUpperTiling E η M q

variable {E : EnergyFunctional} {η : Mollifier} {M : SpinMatrix} {q : Position}

/-- Step 1. Every fixed smoothing width yields the same reference limit. -/
theorem FiniteLocalization.tile_tendsto (H : FiniteLocalization E η M q) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ℓ => averagedTile E η M q ℓ δ) atTop (𝓝 (sswEnergy E η M q)) := by
  apply TileComparison.tendsto _ hδ
  apply TileComparison.of_two_scales H.bounds.eventually_bounded
  intro δ δ' hδ hδ'
  obtain ⟨c, k, d, m, hc, h⟩ := H.twoScale δ δ' hδ hδ'
  refine ⟨c, k, d, m, hc, ?_⟩
  filter_upwards [h] with ℓ hℓ
  filter_upwards [hℓ] with L hL
  simpa only [averagedTile, sub_sub, add_assoc] using hL.estimate

/-- Steps 2 and 3. Both finite-volume comparisons tend to the same value,
including when the outer smoothing width varies along the sequence. -/
theorem FiniteLocalization.tendsto (H : FiniteLocalization E η M q) (D : DomainSequence) :
    Tendsto (fun n => D.energyDensity E M n q) atTop (𝓝 (sswEnergy E η M q)) := by
  have htile := (H.tile_tendsto zero_lt_one).comp D.tileLength_tendsto
  have hsmall := D.tileLength_tendsto.inv_tendsto_atTop
  obtain ⟨a, ha, c, k, d, m, hlower⟩ := H.lower D
  obtain ⟨G, b, hb, A, B, C, hupper⟩ := H.upper D
  have hmean := scaleAverage_tendsto D.tileLength_tendsto (fun _ => H.tile_tendsto)
    ((D.tileLength_tendsto.eventually_ge_atTop 3).mono fun n hn => H.measurable _ hn)
    H.bounds.uniform_bound
  have hlo := hlower.mono fun _ hn => hn.estimate
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _ hlo hupper
  · have hlayer := D.tileBoundaryLayer_tendsto_zero a ha
    have hboundary := (hsmall.add hlayer).const_mul c
    have h := (htile.sub (hboundary.mul (htile.add_const k))).sub
      ((hlayer.const_mul d).add (D.tileLength_tendsto.const_div_atTop m))
    simpa only [Function.comp_apply, Pi.inv_apply, averagedTile, add_zero, mul_zero, zero_mul, sub_zero] using h
  · have hboundary := (hsmall.add (D.tileBoundaryLayer_tendsto_zero b hb)).const_mul A
    have hcut := (hsmall.add G.cost_tendsto_zero).const_mul B
    have h := hmean.add ((hboundary.add hcut).add (D.tileLength_tendsto.const_div_atTop C))
    simpa only [Pi.inv_apply, add_zero, mul_zero] using h

/-- The reference kernel is auxiliary as well. Two constructions for the same
physical energy agree by uniqueness of the limit along any admissible domain. -/
theorem sswEnergy_kernel_independent {η' : Mollifier}
    (H : FiniteLocalization E η M q) (H' : FiniteLocalization E η' M q)
    (D : DomainSequence) : sswEnergy E η M q = sswEnergy E η' M q :=
  tendsto_nhds_unique (H.tendsto D) (H'.tendsto D)

end TSGA.SSW
