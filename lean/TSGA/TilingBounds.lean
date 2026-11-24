import TSGA.BulkLocalization
import TSGA.CutoffOverhead
import TSGA.DilationEndpoint

/-! # Geometric and energetic costs of translating the tetrahedral tiling

The parameter law averages the 24 labels, orientations, and dilations. Each
label therefore carries weight 24 divided by the volume of the dilated cell.
The smoothing width is one and the cell size is ε⁻¹.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory

inductive CutoffSide where
  | upper
  | lower

def CutoffSide.mass : CutoffSide → ℝ → ℝ
  | .upper, ε => (1 - ε) ^ 3
  | .lower, _ => 1

theorem CutoffSide.deficit (side : CutoffSide) {ε : ℝ} (hε : 0 ≤ ε) (hle : ε ≤ 1) :
    1 - side.mass ε ≤ 3 * ε := by
  cases side with
  | lower => simp [mass, hε]
  | upper =>
    dsimp [mass]
    nlinarith only [mul_nonneg (sq_nonneg ε) (by linarith : 0 ≤ 3 - ε)]

/-- A face layer has volume at most A L² w. A pointwise squared-gradient
bound B/w² supported in that layer gives the individual tile bound used
in the orientation and dilation averages. -/
theorem face_gradient_cost_of_support {G : Position → Position} {face : Set Position}
    {L w A B : ℝ} (hw : 0 < w) (hB : 0 ≤ B) (hface : MeasurableSet face)
    (hfinite : volume face ≠ ⊤) (harea : volume.real face ≤ A * L^2 * w)
    (hgrad : ∀ᵐ x, ‖G x‖ ^ 2 ≤ face.indicator (fun _ => B/w^2) x) :
    (∫ x, ‖G x‖ ^ 2) ≤ (A*B) * L^2 / w := by
  have hi : Integrable (face.indicator (fun _ => B/w^2)) :=
    (integrable_indicator_iff hface).2 (integrableOn_const hfinite)
  calc
    _ ≤ ∫ x, face.indicator (fun _ => B/w^2) x :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg ‖G x‖) hi hgrad
    _ = volume.real face * (B/w^2) := by rw [integral_indicator hface, setIntegral_const, smul_eq_mul]
    _ ≤ A * L^2 * w * (B/w^2) := mul_le_mul_of_nonneg_right harea (div_nonneg hB (sq_nonneg w))
    _ = _ := by field_simp [hw.ne']

/-- Finite geometric data for one tiling. The per-label mass is the volume
of its (possibly shrunken) tetrahedron. The square-root gradient scales
with the face area divided by the smoothing width. -/
structure TetrahedralCutoffs (T : AveragedTiles) (side : CutoffSide) (ε k : ℝ) where
  dilation : T.Parameter → ℝ
  dilation_measurable : let := T.space; Measurable dilation
  gradient : T.Parameter → Position → Position
  scale : ∀ i, dilation i ∈ SSW.scaleInterval
  weight : ∀ i, T.weight i = 24 / (dilation i * ε⁻¹) ^ 3
  shape_mass : ∀ i, (∫ z, T.shape i z) = side.mass ε * (dilation i * ε⁻¹) ^ 3 / 24
  weak_gradient : ∀ i j, WeakPartialOn Set.univ j (fun x => Real.sqrt (T.shape i x))
    (fun x => gradient i x j)
  area : ∀ i, (∫ z, ‖gradient i z‖ ^ 2) ≤ k * (dilation i * ε⁻¹) ^ 2 / dilation i
  shape_product : let := T.space
    Integrable (fun p : Position × T.Parameter => T.weight p.2 * T.shape p.2 p.1) (volume.prod T.measure)
  gradient_product : let := T.space
    Integrable (fun p : Position × T.Parameter => T.weight p.2 * ‖gradient p.2 p.1‖ ^ 2)
      (volume.prod T.measure)

def TetrahedralCutoffs.kineticProfile {T : AveragedTiles} {side : CutoffSide} {ε k : ℝ}
    (H : TetrahedralCutoffs T side ε k) (x : Position) : ℝ := by
  letI := T.space
  exact ∫ i, T.weight i * ‖H.gradient i x‖ ^ 2 ∂T.measure

theorem TetrahedralCutoffs.cutoff_mass {T : AveragedTiles} {side : CutoffSide} {ε k : ℝ}
    (H : TetrahedralCutoffs T side ε k) (hε : 0 < ε) :
    (∫ z, T.cutoffProfile z) = side.mass ε := by
  let := T.space
  let := T.probability
  change (∫ z, ∫ i, T.weight i * T.shape i z ∂T.measure) = _
  rw [integral_integral_swap H.shape_product]
  suffices h : (∫ i, ∫ z, T.weight i * T.shape i z ∂volume ∂T.measure) =
      ∫ _ : T.Parameter, side.mass ε ∂T.measure by simpa using h
  apply integral_congr_ae
  filter_upwards with i
  have ht : (1 / 2 : ℝ) ≤ H.dilation i := (H.scale i).1
  rw [integral_const_mul, H.weight, H.shape_mass]
  field_simp [hε.ne', (by linarith : H.dilation i ≠ 0)]

theorem TetrahedralCutoffs.kinetic_mass {T : AveragedTiles} {side : CutoffSide} {ε k : ℝ}
    (H : TetrahedralCutoffs T side ε k) (hε : 0 < ε) (hk : 0 ≤ k) :
    (∫ z, H.kineticProfile z) ≤ (96 * k) * ε := by
  let := T.space
  let := T.probability
  change (∫ z, ∫ i, T.weight i * ‖H.gradient i z‖ ^ 2 ∂T.measure) ≤ _
  rw [integral_integral_swap H.gradient_product]
  have h := integral_mono_ae H.gradient_product.integral_prod_right (integrable_const ((96 * k) * ε)) (by
    filter_upwards with i
    change (∫ z, T.weight i * ‖H.gradient i z‖ ^ 2) ≤ (96 * k) * ε
    rw [integral_const_mul]
    have ht : (1 / 2 : ℝ) ≤ H.dilation i := (H.scale i).1
    have hp : 0 < H.dilation i := by linarith
    have hsize : 1 ≤ 4 * (H.dilation i)^2 := by
      nlinarith only [mul_nonneg (by linarith : 0 ≤ 2 * H.dilation i - 1)
        (by linarith : 0 ≤ 2 * H.dilation i + 1)]
    calc
      _ ≤ T.weight i * (k * (H.dilation i * ε⁻¹) ^ 2 / H.dilation i) :=
        mul_le_mul_of_nonneg_left (H.area i) (T.weight_nonneg i)
      _ = 24 * k * ε / (H.dilation i)^2 := by
        rw [H.weight]
        field_simp [hp.ne', hε.ne']
      _ ≤ _ := by
        apply (div_le_iff₀ (sq_pos_of_pos hp)).2
        nlinarith only [mul_nonneg (mul_nonneg hk hε.le) (sub_nonneg.mpr hsize)])
  simpa using h

/-- Density used to put exterior errors back under the spatial integral. -/
def tilingExterior (D : Density) (φ : Phase) (S : MatrixGradient) (ε B : ℝ) (x : Position) : ℝ :=
  B * ε * (massDensity D φ x + kineticDensity S x)

theorem integral_tilingExterior {D : Density} {φ : Phase} {S : MatrixGradient} (ε B : ℝ)
    (hm : Integrable (massDensity D φ)) (hs : Integrable (kineticDensity S)) :
    (∫ x, tilingExterior D φ S ε B x) = B * ε * ((∫ x, massDensity D φ x) + ∫ x, kineticDensity S x) := by
  simp only [tilingExterior, integral_const_mul, integral_add hm hs]

/-- The exterior error carries ε times the kinetic density; the direct
per-volume comparison carries ε⁻¹. These two coefficients are compatible
for ε ≤ 1. -/
theorem TetrahedralCutoffs.toControl {T : AveragedTiles} {side : CutoffSide} {ε k : ℝ}
    (H : TetrahedralCutoffs T side ε k) (P : TileProfile) (D : Density) (φ : Phase) (S : MatrixGradient)
    {A B V W : ℝ} (hε : 0 < ε) (hle : ε ≤ 1) (hk : 0 ≤ k) (hA : 3 ≤ A)
    (hW : 0 ≤ W) (hkA : W * (96*k) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) (hVA : V ≤ A)
    (hcut : P.cutoff = T.cutoffProfile) (hkin : P.kineticKernel = fun x => W * H.kineticProfile x)
    (hc : P.charge = D.charge) (hext : P.exterior = tilingExterior D φ S ε B)
    (hvol : P.volumeCost = fun x => V * (ε * massDensity D φ x + kineticDensity S x / ε)) :
    CutoffControl P D φ S ε A where
  charge_eq := hc
  missing_mass := by
    rw [hcut, H.cutoff_mass hε]
    exact (side.deficit hε.le hle).trans (mul_le_mul_of_nonneg_right hA hε.le)
  kinetic_mass := by
    rw [hkin, integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (H.kinetic_mass hε hk) hW).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hkA hε.le)
  exterior := by
    rw [hext]
    filter_upwards with x
    have hm := massDensity_nonneg D φ x
    have hs : 0 ≤ kineticDensity S x := sq_nonneg _
    have hεk : ε * kineticDensity S x ≤ kineticDensity S x / ε := by
      apply (le_div_iff₀ hε).2
      nlinarith only [mul_nonneg hs (mul_nonneg (sub_nonneg.mpr hle) (by linarith : 0 ≤ 1 + ε))]
    calc
      _ = B * (ε * massDensity D φ x + ε * kineticDensity S x) := by dsimp [tilingExterior]; ring
      _ ≤ B * (ε * massDensity D φ x + kineticDensity S x / ε) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hεk _) hB
      _ ≤ _ := mul_le_mul_of_nonneg_right hBA (add_nonneg (mul_nonneg hε.le hm) (div_nonneg hs hε.le))
  volumeCost := by
    rw [hvol]
    exact ae_of_all _ fun x => mul_le_mul_of_nonneg_right hVA
      (add_nonneg (mul_nonneg hε.le (massDensity_nonneg D φ x)) (div_nonneg (sq_nonneg _) hε.le))

/-- Spatially translated skeleton energy averaged with the parameter law
(including the normalized cell translation). -/
def skeletonEnergy (T : AveragedTiles) (shape : T.Parameter → Position → ℝ) (F : GasEnergies)
    (D : Density) (φ : Phase) : ℝ := by
  letI := T.space
  exact ∫ i, F.energy (fun x => (shape i x : ℂ) • rotate (φ.value x) (D.matrix x)) ∂T.measure

def SkeletonEnergyIntegrable (T : AveragedTiles) (shape : T.Parameter → Position → ℝ)
    (F : GasEnergies) (D : Density) (φ : Phase) : Prop := by
  letI := T.space
  exact Integrable (fun i => F.energy (fun x => (shape i x : ℂ) • rotate (φ.value x) (D.matrix x))) T.measure

private theorem relevant_moments {D : Density} {φ : Phase} (hm : Integrable (massDensity D φ)) :
    (∫ x, D.charge x) ≤ (∫ x, massDensity D φ x) ∧
    (∫ x, D.charge x ^ 2) ≤ (∫ x, massDensity D φ x) ∧
    (∫ x, D.charge x ^ (5/3 : ℝ)) ≤ (∫ x, massDensity D φ x) ∧
    (∫ x, D.charge x * ‖φ.grad x‖^2) ≤ ∫ x, massDensity D φ x := by
  have hh (x : Position) := D.charge_nonneg x
  have hv (x : Position) := mul_nonneg (hh x) (sq_nonneg ‖φ.grad x‖)
  have hh53 (x : Position) : D.charge x ^ (5/3 : ℝ) ≤ D.charge x + D.charge x ^ 2 := by
    rcases (hh x).eq_or_lt with hz | hp
    · simp [← hz, Real.zero_rpow (by norm_num : (5/3 : ℝ) ≠ 0)]
    · exact BulkRegime.density_power_le hp (by constructor <;> norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply integral_mono_of_nonneg (ae_of_all _ hh) hm
    exact ae_of_all _ fun x => by dsimp [massDensity]; linarith only [sq_nonneg (D.charge x), hv x]
  · apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg (D.charge x)) hm
    exact ae_of_all _ fun x => by dsimp [massDensity]; linarith only [hh x, hv x]
  · apply integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg (hh x) _) hm
    exact ae_of_all _ fun x => (hh53 x).trans (le_add_of_nonneg_right (hv x))
  · apply integral_mono_of_nonneg (ae_of_all _ hv) hm
    exact ae_of_all _ fun x => le_add_of_nonneg_left (add_nonneg (hh x) (sq_nonneg _))

/-- Upper tiling estimate with a separate skeleton term, charge-square error
and the kinetic energy of the rotated square root. The last inequality is
the weak square-root product estimate for the axial rotation. -/
theorem upper_tiling_localization {F : GasEnergies} {D : Density} {φ : Phase} {S Z : MatrixGradient}
    (T J : AveragedTiles) (shape : J.Parameter → Position → ℝ) {ε K : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hm : Integrable (massDensity D φ)) (hs : Integrable (kineticDensity S))
    (tiling : rotatedEnergy F D φ ≤ (∫ c, T.energy F D φ c) + skeletonEnergy J shape F D φ +
      K * ε * (∫ x, D.charge x ^ 2))
    (skeleton : skeletonEnergy J shape F D φ ≤
      K * ε * ((∫ x, D.charge x ^ (5/3 : ℝ)) + ∫ x, kineticDensity Z x) + K * ε * (∫ x, D.charge x))
    (kinetic : (∫ x, kineticDensity Z x) ≤ 2 * (∫ x, kineticDensity S x) +
      2 * (∫ x, D.charge x * ‖φ.grad x‖^2)) :
    rotatedEnergy F D φ ≤ (∫ c, T.energy F D φ c) + ∫ x, tilingExterior D φ S ε (5*K) x := by
  obtain ⟨h1, h2, h53, hq⟩ := relevant_moments hm
  have hw := mul_nonneg hK hε.le
  have hkin := kinetic.trans (add_le_add_right (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 2)) _)
  have hks := mul_le_mul_of_nonneg_left (add_le_add h53 hkin) hw
  have hkn := mul_nonneg hw (show 0 ≤ ∫ x, kineticDensity S x from integral_nonneg fun _ => sq_nonneg _)
  rw [integral_tilingExterior ε (5*K) hm hs]
  linarith only [tiling, skeleton, hks, mul_le_mul_of_nonneg_left h1 hw,
    mul_le_mul_of_nonneg_left h2 hw, hkn]

/-- The lower finite tiling error for a dilation t, with width t and cell
size t/ε. -/
def lowerTilingError (D : Density) (ε K t : ℝ) : ℝ :=
  K * ε * ((t⁻¹ + (t⁻¹)^2) * (∫ x, D.charge x) + t^2 * (∫ x, D.charge x ^ 2))

def TetrahedralCutoffs.lowerCorrection {T : AveragedTiles} {side : CutoffSide} {ε k : ℝ}
    (H : TetrahedralCutoffs T side ε k) (D : Density) (K : ℝ) : ℝ := by
  letI := T.space
  exact ∫ i, lowerTilingError D ε K (H.dilation i) ∂T.measure

private theorem TetrahedralCutoffs.correction_le {T : AveragedTiles} {side : CutoffSide} {ε k K : ℝ}
    (H : TetrahedralCutoffs T side ε k) {D : Density} {φ : Phase} (hε : 0 < ε) (hK : 0 ≤ K)
    (hm : Integrable (massDensity D φ)) :
    H.lowerCorrection D K ≤ K * ε * (10 * ∫ x, massDensity D φ x) := by
  let := T.space
  let := T.probability
  obtain ⟨h1, h2, _, _⟩ := relevant_moments hm
  have hr : 0 ≤ ∫ x, D.charge x := integral_nonneg D.charge_nonneg
  have hr2 : 0 ≤ ∫ x, D.charge x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hpoint (i : T.Parameter) : lowerTilingError D ε K (H.dilation i) ≤
      K * ε * (10 * ∫ x, massDensity D φ x) := by
    have hl : (1/2 : ℝ) ≤ H.dilation i := (H.scale i).1
    have hu : H.dilation i ≤ (3/2 : ℝ) := (H.scale i).2
    have hp : 0 < H.dilation i := by linarith
    have hi : (H.dilation i)⁻¹ ≤ 2 := (inv_le_comm₀ hp (by norm_num)).2 (by linarith)
    have hinv := inv_nonneg.mpr hp.le
    have ha : (H.dilation i)⁻¹ + ((H.dilation i)⁻¹)^2 ≤ 6 := by
      nlinarith only [hi, mul_nonneg (sub_nonneg.mpr hi) (add_nonneg (by norm_num : (0:ℝ) ≤ 2) hinv)]
    have hb : (H.dilation i)^2 ≤ 4 := by
      nlinarith only [mul_nonneg (by linarith : 0 ≤ 2 - H.dilation i) (by linarith : 0 ≤ 2 + H.dilation i)]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hε.le)
    linarith only [mul_le_mul_of_nonneg_right ha hr, mul_le_mul_of_nonneg_right hb hr2, h1, h2]
  have hpos (i : T.Parameter) : 0 ≤ lowerTilingError D ε K (H.dilation i) := by
    have h : (1/2 : ℝ) ≤ H.dilation i := (H.scale i).1
    have hp : 0 ≤ H.dilation i := by linarith
    dsimp [lowerTilingError]
    positivity
  have ha : Measurable H.dilation := H.dilation_measurable
  have hconst := integrable_const (μ := T.measure) (K * ε * (10 * ∫ x, massDensity D φ x))
  have herr : Integrable (fun i => lowerTilingError D ε K (H.dilation i)) T.measure := by
    apply hconst.mono'
    · apply Measurable.aestronglyMeasurable
      unfold lowerTilingError
      fun_prop
    · exact ae_of_all _ fun i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos i)]
        exact hpoint i
  have hi := integral_mono herr hconst hpoint
  simpa [TetrahedralCutoffs.lowerCorrection] using hi

/-- Remove the finite lower-bound prefactor using an upper bound on the
whole-space energy. The loss is controlled even when the tile energy is
negative. -/
theorem TetrahedralCutoffs.lower_localization {T : AveragedTiles} {ε k K A : ℝ}
    (H : TetrahedralCutoffs T .lower ε k) {F : GasEnergies} {D : Density} {φ : Phase}
    {S : MatrixGradient} (hε : 0 < ε) (hK : 0 ≤ K) (hA : 0 ≤ A) (hsmall : K * ε ≤ 1 / 2)
    (hm : Integrable (massDensity D φ)) (hs : Integrable (kineticDensity S))
    (tiling : (1 - K * ε) * (∫ c, T.energy F D φ c) - H.lowerCorrection D K ≤ rotatedEnergy F D φ)
    (upper : rotatedEnergy F D φ ≤ A * ((∫ x, massDensity D φ x) + ∫ x, kineticDensity S x)) :
    -rotatedEnergy F D φ ≤ (∫ c, -T.energy F D φ c) +
      ∫ x, tilingExterior D φ S ε (2 * K * (A + 10)) x := by
  let M := ∫ x, massDensity D φ x
  let s := ∫ x, kineticDensity S x
  let I := ∫ c, T.energy F D φ c
  let E := rotatedEnergy F D φ
  have hm₀ : 0 ≤ M := integral_nonneg (massDensity_nonneg D φ)
  have hs₀ : 0 ≤ s := integral_nonneg fun _ => sq_nonneg _
  have hw := mul_nonneg hK hε.le
  have he : E ≤ A * (M + s) := upper
  have raw : (1 - K * ε) * I - H.lowerCorrection D K ≤ E := tiling
  have hcor : H.lowerCorrection D K ≤ K * ε * (10 * M) := H.correction_le hε hK hm
  rw [integral_neg, integral_tilingExterior ε _ hm hs]
  change -E ≤ -I + 2 * K * (A + 10) * ε * (M + s)
  by_cases hz : 0 ≤ I - E
  · have hl := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-K*ε by linarith) hz
    linarith only [hl, raw, hcor, mul_le_mul_of_nonneg_left he hw, mul_nonneg hw hs₀]
  · have cost : 0 ≤ 2 * K * (A + 10) * ε * (M + s) := by positivity
    linarith

/-- Shape and density identifications for a concrete signed comparison. -/
structure TilingOverhead (T : AveragedTiles) (P : TileProfile) (D : Density) (φ : Phase)
    (S : MatrixGradient) (side : CutoffSide) (ε A B : ℝ) where
  faceCoefficient : ℝ
  face_nonneg : 0 ≤ faceCoefficient
  kineticCoefficient : ℝ
  kinetic_nonneg : 0 ≤ kineticCoefficient
  face_le : kineticCoefficient * (96 * faceCoefficient) ≤ A
  three_le : 3 ≤ A
  exterior_le : B ≤ A
  directCoefficient : ℝ
  direct_le : directCoefficient ≤ A
  geometry : TetrahedralCutoffs T side ε faceCoefficient
  charge : P.charge = D.charge
  kinetic : P.kineticKernel = fun x => kineticCoefficient * geometry.kineticProfile x
  exterior : P.exterior = tilingExterior D φ S ε B
  direct : P.volumeCost = fun x => directCoefficient *
    (ε * massDensity D φ x + kineticDensity S x / ε)

private theorem TilingOverhead.control {T : AveragedTiles} {P : TileProfile} {D : Density} {φ : Phase}
    {S : MatrixGradient} {side : CutoffSide} {ε A B : ℝ}
    (H : TilingOverhead T P D φ S side ε A B) (hε : 0 < ε) (hle : ε ≤ 1)
    (hB : 0 ≤ B) (hcut : P.cutoff = T.cutoffProfile) : CutoffControl P D φ S ε A :=
  H.geometry.toControl P D φ S hε hle H.face_nonneg H.three_le H.kinetic_nonneg H.face_le hB H.exterior_le
    H.direct_le hcut H.kinetic H.charge H.exterior H.direct

/-- Finite inputs before the skeleton is combined with the direct errors or
the lower-bound prefactor is removed. -/
inductive FiniteTilingLaws (F : GasEnergies) (T : AveragedTiles) (P : TileProfile) (D : Density)
    (φ : Phase) (S : MatrixGradient) (ε A : ℝ) : ℝ → Prop where
  | upper (K : ℝ) (hK : 0 ≤ K) (H : TilingOverhead T P D φ S .upper ε A (5*K))
      (J : AveragedTiles) (shape : J.Parameter → Position → ℝ) (Z : MatrixGradient)
      (skeleton_integrable : SkeletonEnergyIntegrable J shape F D φ)
      (rotated_gradient : IsMatrixGradientOn Set.univ (fun x => rotate (φ.value x) (D.power (1/2) x)) Z)
      (finiteEnergy : ℝ → ℝ)
      (integrable : IntegrableOn (fun t => finiteEnergy t * SSW.scaleWeight t) SSW.scaleInterval)
      (split : SSW.scaleAverage finiteEnergy = (∫ c, T.energy F D φ c) + skeletonEnergy J shape F D φ)
      (tiling : ∀ α : ℝ, 0 < α → α < 1/2 → rotatedEnergy F D φ ≤ SSW.scaleAverageAt α finiteEnergy +
        (K * ε * (∫ x, D.charge x ^ 2)) * Real.log α⁻¹)
      (skeleton : skeletonEnergy J shape F D φ ≤
        K * ε * ((∫ x, D.charge x ^ (5/3 : ℝ)) + ∫ x, kineticDensity Z x) + K * ε * (∫ x, D.charge x))
      (kinetic : (∫ x, kineticDensity Z x) ≤ 2 * (∫ x, kineticDensity S x) +
        2 * (∫ x, D.charge x * ‖φ.grad x‖^2)) : FiniteTilingLaws F T P D φ S ε A 1
  | lower (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hsmall : K * ε ≤ 1/2)
      (H : TilingOverhead T P D φ S .lower ε A (2*K*(B+10)))
      (tiling : (1 - K * ε) * (∫ c, T.energy F D φ c) - H.geometry.lowerCorrection D K ≤
        rotatedEnergy F D φ)
      (energy_upper : rotatedEnergy F D φ ≤ B * ((∫ x, massDensity D φ x) + ∫ x, kineticDensity S x)) :
      FiniteTilingLaws F T P D φ S ε A (-1)

theorem FiniteTilingLaws.assemble {F : GasEnergies} {T : AveragedTiles} {P : TileProfile}
    {D : Density} {φ : Phase} {S : MatrixGradient} {ε A σ : ℝ}
    (H : FiniteTilingLaws F T P D φ S ε A σ) (hε : 0 < ε) (hle : ε ≤ 1)
    (hm : Integrable (massDensity D φ)) (hs : Integrable (kineticDensity S))
    (hcut : P.cutoff = T.cutoffProfile) (heng : P.tileEnergy = fun c => σ * T.energy F D φ c) :
    CutoffControl P D φ S ε A ∧
      σ * rotatedEnergy F D φ ≤ (∫ c, P.tileEnergy c) + ∫ x, P.exterior x := by
  cases H with
  | upper K hK H J shape Z _ _ finiteEnergy hint split tiling skeleton kinetic =>
    have hel := SSW.finite_upper_at_half_le_one (B := 0) hint
      (mul_nonneg (mul_nonneg hK hε.le) (integral_nonneg fun x => sq_nonneg (D.charge x)))
      (fun α ha hb => by simpa only [add_zero] using tiling α ha hb)
    rw [add_zero, split] at hel
    refine ⟨H.control hε hle (by positivity) hcut, ?_⟩
    simp only [heng, H.exterior, one_mul]
    exact upper_tiling_localization T J shape hε hK hm hs hel skeleton kinetic
  | lower K B hK hB hsmall H tiling energy_upper =>
    refine ⟨H.control hε hle (by positivity) hcut, ?_⟩
    simp only [heng, H.exterior, neg_one_mul]
    exact H.geometry.lower_localization hε hK hB hsmall hm hs tiling energy_upper

end TSGA.Localization
