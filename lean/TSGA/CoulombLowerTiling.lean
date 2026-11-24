import TSGA.TetrahedronBoundary
import TSGA.FiniteCoulombSpirals
import TSGA.CutoffRepresentability
import TSGA.CutoffFisher
import Mathlib.Analysis.Convex.Contractible
import TSGA.CoulombRigidMotion

/-! # The lower Coulomb localization comparison

Write the translation average of the tetrahedral tiling as an integral over
the tile center. All orientations then have the same interior set of centers.
Outside the boundary layer, the outer density cutoff is constant on the
whole support of the inner tile.
-/

noncomputable section

namespace TSGA.ManyBody

open SSW MeasureTheory Set Filter Metric
open scoped Topology ComplexOrder InnerProductSpace Convolution

/-- An orientation distribution giving the uniform spherical average. Both
proper and improper frames preserve the Coulomb energy. -/
structure TileOrientationLaw where
  Frames : Type
  [space : MeasurableSpace Frames]
  law : Measure Frames
  [probability : IsProbabilityMeasure law]
  frame : Frames → Position ≃ₗᵢ[ℝ] Position
  average : ∀ (f : Position → ℝ), Continuous f → ∀ q : Position,
    Integrable (fun u => f (frame u q)) law ∧
      (∫ u, f (frame u q) ∂law) = directionAverage f ‖q‖

attribute [instance] TileOrientationLaw.space TileOrientationLaw.probability

/-- Energy of one localized Fock state with the Hartree term evaluated at
its prescribed marginal. -/
def localStateEnergy (Γ : MixedState) (F : Position → SpinMatrix) : ℝ :=
  Γ.kinetic + Γ.interaction - hartree (fun x => (F x).trace.re)

/-- The scalar localization function for a rotated tetrahedron centered at z. -/
def centeredWindow (η : Mollifier) (ℓ δ : ℝ) (R : Position ≃ₗᵢ[ℝ] Position)
    (z x : Position) : ℝ := smoothedIndicator (tetrahedron ℓ) η δ (R (x-z))

/-- The state-level smeared Graf–Schenker inequality with the IMS kinetic
error, in the integral-over-centers form of Lewin–Lieb–Seiringer (2020),
Eq. (54). Each localized state has marginal ξ F by geometric localization.
The volume factor is the mass of a single tile. -/
def SmearedGrafSchenker (η : Mollifier) (O : TileOrientationLaw) (C : ℝ) : Prop :=
  ∀ (F : Position → SpinMatrix) (Γ : MixedState), feasible F Γ →
    ∀ {ℓ δ : ℝ}, 0 < ℓ → 0 < δ → 2*C*δ ≤ ℓ →
    let V := regionVolume (tetrahedron ℓ)
    let field := fun u z x => ((centeredWindow η ℓ δ (O.frame u) z x : ℝ) : ℂ) • F x
    ∃ s : O.Frames → Position → MixedState,
      (∀ᵐ u ∂O.law, ∀ᵐ z, feasible (field u z) (s u z)) ∧
      (∀ᵐ u ∂O.law, Integrable (fun z => localStateEnergy (s u z) (field u z) / V)) ∧
      Integrable (fun u => ∫ z, localStateEnergy (s u z) (field u z) / V) O.law ∧
      (1-C*δ/ℓ)*(∫ u, ∫ z, localStateEnergy (s u z) (field u z) / V ∂volume ∂O.law) -
        C/ℓ*((1+δ⁻¹)*(∫ x, (F x).trace.re) + δ^3*(∫ x, (F x).trace.re^2)) ≤
          localStateEnergy Γ F

private theorem smooth_mass {Ω : Set Position} (hop : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (χ : Mollifier) {d : ℝ} (hd : 0 < d) : ∫ x, smoothedIndicator Ω χ d x = regionVolume Ω := by
  classical
  have hi : Integrable (Ω.indicator (fun _ => (1:ℝ))) := (integrable_indicator_iff hop.measurableSet).2
    (integrableOn_const (C := (1:ℝ)) hbd.measure_lt_top.ne)
  rw [smoothedIndicator, integral_convolution _ hi (χ.scaled_integrable hd), χ.scaled_mass hd,
    integral_indicator hop.measurableSet]
  simp [regionVolume]

/-- When the ball around a tile center misses the outer boundary it lies
entirely inside the domain or entirely outside its closure. -/
private theorem ball_side {Ω : Set Position} (hop : IsOpen Ω) {z : Position} {b : ℝ}
    (hb : 0 < b) (hz : z ∉ thickening b (frontier Ω)) :
    ∀ y ∈ ball z b, (y ∈ Ω ↔ z ∈ Ω) := by
  have hd : ball z b ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro y hy
    by_cases h : y ∈ Ω
    · exact Or.inl h
    · refine Or.inr (fun hc => hz (mem_thickening_iff.mpr ⟨y,?_,?_⟩))
      · exact ⟨hc,by simpa only [hop.interior_eq] using h⟩
      · simpa only [dist_comm] using (mem_ball.mp hy)
  have h := IsPreconnected.subset_or_subset hop isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ hy hc => hc (subset_closure hy)) hd (convex_ball z b).isPreconnected
  intro y hy
  rcases h with h | h
  · exact iff_of_true (h hy) (h (mem_ball_self hb))
  · exact iff_of_false (fun hyΩ => h hy (subset_closure hyΩ))
      (fun hzΩ => h (mem_ball_self hb) (subset_closure hzΩ))

private theorem kernel_radius (χ : Mollifier) : ∃ r > 0, ∀ {δ : ℝ}, 0 < δ →
    ∀ {x : Position}, χ.scaled δ x ≠ 0 → ‖x‖ < r*δ := by
  obtain ⟨r,hr,hs⟩ := χ.compact.isBounded.subset_ball_lt 0 (0 : Position)
  refine ⟨r,hr,?_⟩
  intro δ hd x hx
  have hk : χ.kernel (δ⁻¹ • x) ≠ 0 := fun hz => hx (by simp [Mollifier.scaled,hz])
  have h := mem_ball.mp (hs (subset_tsupport χ.kernel hk))
  simp only [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le),← div_eq_inv_mul] at h
  exact (div_lt_iff₀ hd).mp h

private theorem smooth_constant {Ω : Set Position} (χ : Mollifier) {d : ℝ} (hd : 0 < d)
    (x : Position) (c : ℝ)
    (h : ∀ y, χ.scaled d (x-y) ≠ 0 → Ω.indicator (fun _ => (1:ℝ)) y = c) :
    smoothedIndicator Ω χ d x = c := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  change (∫ y, Ω.indicator (fun _ => (1:ℝ)) y * χ.scaled d (x-y)) = c
  have he (y) : Ω.indicator (fun _ => (1:ℝ)) y * χ.scaled d (x-y) = c*χ.scaled d (x-y) := by
    by_cases hz : χ.scaled d (x-y) = 0
    · simp [hz]
    · rw [h y hz]
  simp_rw [he]
  rw [integral_const_mul, integral_sub_left_eq_self, χ.scaled_mass hd,mul_one]

private theorem supported_window {η : Mollifier} {r ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ)
    (hη : ∀ {x : Position}, η.scaled δ x ≠ 0 → ‖x‖ < r*δ)
    (R : Position ≃ₗᵢ[ℝ] Position) (z x : Position) (hn : centeredWindow η ℓ δ R z x ≠ 0) :
    dist x z < 2*ℓ+r*δ := by
  by_contra! hlarge
  apply hn
  apply smooth_constant η hd _ 0
  intro y hy
  apply indicator_of_notMem
  intro hty
  have hnorm : ‖y‖ ≤ 2*ℓ := by simpa using (tetrahedron_subset he hty)
  have hk := hη hy
  have ht := norm_add_le (R (x-z)-y) y
  rw [sub_add_cancel,R.norm_map,← dist_eq_norm] at ht
  linarith

/-- Off a single orientation-independent boundary layer the product of the
two physical cutoffs equals either the whole inner cutoff or zero. -/
theorem centeredWindow_boundary (η χ : Mollifier) :
    ∃ a > 0, ∀ {Ω : Set Position}, IsOpen Ω → ∀ {ℓ δ d : ℝ}, 0 < ℓ → 0 < δ → 0 < d →
      ∀ (R : Position ≃ₗᵢ[ℝ] Position) (z : Position),
      z ∉ thickening (a*(ℓ+δ+d)) (frontier Ω) → ∀ x,
        centeredWindow η ℓ δ R z x * smoothedIndicator Ω χ d x =
          centeredWindow η ℓ δ R z x * Ω.indicator (fun _ => (1:ℝ)) z := by
  classical
  obtain ⟨r,hr,hη⟩ := kernel_radius η
  obtain ⟨s,hs,hχ⟩ := kernel_radius χ
  let a := 2+r+s
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a,ha,?_⟩
  intro Ω hop ℓ δ d he hd hD R z hz x
  by_cases hx : centeredWindow η ℓ δ R z x = 0
  · simp [hx]
  congr 1
  apply smooth_constant χ hD
  intro y hy
  have hdist := supported_window he hd (hη hd) R z x hx
  have hdy := hχ hD hy
  have hlt : dist y z < a*(ℓ+δ+d) := by
    have htriangle := dist_triangle y x z
    rw [dist_comm y x,dist_eq_norm x y] at htriangle
    dsimp [a]
    nlinarith only [htriangle,hdist,hdy,mul_nonneg hr.le he.le,mul_nonneg hs.le he.le,
      mul_nonneg hs.le hd.le,mul_nonneg hr.le hD.le,hd,hD]
  have hh := ball_side hop (mul_pos ha (by positivity)) hz y hlt
  by_cases hw : z ∈ Ω
  · simp [hw,hh.mpr hw]
  · simp [hw,mt hh.mp hw]

private theorem flat_state (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    {Ω : Set Position} (hop : IsOpen Ω) (hbd : Bornology.IsBounded Ω) (hv : 0 < regionVolume Ω)
    (χ : Mollifier) {d : ℝ} (hd : 0 < d) {A : SpinMatrix} (hA : A.PosSemidef) :
    ∃ Γ, feasible (fun x => (smoothedIndicator Ω χ d x : ℂ) • A) Γ := by
  let f := smoothedIndicator Ω χ d
  have hm := smooth_mass hop hbd χ hd
  have hi : Integrable f := Integrable.of_integral_ne_zero (hm.trans_ne hv.ne')
  obtain ⟨g,hw,hg⟩ := smoothedIndicator_sqrt_sobolev sob hop.measurableSet hbd.measure_lt_top.ne χ hd
  exact H.representable_cutoff (fun x => (smoothedIndicator_bounds Ω χ hd x).1) hi g hw hg hA

/-- Continuity in the wavevector follows from corrected concavity of the finite Coulomb spiral. -/
theorem coulomb_continuous_tile (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (η : Mollifier) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) {A : SpinMatrix} (hA : A.PosSemidef) :
    Continuous (tileEnergy energy η A ℓ δ) := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  have rep := flat_state H sob (tetrahedron_open ℓ) (isBounded_closedBall.subset (tetrahedron_subset he))
    (tetrahedron_volume_pos he) η hd hA
  change ∃ Γ, feasible (fun x => (f x : ℂ) • A) Γ at rep
  have spin (k : Position) : axialSpiral (fun x => (f x : ℂ) • A) k = cutoffSpiral f A k :=
    funext fun x => rotate_smul _ _ _
  change Continuous (fun k => energy (cutoffSpiral f A k)/regionVolume (tetrahedron ℓ))
  simpa only [spin] using (finiteCoulombSpiral_continuous rep).div_const (regionVolume (tetrahedron ℓ))

private theorem centeredWindow_mass (η : Mollifier) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ)
    (R : Position ≃ₗᵢ[ℝ] Position) (z : Position) :
    (∫ x, centeredWindow η ℓ δ R z x) = regionVolume (tetrahedron ℓ) := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  change (∫ x, (fun y => f (R y)) (x-z)) = _
  calc
    _ = ∫ y, f (R y) := integral_sub_right_eq_self (fun y => f (R y)) z
    _ = ∫ y, f y := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding f
    _ = _ := tile_cutoff_mass η he hd

/-- The Lieb–Oxford cost of a boundary state is bounded using only the mass
of the inner window. The comparison includes the entire boundary layer on
both sides of the outer domain. -/
private theorem boundary_state_floor (H : FiniteEnergyInputs) {A : SpinMatrix} (hA : A.PosSemidef)
    {ξ f : Position → ℝ} (hξ : ∀ x, ξ x ∈ Icc 0 1) (hf : ∀ x, f x ∈ Icc 0 1)
    {V : ℝ} (hv : 0 < V) (mass : ∫ x, ξ x = V) (q : Position)
    {Γ : MixedState} (rep : feasible (fun x => (ξ x : ℂ) • cutoffSpiral f A q x) Γ) :
    -H.loCoeff*A.trace.re^(4/3:ℝ) ≤ localStateEnergy Γ (fun x => (ξ x : ℂ) • cutoffSpiral f A q x) / V := by
  let F := fun x => (ξ x : ℂ) • cutoffSpiral f A q x
  let D : Density := ⟨F, fun x => ((rotate_posSemidef _ hA).smul (Complex.zero_le_real.mpr (hf x).1)).smul
    (Complex.zero_le_real.mpr (hξ x).1)⟩
  let ρ := A.trace.re
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hi : Integrable ξ := Integrable.of_integral_ne_zero (mass.trans_ne hv.ne')
  have hc (x) : D.charge x = (ξ x*f x)*ρ := by simp [D,F,Density.charge,cutoffSpiral,ρ,mul_assoc]
  have hm : chargeMoment D (4/3) ≤ V*ρ^(4/3:ℝ) := by
    have hh := integral_mono_of_nonneg (μ := volume)
      (ae_of_all _ fun x => Real.rpow_nonneg (D.charge_nonneg x) (4/3:ℝ)) (hi.mul_const (ρ^(4/3:ℝ)))
      (ae_of_all _ fun x => by
        dsimp only
        rw [hc,Real.mul_rpow (mul_nonneg (hξ x).1 (hf x).1) hr]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr _)
        have hle := mul_le_of_le_one_right (hξ x).1 (hf x).2
        exact (Real.rpow_le_self_of_le_one (mul_nonneg (hξ x).1 (hf x).1)
          (hle.trans (hξ x).2) (by norm_num)).trans hle)
    exact hh.trans_eq (by rw [integral_mul_const,mass])
  have hlo := H.liebOxford D Γ rep
  have h := mul_le_mul_of_nonneg_left hm H.lo_nonneg
  apply (le_div_iff₀ hv).2
  change -H.loCoeff*ρ^(4/3:ℝ)*V ≤ Γ.kinetic+Γ.interaction-hartree D.charge
  nlinarith only [hlo,h,Γ.kinetic_nonneg]

/-- A finite interior center contributes the energy of the unshifted tile
with rotated wavevector. -/
theorem centered_energy
    (η : Mollifier) (ℓ δ : ℝ) (R : Position ≃ₗᵢ[ℝ] Position) (z : Position)
    (A : SpinMatrix) (q : Position) :
    energy (cutoffSpiral (centeredWindow η ℓ δ R z) A q) / regionVolume (tetrahedron ℓ) =
      tileEnergy energy η A ℓ δ (R q) := by
  let ξ := smoothedIndicator (tetrahedron ℓ) η δ
  change energy (cutoffSpiral (fun x => ξ (R (x-z))) A q) / regionVolume (tetrahedron ℓ) =
    energy (cutoffSpiral ξ A (R q))/regionVolume (tetrahedron ℓ)
  simpa only [map_sub] using
    congrArg (· / regionVolume (tetrahedron ℓ)) (coulomb_spiral_rigidMotion ξ A q (R z) R)

/-- Integrating over the centers of a fixed orientation. The interior and
boundary sets are independent of orientation and disjoint. -/
private theorem center_integral {I B : Set Position} (hI : MeasurableSet I) (hB : MeasurableSet B)
    (fi : volume I ≠ ⊤) (fb : volume B ≠ ⊤) (disj : Disjoint I B)
    {e k : ℝ} {v : Position → ℝ} (hi : Integrable v)
    (h : ∀ᵐ z, (z ∈ I → e ≤ v z) ∧ (z ∈ B → -k ≤ v z) ∧ (z ∉ I → z ∉ B → 0 ≤ v z)) :
    regionVolume I*e - regionVolume B*k ≤ ∫ z, v z := by
  classical
  have hci := (integrable_indicator_iff hI).2 (integrableOn_const (C := e) fi)
  have hcb := (integrable_indicator_iff hB).2 (integrableOn_const (C := -k) fb)
  have hh := integral_mono_ae (hci.add hcb) hi (h.mono fun z hz => by
    by_cases hzI : z ∈ I
    · have hzB := Set.disjoint_left.mp disj hzI
      simpa [hzI,hzB] using hz.1 hzI
    · by_cases hzB : z ∈ B
      · simpa [hzI,hzB] using hz.2.1 hzB
      · simpa [hzI,hzB] using hz.2.2 hzI hzB)
  simpa only [Pi.add_apply,integral_add hci hcb,integral_indicator_const _ hI,integral_indicator_const _ hB,
    regionVolume,smul_eq_mul,mul_neg,sub_eq_add_neg] using hh

/-- The common interior fraction is formed from center volumes after applying
the IMS and Graf–Schenker prefactor. -/
def centerWeight (Ω B : Set Position) (loss : ℝ) :=
  (1-loss)*(regionVolume (Ω \ B)/regionVolume Ω)

/-- The omitted fraction is bounded by the sum of the normalization loss and the boundary volume fraction. -/
theorem centerWeight_bounds {Ω B : Set Position} (hm : MeasurableSet B) (hΩ : volume Ω ≠ ⊤)
    (hb : volume B ≠ ⊤) (hv : 0 < regionVolume Ω) {loss : ℝ} (hl : loss ∈ Icc 0 1) :
    0 ≤ centerWeight Ω B loss ∧ 1-(loss+regionVolume B/regionVolume Ω) ≤ centerWeight Ω B loss ∧
      centerWeight Ω B loss ≤ 1 := by
  have hs := measureReal_inter_add_sdiff (μ := volume) (s := Ω) hm hΩ
  have hbnd := measureReal_mono (μ := volume) (s₁ := Ω ∩ B) inter_subset_right hb
  have hi := measureReal_mono (μ := volume) (s₁ := Ω \ B) sdiff_subset hΩ
  change regionVolume (Ω ∩ B) + regionVolume (Ω \ B) = regionVolume Ω at hs
  change regionVolume (Ω ∩ B) ≤ regionVolume B at hbnd
  change regionVolume (Ω \ B) ≤ regionVolume Ω at hi
  have hu := (div_le_one hv).2 hi
  have hp : 0 ≤ regionVolume (Ω \ B)/regionVolume Ω := div_nonneg ENNReal.toReal_nonneg hv.le
  have h := (div_le_div_iff_of_pos_right hv).2 (show regionVolume Ω ≤ regionVolume B+regionVolume (Ω \ B) by linarith)
  rw [div_self hv.ne',add_div] at h
  unfold centerWeight
  exact ⟨mul_nonneg (sub_nonneg.mpr hl.2) hp, by nlinarith only [h,mul_nonneg hl.1 (sub_nonneg.mpr hu)],
    (mul_le_of_le_one_left hp (by linarith [hl.1])).trans hu⟩

/-- Exact charge and an upper bound on its square for a smoothed spiral domain. -/
theorem cutoff_charge_integrals {Ω : Set Position} (hop : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (hv : 0 < regionVolume Ω) (χ : Mollifier) {d : ℝ} (hd : 0 < d) (A : SpinMatrix) (q : Position) :
    let F := cutoffSpiral (smoothedIndicator Ω χ d) A q
    (∫ x, (F x).trace.re) = regionVolume Ω * A.trace.re ∧
      (∫ x, (F x).trace.re^2) ≤ regionVolume Ω * A.trace.re^2 := by
  let f := smoothedIndicator Ω χ d
  have hf := smoothedIndicator_bounds Ω χ hd
  have hm := smooth_mass hop hbd χ hd
  have hi : Integrable f := Integrable.of_integral_ne_zero (hm.trans_ne hv.ne')
  have htr (x : Position) : (cutoffSpiral f A q x).trace.re = f x * A.trace.re := by simp [cutoffSpiral]
  change (∫ x, (cutoffSpiral f A q x).trace.re) = _ ∧ (∫ x, (cutoffSpiral f A q x).trace.re^2) ≤ _
  constructor
  · simp_rw [htr]
    rw [integral_mul_const,hm]
  · refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
      (hi.mul_const (A.trace.re^2)) (ae_of_all _ fun x => ?_)).trans_eq ?_
    · rw [htr,mul_pow]
      exact mul_le_mul_of_nonneg_right (by simpa only [sq] using mul_le_of_le_one_right (hf x).1 (hf x).2) (sq_nonneg _)
    · rw [integral_mul_const,hm]

/-- The finite-domain lower bound, uniform in the direction of the outer
wavevector, before using any regularity assumption on its boundary. -/
private theorem lower_domain (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    {O : TileOrientationLaw} {η χ : Mollifier} {C : ℝ} (hC : 0 ≤ C) (gs : SmearedGrafSchenker η O C)
    {Ω : Set Position} (hop : IsOpen Ω) (hbd : Bornology.IsBounded Ω) (hv : 0 < regionVolume Ω)
    {ℓ δ d : ℝ} (he : 0 < ℓ) (hd : 0 < δ) (hD : 0 < d) (hscale : 2*C*δ ≤ ℓ)
    {B : Set Position} (hB : MeasurableSet B) (fb : volume B ≠ ⊤)
    (cut : ∀ (R : Position ≃ₗᵢ[ℝ] Position) (z : Position), z ∉ B → ∀ x,
      centeredWindow η ℓ δ R z x * smoothedIndicator Ω χ d x =
        centeredWindow η ℓ δ R z x * Ω.indicator (fun _ => (1:ℝ)) z)
    {A : SpinMatrix} (hA : A.PosSemidef) (q : Position) :
    let ρ := A.trace.re
    let frac := regionVolume B / regionVolume Ω
    centerWeight Ω B (C*δ/ℓ) * averagedTile energy η A q ℓ δ -
      (H.loCoeff*ρ^(4/3:ℝ)*frac + C*(ρ/ℓ)*(1+δ⁻¹+δ^3*ρ)) ≤
      energy (cutoffSpiral (smoothedIndicator Ω χ d) A q) / regionVolume Ω := by
  classical
  let f := smoothedIndicator Ω χ d
  let F := cutoffSpiral f A q
  let V := regionVolume (tetrahedron ℓ)
  let D := regionVolume Ω
  let ρ := A.trace.re
  let k := H.loCoeff*ρ^(4/3:ℝ)
  let I := Ω \ B
  let t := 1-C*δ/ℓ
  let E := tileEnergy energy η A ℓ δ
  have hV : 0 < V := tetrahedron_volume_pos he
  have hk : 0 ≤ k := mul_nonneg H.lo_nonneg (Real.rpow_nonneg (RCLike.nonneg_iff.mp hA.trace_nonneg).1 _)
  have ht : t ∈ Icc 0 1 := ⟨sub_nonneg.mpr ((div_le_one he).2 (by linarith only [hscale,mul_nonneg hC hd.le])),
    sub_le_self _ (div_nonneg (mul_nonneg hC hd.le) he.le)⟩
  obtain ⟨Γ₀,h₀⟩ := flat_state H sob hop hbd hv χ hD hA
  let s₀ := cutoffRotation f A q ⟨Γ₀,h₀⟩
  have rep : ∃ Γ, feasible F Γ := ⟨s₀.val,s₀.property⟩
  have hf := smoothedIndicator_bounds Ω χ hD
  obtain ⟨hiE,avg⟩ := O.average E (coulomb_continuous_tile H sob η he hd hA) q
  have hm := cutoff_charge_integrals hop hbd hv χ hD A q
  change (∫ x, (F x).trace.re) = D*ρ ∧ (∫ x, (F x).trace.re^2) ≤ D*ρ^2 at hm
  have heq := hm.1
  let e := averagedTile energy η A q ℓ δ
  have state (Γ : MixedState) (hΓ : feasible F Γ) :
      t*(regionVolume I*e-regionVolume B*k) - C/ℓ*((1+δ⁻¹)*(D*ρ)+δ^3*(D*ρ^2)) ≤ localStateEnergy Γ F := by
    obtain ⟨s,feas,intZ,intU,loc⟩ := gs F Γ hΓ he hd hscale
    let ξ := fun u z => centeredWindow η ℓ δ (O.frame u) z
    let field := fun u z x => ((ξ u z x : ℝ) : ℂ) • F x
    let v := fun u z => localStateEnergy (s u z) (field u z)/V
    have cent : ∀ᵐ u ∂O.law, regionVolume I * E (O.frame u q) - regionVolume B*k ≤ ∫ z, v u z := by
      filter_upwards [feas,intZ] with u hu hi
      apply center_integral (hop.measurableSet.diff hB) hB (measure_ne_top_of_subset sdiff_subset hbd.measure_lt_top.ne)
        fb (Set.disjoint_left.mpr fun _ h => h.2) hi
      filter_upwards [hu] with z hz
      change feasible (field u z) (s u z) at hz
      have lower := sub_le_sub_right (levyLieb_le hz) (hartree (fun x => (field u z x).trace.re))
      change energy (field u z) ≤ localStateEnergy (s u z) (field u z) at lower
      have fixed (hb : z ∉ B) (x : Position) : field u z x =
          ((ξ u z x*Ω.indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ) • rotate (⟪q,x⟫_ℝ) A := by
        change (ξ u z x : ℂ) • ((f x : ℂ) • rotate _ A) = _
        rw [smul_smul,← Complex.ofReal_mul,cut (O.frame u) z hb]
      refine ⟨fun h => ?_, fun _ => ?_, fun hni hnb => ?_⟩
      · obtain ⟨hin,hout⟩ := h
        have eqf : field u z = cutoffSpiral (ξ u z) A q := funext fun x => by
          rw [fixed hout]; simp [cutoffSpiral,hin]
        calc
          E (O.frame u q) = energy (cutoffSpiral (ξ u z) A q)/V := (centered_energy η ℓ δ (O.frame u) z A q).symm
          _ = energy (field u z)/V := by rw [eqf]
          _ ≤ _ := div_le_div_of_nonneg_right lower hV.le
      · have hfloor := boundary_state_floor H hA (ξ := ξ u z) (f := f)
          (fun x => smoothedIndicator_bounds _ η hd _) hf hV (centeredWindow_mass η he hd _ z) q hz
        simpa only [k,← neg_mul] using hfloor
      · have ho : z ∉ Ω := fun h => hni ⟨h,hnb⟩
        have eqf : field u z = 0 := funext fun x => by rw [fixed hnb]; simp [ho]
        rw [show energy (field u z) = 0 from eqf ▸ energy_vacuum] at lower
        exact div_nonneg lower hV.le
    have hmean := integral_mono_ae ((hiE.const_mul _).sub (integrable_const _)) intU cent
    simp only [Pi.sub_apply] at hmean
    rw [integral_sub (hiE.const_mul _) (integrable_const _),integral_const_mul,avg,integral_const,
      probReal_univ,one_smul] at hmean
    have hm2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm.2 (by positivity : 0 ≤ δ^3))
      (div_nonneg hC he.le)
    change t*(∫ u, ∫ z, v u z ∂volume ∂O.law)-C/ℓ*((1+δ⁻¹)*(∫ x, (F x).trace.re)+δ^3*(∫ x, (F x).trace.re^2)) ≤ _ at loc
    rw [heq] at loc
    change regionVolume I*e-regionVolume B*k ≤ _ at hmean
    linarith only [mul_le_mul_of_nonneg_left hmean ht.1,hm2,loc]
  have hlo := le_levyLieb rep (a := t*(regionVolume I*e-regionVolume B*k) -
    C/ℓ*((1+δ⁻¹)*(D*ρ)+δ^3*(D*ρ^2)) + hartree (fun x => (F x).trace.re)) (fun Γ h => by
      have h := state Γ h; unfold localStateEnergy at h; linarith)
  have hb : 0 ≤ regionVolume B*k := mul_nonneg ENNReal.toReal_nonneg hk
  have hsmall := mul_le_of_le_one_left hb ht.2
  apply (le_div_iff₀ hv).2
  change (t*(regionVolume I/D)*e-(k*(regionVolume B/D)+C*(ρ/ℓ)*(1+δ⁻¹+δ^3*ρ)))*D ≤
    levyLieb F - hartree (fun x => (F x).trace.re)
  have hD0 : D ≠ 0 := hv.ne'
  have alg :
      (t*(regionVolume I/D)*e-(k*(regionVolume B/D)+C*(ρ/ℓ)*(1+δ⁻¹+δ^3*ρ)))*D =
      t*(regionVolume I*e)-regionVolume B*k-C/ℓ*((1+δ⁻¹)*(D*ρ)+δ^3*(D*ρ^2)) := by
    field_simp [hD0]
    ring
  rw [alg]
  linarith only [hlo,hsmall]

/-- Lieb–Oxford uniformly bounds every orientation of the inner tetrahedron. -/
theorem tile_floor (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (η : Mollifier)
    {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) {A : SpinMatrix} (hA : A.PosSemidef) (q : Position) :
    -(H.loCoeff*A.trace.re^(4/3:ℝ)) ≤ tileEnergy energy η A ℓ δ q := by
  let ξ := smoothedIndicator (tetrahedron ℓ) η δ
  let V := regionVolume (tetrahedron ℓ)
  let F := cutoffSpiral ξ A q
  let k := H.loCoeff*A.trace.re^(4/3:ℝ)
  have hv : 0 < V := tetrahedron_volume_pos he
  obtain ⟨Γ,hΓ⟩ := flat_state H sob (tetrahedron_open ℓ) (isBounded_closedBall.subset (tetrahedron_subset he))
    hv η hd hA
  let s := cutoffRotation ξ A q ⟨Γ,hΓ⟩
  have eqf : (fun x => (ξ x : ℂ) • cutoffSpiral (fun _ => 1) A q x) = F := by
    funext x; simp [F,cutoffSpiral]
  have hlo := le_levyLieb (M := F) ⟨s.val,s.property⟩ (a := -k*V+hartree (fun x => (F x).trace.re))
    (fun Γ hh => by
      rw [← eqf] at hh
      have hc := boundary_state_floor H hA (smoothedIndicator_bounds _ η hd)
        (fun _ => (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)) hv
        (tile_cutoff_mass η he hd) q hh
      rw [eqf] at hc
      have h := (le_div_iff₀ hv).mp hc
      change -H.loCoeff*A.trace.re^(4/3:ℝ)*V ≤ Γ.kinetic+Γ.interaction-hartree (fun x => (F x).trace.re) at h
      dsimp [k]
      linarith)
  apply (le_div_iff₀ hv).2
  change -k*V ≤ levyLieb F - hartree (fun x => (F x).trace.re)
  linarith

/-- Continuous wavevector functions are integrable on each sphere of directions. -/
theorem continuous_direction_integrable {E : Position → ℝ} (he : Continuous E) (q : Position) :
    Integrable (fun ω : sphere (0 : Position) 1 => E (‖q‖ • (ω : Position))) (volume : Measure Position).toSphere := by
  have h : Continuous (fun ω : sphere (0 : Position) 1 => E (‖q‖ • (ω : Position))) := by fun_prop
  exact integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ)

/-- The state and orientation law needed for the lower bounds are the same
for every spin, wavevector, outer domain and pair of scales. -/
structure CoulombLowerLocalization (η : Mollifier) where
  orientations : TileOrientationLaw
  coefficient : ℝ
  nonneg : 0 ≤ coefficient
  grafSchenker : SmearedGrafSchenker η orientations coefficient

private theorem interior_of_center (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    {η : Mollifier} {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) {A : SpinMatrix} (hA : A.PosSemidef)
    (q : Position) {w miss floor rem outer : ℝ}
    (wf : 0 ≤ w ∧ 1-miss ≤ w ∧ w ≤ 1) (hk : H.loCoeff*A.trace.re^(4/3:ℝ) ≤ floor)
    (bound : w*averagedTile energy η A q ℓ δ-rem ≤ outer) :
    InteriorLower (tileEnergy energy η A ℓ δ) ‖q‖ miss floor rem outer := by
  have hn : 0 ≤ H.loCoeff*A.trace.re^(4/3:ℝ) := mul_nonneg H.lo_nonneg
    (Real.rpow_nonneg (RCLike.nonneg_iff.mp hA.trace_nonneg).1 _)
  refine ⟨fun _ => w,continuous_direction_integrable (coulomb_continuous_tile H sob η he hd hA) q,
    aestronglyMeasurable_const,hn.trans hk,ae_of_all _ fun _ => wf,ae_of_all _ fun ω =>
      (neg_le_neg hk).trans (tile_floor H sob η he hd hA _),?_⟩
  simpa only [average_const_mul,averagedTile,directionAverage] using bound

private theorem avg_lower_const (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) {η : Mollifier}
    {L d : ℝ} (hL : 0 < L) (hD : 0 < d) {A : SpinMatrix} (hA : A.PosSemidef) (q : Position)
    {b : ℝ} (bound : ∀ q' : Position, ‖q'‖ = ‖q‖ → b ≤ tileEnergy energy η A L d q') :
    b ≤ averagedTile energy η A q L d := by
  have hh := direction_mono_add (f := fun _ => b) (d := 0) (integrable_const b)
    (continuous_direction_integrable (coulomb_continuous_tile H sob η hL hD hA) q) (fun ω => by
      rw [add_zero]
      apply bound
      simp [norm_smul,mem_sphere_zero_iff_norm.mp ω.property])
  simpa [averagedTile] using hh

/-- Lower comparison on arbitrary admissible domains, including the precise
boundary fraction along the sequence. -/
theorem CoulombLowerLocalization.domain_lower {η : Mollifier} (G : CoulombLowerLocalization η)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) {A : SpinMatrix} (hA : A.PosSemidef)
    (q : Position) : DomainLowerTiling energy η A q := by
  intro D
  obtain ⟨a,ha,cut⟩ := centeredWindow_boundary η D.mollifier
  let C := G.coefficient
  let ρ := A.trace.re
  let k := H.loCoeff*ρ^(4/3:ℝ)
  let c := max C 1
  refine ⟨a,ha,c,k,k,C*ρ*(2+ρ),?_⟩
  filter_upwards [D.tileLength_tendsto.eventually_ge_atTop (2*C)] with n hn
  let ℓ := D.tileLength n
  let B := thickening (a*(ℓ+1+D.delta n)) (frontier (D.region n))
  have hB : MeasurableSet B := isOpen_thickening.measurableSet
  have fb : volume B ≠ ⊤ := ((D.region_bounded n).closure.subset frontier_subset_closure).thickening.measure_lt_top.ne
  have he : 0 < ℓ := D.tileLength_pos n
  have hc : 0 ≤ C := G.nonneg
  have hsc : 2*C*1 ≤ ℓ := by simpa using hn
  have hw := centerWeight_bounds hB (D.region_bounded n).measure_lt_top.ne fb (D.vol_pos n)
    (loss := C*1/ℓ) ⟨div_nonneg (by simpa using hc) he.le,(div_le_one he).2 (by linarith)⟩
  have hb := lower_domain H sob G.nonneg G.grafSchenker
    (D.region_open n) (D.region_bounded n) (D.vol_pos n) he zero_lt_one (D.delta_pos n) hsc hB fb
    (cut (D.region_open n) he zero_lt_one (D.delta_pos n)) hA q
  have frac : 0 ≤ D.tileBoundaryFraction a n := div_nonneg ENNReal.toReal_nonneg (D.vol_pos n).le
  have hm : C*1/ℓ+D.tileBoundaryFraction a n ≤ c*(ℓ⁻¹+D.tileBoundaryFraction a n) := by
    have p := mul_le_mul_of_nonneg_right (le_max_left C 1) (inv_nonneg.mpr he.le)
    have r := mul_le_mul_of_nonneg_right (le_max_right C 1) frac
    dsimp [c]; rw [mul_one,div_eq_mul_inv]; linarith only [p,r]
  apply interior_of_center H sob he zero_lt_one hA q ⟨hw.1,(sub_le_sub_left hm 1).trans hw.2.1,hw.2.2⟩ le_rfl
  change _ ≤ energy (cutoffSpiral (D.cutoff n) A q)/D.vol n
  change centerWeight (D.region n) B (C*1/ℓ)*averagedTile energy η A q ℓ 1 -
    (k*D.tileBoundaryFraction a n+C*ρ*(2+ρ)/ℓ) ≤ _ 
  change centerWeight (D.region n) B (C*1/ℓ)*averagedTile energy η A q ℓ 1 -
    (k*D.tileBoundaryFraction a n+C*(ρ/ℓ)*(1+1⁻¹+1^3*ρ)) ≤ _ at hb
  convert hb using 1
  · norm_num
    ring
  · rfl

/-- One finite comparison, with arbitrary outer smoothing width, gives both
the two-scale estimate and the quantitative interior estimate. The factor
27744 is the boundary-layer coefficient 1156 divided by the reference volume 1/24. -/
theorem CoulombLowerLocalization.tetrahedra {η : Mollifier} (G : CoulombLowerLocalization η)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) :
    ∃ K₀ ≥ 1, ∀ K ≥ K₀, ∀ {A : SpinMatrix}, A.PosSemidef → ∀ (q : Position) {ℓ δ d : ℝ},
      0 < ℓ → 0 < δ → 0 < d → δ*K ≤ ℓ →
      let ρ := A.trace.re
      ∀ᶠ L : ℝ in atTop,
        InteriorLower (tileEnergy energy η A ℓ δ) ‖q‖ (K*(δ/ℓ+(ℓ+δ+d)/L))
          (K*(ρ*ρ^(1/3:ℝ))) (K*(ρ*ρ^(1/3:ℝ))*((ℓ+δ+d)/L)+
            K*(ρ/ℓ)*(1+δ⁻¹+δ^3*ρ)) (averagedTile energy η A q L d) := by
  obtain ⟨a,ha,cut⟩ := centeredWindow_boundary η η
  let b := 27744*a
  let C := G.coefficient
  let K₀ := max 1 (max (2*C) (max b (max H.loCoeff (H.loCoeff*b))))
  refine ⟨K₀,le_max_left ..,?_⟩
  intro K hK A hA q ℓ δ d he hd hD hscale
  have hCK₂ : 2*C ≤ K := (le_max_left ..).trans ((le_max_right ..).trans hK)
  have hCK : C ≤ K := by linarith [show 0 ≤ C from G.nonneg]
  have hbK : b ≤ K := (le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans hK))
  have hloK : H.loCoeff ≤ K := (le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans hK)))
  have hprodK : H.loCoeff*b ≤ K := (le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans hK)))
  let ρ := A.trace.re
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hp : ρ^(4/3:ℝ) = ρ*ρ^(1/3:ℝ) := by
    rw [show (4/3:ℝ) = 1+(1/3:ℝ) by norm_num,Real.rpow_add_of_nonneg hr (by norm_num) (by norm_num),Real.rpow_one]
  let w := a*(ℓ+δ+d)
  have hw : 0 < w := mul_pos ha (by positivity)
  have hsc : 2*C*δ ≤ ℓ := (mul_le_mul_of_nonneg_right hCK₂ hd.le).trans (by simpa [mul_comm] using hscale)
  filter_upwards [eventually_ge_atTop w] with L hLw
  have hL := hw.trans_le hLw
  let Ω := tetrahedron L
  let B := thickening w (frontier Ω)
  have hbd : Bornology.IsBounded Ω := isBounded_closedBall.subset (tetrahedron_subset hL)
  have hB : MeasurableSet B := isOpen_thickening.measurableSet
  have fb : volume B ≠ ⊤ := (hbd.closure.subset frontier_subset_closure).thickening.measure_lt_top.ne
  have hv := tetrahedron_volume_pos hL
  let frac := regionVolume B / regionVolume Ω
  let g := (ℓ+δ+d)/L
  have hg : 0 ≤ g := div_nonneg (by positivity) hL.le
  have hf : frac ≤ b*g := by
    have h := div_le_div_of_nonneg_right (tetrahedron_boundary_volume hw hLw) hv.le
    apply h.trans_eq
    rw [tetrahedron_volume hL]
    dsimp [b,g,w]
    field_simp [hL.ne']
    ring
  have hwgt := centerWeight_bounds hB hbd.measure_lt_top.ne fb hv (loss := C*δ/ℓ)
    ⟨div_nonneg (mul_nonneg G.nonneg hd.le) he.le,(div_le_one he).2 (by linarith only [hsc,mul_nonneg G.nonneg hd.le])⟩
  have hmiss : C*δ/ℓ+frac ≤ K*(δ/ℓ+g) := by
    have h1 := mul_le_mul_of_nonneg_right hCK (div_nonneg hd.le he.le)
    have h2 := mul_le_mul_of_nonneg_right hbK hg
    rw [mul_div_assoc,mul_add]
    exact add_le_add h1 (hf.trans h2)
  have hfloor := mul_le_mul_of_nonneg_right hloK (Real.rpow_nonneg hr (4/3:ℝ))
  rw [hp] at hfloor
  apply interior_of_center H sob he hd hA q
    ⟨hwgt.1,(sub_le_sub_left hmiss 1).trans hwgt.2.1,hwgt.2.2⟩ (by change H.loCoeff*ρ^(4/3:ℝ) ≤ _; rw [hp]; exact hfloor)
  apply avg_lower_const H sob hL hD hA q
  intro q' hn
  have h := lower_domain H sob G.nonneg G.grafSchenker (tetrahedron_open L)
    hbd hv he hd hD hsc hB fb (cut (tetrahedron_open L) he hd hD) hA q'
  have heq : averagedTile energy η A q' ℓ δ = averagedTile energy η A q ℓ δ := by simp only [averagedTile,hn]
  change centerWeight Ω B (C*δ/ℓ)*averagedTile energy η A q' ℓ δ -
    (H.loCoeff*ρ^(4/3:ℝ)*frac+C*(ρ/ℓ)*(1+δ⁻¹+δ^3*ρ)) ≤ tileEnergy energy η A L d q' at h
  rw [heq,hp] at h
  have hρ : 0 ≤ ρ*ρ^(1/3:ℝ) := mul_nonneg hr (Real.rpow_nonneg hr _)
  have hleft := mul_le_mul_of_nonneg_left hf (mul_nonneg H.lo_nonneg hρ)
  have hrgt := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprodK hρ) hg
  have hcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK (div_nonneg hr he.le))
    (by positivity : 0 ≤ 1+δ⁻¹+δ^3*ρ)
  linarith only [h,hleft,hrgt,hcost]

/-- Three lower tiling comparisons follow from the single state-level
localization inequality with the same quantitative constant. -/
theorem CoulombLowerLocalization.comparisons {η : Mollifier} (G : CoulombLowerLocalization η)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) :
    ∃ K₀ ≥ 1, ∀ K ≥ K₀,
      (∀ (A : SpinMatrix), A.PosSemidef → ∀ q, TetrahedronTwoScale energy η A q) ∧
      (∀ (A : SpinMatrix), A.PosSemidef → ∀ q, DomainLowerTiling energy η A q) ∧
      TileInteriorComparison energy η K := by
  obtain ⟨K₀,h₀,h⟩ := G.tetrahedra H sob
  refine ⟨K₀,h₀,?_⟩
  intro K hK
  refine ⟨?_,fun _ hA q => G.domain_lower H sob hA q,?_⟩
  · intro A hA q δ d hd hD
    let ρ := A.trace.re
    refine ⟨K,K*(ρ*ρ^(1/3:ℝ)),K*(ρ*ρ^(1/3:ℝ)),K*ρ*(1+δ⁻¹+δ^3*ρ),
      zero_le_one.trans (h₀.trans hK),?_⟩
    filter_upwards [eventually_ge_atTop (δ*K),eventually_gt_atTop (0:ℝ)] with ℓ hsc he
    filter_upwards [h K hK hA q he hd hD hsc] with L hL
    convert hL using 2
    ring
  · intro A hA q ℓ δ he hd hsc
    exact h K hK hA q he hd zero_lt_one hsc

end TSGA.ManyBody
