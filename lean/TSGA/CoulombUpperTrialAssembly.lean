import TSGA.CoulombUpperBoundaryEnergy
import TSGA.CoulombUpperComparison
import TSGA.CoulombTileUnfolding
import TSGA.CoulombDilationMeasure

/-! # Upper trials from finite Fock products on the periodic tiling -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization Metric Set
open scoped ComplexOrder

/-- The direct error left by mixing product states with different
pointwise charges. The order of integration agrees with Theorem 4.10. -/
def latticeVariance (O : TileOrientationLaw) (η : Mollifier) (charge : Position → ℝ)
    (ℓ δ t : ℝ) : ℝ :=
  ∫ u, ∫ τ, hartree (fun x =>
    (latticeTotalWindow (t*ℓ) (t*δ) η (O.frame u x-τ)-1)*charge x)
    ∂latticeShiftMeasure (t*ℓ) ∂O.law

def normalizedSkeleton (η : Mollifier) (b d : ℝ) (R : Position ≃ₗᵢ[ℝ] Position)
    (τ x : Position) : ℝ := latticeBlock b d η none (R x-τ)/2

/-- The periodic skeleton has mean mass of order d/b and mean Fisher energy
of order 1/(bd). These are the scalar skeleton estimates of Csirik and
Laestadius, in physical coordinates, for half the skeleton. -/
structure SkeletonFisherAverages (η : Mollifier) where
  coefficient : ℝ
  nonneg : 0 ≤ coefficient
  averages : ∀ {b d : ℝ}, 0 < d → d ≤ b/2 → ∀ R : Position ≃ₗᵢ[ℝ] Position,
    let μ := latticeShiftMeasure b
    let w := normalizedSkeleton η b d R
    ∃ h : Position → Position → Position,
      AEStronglyMeasurable (fun z : Position × Position => w z.1 z.2) (μ.prod volume) ∧
      AEStronglyMeasurable (fun z : Position × Position => h z.1 z.2) (μ.prod volume) ∧
      (∀ᵐ τ ∂μ, ∀ i, WeakPartialOn univ i (fun x => √(w τ x)) (fun x => h τ x i)) ∧
      (∀ᵐ x, Integrable (fun τ => w τ x) μ ∧ (∫ τ, w τ x ∂μ) ≤ coefficient*(d/b)) ∧
      (∀ᵐ x, Integrable (fun τ => ‖h τ x‖^2) μ ∧ (∫ τ, ‖h τ x‖^2 ∂μ) ≤ coefficient/(b*d))

/-- Analytic prerequisites for the finite integrals over rotations and
translations. Every energy here is evaluated on the specified Coulomb
density, and these fields contain no energy inequalities. -/
structure CoulombLatticeIntegrals (O : TileOrientationLaw) (η : Mollifier) (f : Position → ℝ)
    (M : SpinMatrix) (q : Position) (ℓ δ : ℝ) : Prop where
  measurable : ∀ i j, Measurable (fun x => cutoffSpiral f M q x i j)
  integrable : ∀ i j, Integrable (fun x => cutoffSpiral f M q x i j)
  compact : ∃ B : ℝ, ∀ x, cutoffSpiral f M q x ≠ 0 → ‖x‖ ≤ B
  direct : Integrable (directKernel (fun x => (cutoffSpiral f M q x).trace.re)
    (fun x => (cutoffSpiral f M q x).trace.re)) pairVolume
  shifts : ∀ t ∈ scaleInterval, ∀ R : Position ≃ₗᵢ[ℝ] Position,
    let b := t*ℓ
    let d := t*δ
    let D := cutoffSpiral f M q
    Integrable (latticeBlockEnergySum b d η R D) (latticeShiftMeasure b) ∧
      Integrable (fun τ => energy (latticeBlockDensity b d η R D τ none)) (latticeShiftMeasure b)
  centers : ∀ t ∈ scaleInterval, ∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => energy
    (cutoffSpiral (fun x => f x*centeredWindow η (t*ℓ-t*δ) (t*δ) R z x) M q))
  centerFrames : ∀ t ∈ scaleInterval, Integrable (fun u => ∫ z, energy
    (cutoffSpiral (fun x => f x*centeredWindow η (t*ℓ-t*δ) (t*δ) (O.frame u) z x) M q)) O.law
  shiftsFrames : ∀ t ∈ scaleInterval, Integrable (fun u => ∫ τ, ∑' p : LatticeTile,
    energy (cutoffSpiral (fun x => f x*latticeWindow (t*ℓ) (t*δ) η p (O.frame u x-τ)) M q)
    ∂latticeShiftMeasure (t*ℓ)) O.law
  directFrames : ∀ t ∈ scaleInterval, Integrable (fun u => ∫ τ, hartree (fun x =>
    (latticeTotalWindow (t*ℓ) (t*δ) η (O.frame u x-τ)-1)*(cutoffSpiral f M q x).trace.re)
    ∂latticeShiftMeasure (t*ℓ)) O.law
  directScales : IntegrableOn (fun t => latticeVariance O η
    (fun x => (cutoffSpiral f M q x).trace.re) ℓ δ t * scaleWeight t) scaleInterval

/-- The electrostatic variance bound. At the earlier quadratic estimate
its coefficient is proportional to δ². For the manuscript's sharper
estimate it is proportional to δ³/ℓ. -/
def CoulombVarianceBound (O : TileOrientationLaw) (η : Mollifier) (p : CoulombTilingCost) (A : ℝ) : Prop :=
  ∀ {Ω : Set Position}, IsOpen Ω → Bornology.IsBounded Ω → ∀ (χ : Mollifier) {d : ℝ}, 0 < d →
    ∀ {ρ : ℝ}, 0 ≤ ρ → ∀ {ℓ δ : ℝ}, 0 < δ → δ ≤ ℓ/2 → ∀ α : ℝ, 0 < α → α < 1/2 →
    let charge := fun x => smoothedIndicator Ω χ d x * ρ
    scaleAverageAt α (latticeVariance O η charge ℓ δ) ≤
      (A*p.cost ℓ δ)*(∫ x, charge x^2)*Real.log α⁻¹

private theorem cell_field_eq (η : Mollifier) (f : Position → ℝ) (M : SpinMatrix)
    (q : Position) (b d : ℝ) (R : Position ≃ₗᵢ[ℝ] Position) (τ : Position) (p : LatticeTile) :
    latticeBlockDensity b d η R (cutoffSpiral f M q) τ (some p) =
      cutoffSpiral (fun x => f x*latticeWindow b d η p (R x-τ)) M q := by
  funext x
  simp only [latticeBlockDensity,latticeBlock,cutoffSpiral,smul_smul,Complex.ofReal_mul]
  rw [mul_comm]

private theorem skeleton_field_eq (η : Mollifier) (f : Position → ℝ) (M : SpinMatrix)
    (q : Position) (b d : ℝ) (R : Position ≃ₗᵢ[ℝ] Position) (τ : Position) :
    latticeBlockDensity b d η R (cutoffSpiral f M q) τ none =
      cutoffSpiral (fun x => f x*normalizedSkeleton η b d R τ x) ((2:ℝ) • M) q := by
  funext x
  have hM : (2:ℝ) • M = (2:ℂ) • M := by ext i j; simp [Complex.real_smul]
  simp only [hM,latticeBlockDensity,cutoffSpiral,rotate_smul,smul_smul,normalizedSkeleton,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  congr 1
  ring

theorem scale_average_bound {f g : ℝ → ℝ} {e C α : ℝ} (ha : 0 < α) (hα : α < 1/2)
    (hf : IntegrableOn (fun t => f t*scaleWeight t) scaleInterval)
    (hg : IntegrableOn (fun t => g t*scaleWeight t) scaleInterval)
    (h : ∀ t ∈ scaleInterval, e ≤ f t+C+g t) : e ≤ scaleAverageAt α f + C + scaleAverageAt α g := by
  let I := Icc (1-α) (1+α)
  have sub : I ⊆ scaleInterval := fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hw := scaleWeight_integrableOn.mono_set sub
  have hp : 0 < ∫ t in I, scaleWeight t := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae _ hw).2
    · have inc : I ⊆ Function.support scaleWeight := fun t ht => inv_ne_zero (pow_ne_zero _ (by linarith [(sub ht).1]))
      rw [inter_eq_right.mpr inc,Real.volume_Icc]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    · exact ae_of_all _ fun t => inv_nonneg.mpr (by positivity : 0 ≤ t^4)
  have hf' := hf.mono_set sub
  have hg' := hg.mono_set sub
  have low := integral_mono_ae (hw.const_mul e) ((hf'.add (hw.const_mul C)).add hg')
    (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := I) measurableSet_Icc |>.mono fun t ht =>
      show e*scaleWeight t ≤ f t*scaleWeight t + C*scaleWeight t + g t*scaleWeight t by
        simpa only [add_mul] using mul_le_mul_of_nonneg_right (h t (sub ht))
          (show 0 ≤ scaleWeight t from inv_nonneg.mpr (by positivity : 0 ≤ t^4)))
  change (∫ t in I, e*scaleWeight t) ≤ ∫ t in I, f t*scaleWeight t+C*scaleWeight t+g t*scaleWeight t at low
  have fc : IntegrableOn (fun t => f t*scaleWeight t+C*scaleWeight t) I := hf'.add (hw.const_mul C)
  rw [integral_const_mul,integral_add fc hg',integral_add hf' (hw.const_mul C),
    integral_const_mul] at low
  change e ≤ _ / (∫ t in I, scaleWeight t) + C + _ / (∫ t in I, scaleWeight t)
  apply (le_of_mul_le_mul_right ?_ hp)
  field_simp [hp.ne']
  linarith only [low]

theorem skeleton_shift_bounds (H : FiniteEnergyInputs) (W : WindowSobolevRules)
    {η : Mollifier} (s : SkeletonFisherAverages η)
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {f : Position → ℝ} (hf : ∀ x, f x ∈ Icc 0 1) (fi : Integrable f)
    (g : Position → Position) (gf : MemLp g 2)
    (df : ∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i))
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) {b d : ℝ} (hd : 0 < d) (hsc : d ≤ b/2)
    (R : Position ≃ₗᵢ[ℝ] Position) :
    let D := cutoffSpiral f M q
    let F := fun τ => latticeBlockDensity b d η R D τ none
    let ρ := M.trace.re
    (∀ᵐ τ ∂latticeShiftMeasure b, ∃ Γ, feasible (F τ) Γ) ∧
      (∃ G : Position → ℝ, Integrable G (latticeShiftMeasure b) ∧ ∀ᵐ τ ∂latticeShiftMeasure b, energy (F τ) ≤ G τ) ∧
      (∫ τ, energy (F τ) ∂latticeShiftMeasure b) ≤
        windowMassCost H (2*ρ) q*(s.coefficient*(d/b)*(∫ x, f x))+
        windowFisherCost H (2*ρ)*(s.coefficient/(b*d)*(∫ x, f x)+s.coefficient*(d/b)*(∫ x, ‖g x‖^2)) := by
  intro D F ρ
  have hb : 0 < b := by linarith
  let : IsProbabilityMeasure (latticeShiftMeasure b) := latticeShiftMeasure_probability hb
  obtain ⟨v,hwm,hvm,hwv,hmass,hgrad⟩ := s.averages hd hsc R
  have unit (τ x : Position) : normalizedSkeleton η b d R τ x ∈ Icc 0 1 := by
    have h := latticeBlock_bounds hd hsc hs none (R x-τ)
    dsimp [normalizedSkeleton]
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  have hρ : (((2:ℝ) • M).trace).re = 2*ρ := by simp [ρ,Matrix.trace_smul,Complex.real_smul]
  have h := H.skeleton_windows_upper W hf fi g gf df _ v unit hwm hvm hwv
    (mul_nonneg s.nonneg (div_nonneg hd.le hb.le)) (div_nonneg s.nonneg (mul_nonneg hb.le hd.le))
    hmass hgrad (hM.smul (by norm_num : (0:ℝ) ≤ 2)) q
  simpa only [F,D,skeleton_field_eq,hρ] using h

private theorem interior_frame_integrable (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (O : TileOrientationLaw) (η : Mollifier) (I : Set Position) {M : SpinMatrix} (hM : M.PosSemidef)
    (q : Position) {a b d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    Integrable (fun u => ∫ z in I, energy (cutoffSpiral (centeredWindow η a d (O.frame u) z) M q) /
      regionVolume (tetrahedron b)) O.law := by
  let v := regionVolume (tetrahedron a)
  let V := regionVolume (tetrahedron b)
  have hv := (tetrahedron_volume_pos ha).ne'
  let E := tileEnergy energy η M a d
  have step (u : O.Frames) (z : Position) :
      energy (cutoffSpiral (centeredWindow η a d (O.frame u) z) M q) / V = (v/V)*E (O.frame u q) := by
    have h := centered_energy η a d (O.frame u) z M q
    change _ / v = E _ at h
    rw [← h]
    field_simp [show v ≠ 0 from hv]
  change Integrable (fun u => ∫ z in I, energy (cutoffSpiral (centeredWindow η a d (O.frame u) z) M q)/V) O.law
  simp_rw [step, setIntegral_const, smul_eq_mul,← mul_assoc]
  exact (O.average E (coulomb_continuous_tile H sob η ha hd hM) q).1.const_mul _

private theorem upper_from_fixed_shifts (H : FiniteEnergyInputs) (W : WindowSobolevRules)
    (sob : SobolevDifferenceQuotients) (O : TileOrientationLaw) (haar : CubeFrameInvariant O)
    (tensor : DisjointFockTensorization) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (S : SkeletonFisherAverages η) {f : Position → ℝ} (hf : ∀ x, f x ∈ Icc 0 1) (fi : Integrable f)
    (g : Position → Position) (gf : MemLp g 2) (df : ∀ i, WeakPartialOn univ i (fun x => √(f x)) (fun x => g x i))
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {ℓ δ t : ℝ} (hd : 0 < δ) (hsc : δ ≤ ℓ/2) (ht : t ∈ scaleInterval)
    (integrals : CoulombLatticeIntegrals O η f M q ℓ δ) (I : Set Position) (Bnd : ℝ)
    (rep : ∀ R : Position ≃ₗᵢ[ℝ] Position, ∀ z, ∃ Γ, feasible
      (cutoffSpiral (fun x => f x*centeredWindow η (t*(ℓ-δ)) (t*δ) R z x) M q) Γ)
    (centers : ∀ R : Position ≃ₗᵢ[ℝ] Position, (∫ z, energy (cutoffSpiral
      (fun x => f x*centeredWindow η (t*(ℓ-δ)) (t*δ) R z x) M q) / regionVolume (tetrahedron (t*ℓ))) ≤
      (∫ z in I, energy (cutoffSpiral (centeredWindow η (t*(ℓ-δ)) (t*δ) R z) M q) /
        regionVolume (tetrahedron (t*ℓ))) + Bnd) :
    let D := cutoffSpiral f M q
    let ρ := M.trace.re
    energy D ≤ upperInteriorEnergy O η I M q ℓ δ t + Bnd +
      (windowMassCost H (2*ρ) q*(S.coefficient*(δ/ℓ)*(∫ x, f x))+
        windowFisherCost H (2*ρ)*(S.coefficient/((t*ℓ)*(t*δ))*(∫ x, f x) +
          S.coefficient*(δ/ℓ)*(∫ x, ‖g x‖^2))) +
      latticeVariance O η (fun x => (D x).trace.re) ℓ δ t := by
  intro D ρ
  let b := t*ℓ
  let d := t*δ
  let μ := latticeShiftMeasure b
  let V := regionVolume (tetrahedron b)
  let e := energy D
  have ht' : 0 < t := by linarith [ht.1]
  have he : 0 < ℓ := by linarith
  have hb : 0 < b := mul_pos ht' he
  have hD : 0 < d := mul_pos ht' hd
  have hbd : d ≤ b/2 := by dsimp [b,d]; nlinarith only [mul_le_mul_of_nonneg_left hsc ht'.le]
  have hsize : b-d = t*(ℓ-δ) := by dsimp [b,d]; ring
  have hr : d/b = δ/ℓ := by dsimp [b,d]; field_simp [ht'.ne',he.ne']
  let tiles := fun (u : O.Frames) (τ : Position) => ∑' j : LatticeTile,
    energy (cutoffSpiral (fun x => f x*latticeWindow b d η j (O.frame u x-τ)) M q)
  let sk := fun (u : O.Frames) (τ : Position) => energy (latticeBlockDensity b d η (O.frame u) D τ none)
  let direct := fun u => ∫ τ, hartree (fun x =>
    (latticeTotalWindow b d η (O.frame u x-τ)-1)*(D x).trace.re) ∂μ
  let sc := windowMassCost H (2*ρ) q*(S.coefficient*(δ/ℓ)*(∫ x, f x))+
    windowFisherCost H (2*ρ)*(S.coefficient/(b*d)*(∫ x, f x)+S.coefficient*(δ/ℓ)*(∫ x, ‖g x‖^2))
  have fixed (u : O.Frames) : e ≤ (∫ τ, tiles u τ ∂μ)+sc+direct u := by
    let R := O.frame u
    have parts := skeleton_shift_bounds H W S hs hf fi g gf df hM q hD hbd R
    have repAll : ∀ᵐ τ ∂μ, ∀ p, ∃ Γ, feasible (latticeBlockDensity b d η R D τ p) Γ := by
      filter_upwards [parts.1] with τ hτ
      rintro (_ | p)
      · exact hτ
      · rw [show latticeBlockDensity b d η R D τ (some p) = _ from cell_field_eq η f M q b d R τ p]
        simp_rw [latticeWindow_centered η b d R τ p,hsize]
        apply rep
    have bounds := integrals.shifts t ht R
    have source := coulomb_upper_lattice_shifts tensor lsc hD hbd hs R D integrals.measurable
      integrals.integrable integrals.compact repAll bounds.1 integrals.direct
    have split (τ : Position) : latticeBlockEnergySum b d η R D τ = sk u τ+tiles u τ := by
      simp only [latticeBlockEnergySum,sk,tiles,D,R,cell_field_eq]
    have ti : Integrable (tiles u) μ := by
      have equiv : (fun τ => latticeBlockEnergySum b d η R D τ-sk u τ) = tiles u := by
        funext τ; rw [split]; ring
      rw [← equiv]
      exact bounds.1.sub bounds.2
    change e ≤ (∫ τ, latticeBlockEnergySum b d η R D τ ∂μ) + direct u at source
    simp_rw [split] at source
    rw [integral_add bounds.2 ti] at source
    have skBound : (∫ τ, sk u τ ∂μ) ≤ sc := by simpa only [sk,sc,hr,ρ,D,R,b,d] using parts.2.2
    linarith only [source,skBound]
  have ti : Integrable (fun u => ∫ τ, tiles u τ ∂μ) O.law := integrals.shiftsFrames t ht
  have di : Integrable direct O.law := integrals.directFrames t ht
  have tiC : Integrable (fun u => (∫ τ, tiles u τ ∂μ)+sc) O.law := ti.add (integrable_const sc)
  have h := integral_mono (integrable_const (μ := O.law) e)
    ((ti.add (integrable_const sc)).add di) fixed
  change (∫ _ : O.Frames, e ∂O.law) ≤ ∫ u, (∫ τ, tiles u τ ∂μ)+sc+direct u ∂O.law at h
  rw [integral_const,probReal_univ,one_smul,integral_add tiC di,
    integral_add ti (integrable_const sc),integral_const,probReal_univ,one_smul] at h
  have unfolded := coulomb_unfold_lattice_tiles O haar η hb d f M q
    (integrals.centers t ht) (integrals.centerFrames t ht)
  change (∫ u, ∫ τ, tiles u τ ∂μ ∂O.law) = _ at unfolded
  simp only [hsize] at unfolded
  rw [unfolded] at h
  let Iref := fun u => ∫ z in I,
    energy (cutoffSpiral (centeredWindow η (t*(ℓ-δ)) (t*δ) (O.frame u) z) M q) / V
  have Iint : Integrable Iref O.law := interior_frame_integrable H sob O η I hM q
    (mul_pos ht' (by linarith)) hD
  have cint : Integrable (fun u => ∫ z, energy (cutoffSpiral
      (fun x => f x*centeredWindow η (t*(ℓ-δ)) d (O.frame u) z x) M q)/V) O.law := by
    simp_rw [integral_div]
    simpa only [mul_sub,d] using (integrals.centerFrames t ht).div_const V
  have cmp := integral_mono cint (Iint.add (integrable_const Bnd))
    (fun u => centers (O.frame u))
  change _ ≤ ∫ u, Iref u+Bnd ∂O.law at cmp
  rw [integral_add Iint (integrable_const _),integral_const,probReal_univ,one_smul] at cmp
  change _ ≤ upperInteriorEnergy O η I M q ℓ δ t+Bnd at cmp
  change e ≤ upperInteriorEnergy O η I M q ℓ δ t+Bnd+sc+∫ u, direct u ∂O.law
  exact h.trans (add_le_add (add_le_add cmp (le_refl _)) (le_refl _))

private theorem physical_cost_sum {H : FiniteEnergyInputs} {ρ C c s K W X Y ℓ δ t : ℝ}
    (hr : 0 ≤ ρ) (hC : 0 ≤ C) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hK : C*(1+c+5*s) ≤ K) (hW : 0 ≤ W) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (he : 0 < ℓ) (hd : 0 < δ) (hsc : δ ≤ ℓ/2) (ht : t ∈ scaleInterval) (q : Position)
    (pu : windowMassCost H ρ q ≤ C*(ρ*rateGrowth ρ q))
    (p₂ : windowMassCost H (2*ρ) q ≤ C*(ρ*rateGrowth ρ q))
    (ku : windowFisherCost H ρ ≤ C*ρ) (k₂ : windowFisherCost H (2*ρ) ≤ C*ρ) :
    (windowMassCost H ρ q*X+windowFisherCost H ρ*(c/(ℓ*δ)*W+Y))+
    (windowMassCost H (2*ρ) q*(s*(δ/ℓ)*W)+
      windowFisherCost H (2*ρ)*(s/((t*ℓ)*(t*δ))*W+s*(δ/ℓ)*Y)) ≤
    K*(ρ*rateGrowth ρ q*(W*δ/ℓ+X)+ρ*(W/(ℓ*δ)+Y)) := by
  let D := ρ*rateGrowth ρ q
  have hD : 0 ≤ D := mul_nonneg hr (add_nonneg (add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)) (sq_nonneg _))
  have e := (div_le_one he).mpr (show δ ≤ ℓ by linarith)
  have ht₀ : 0 < t := by linarith [ht.1]
  have ht₂ : 1 ≤ 4*t^2 := by nlinarith only [sq_nonneg (t-1/2), ht.1]
  have rat : s/((t*ℓ)*(t*δ)) ≤ 4*s/(ℓ*δ) := by
    apply (div_le_div_iff₀ (mul_pos (mul_pos ht₀ he) (mul_pos ht₀ hd)) (mul_pos he hd)).2
    nlinarith only [mul_le_mul_of_nonneg_right ht₂ (mul_nonneg hs (mul_nonneg he.le hd.le))]
  have sc : s*(δ/ℓ) ≤ s := mul_le_of_le_one_right hs e
  have h₁ : C ≤ K := by nlinarith only [hK,mul_nonneg hC hc,mul_nonneg hC hs]
  have h₂ : C*s ≤ K := by nlinarith only [hK,hC,mul_nonneg hC hc,mul_nonneg hC hs]
  have h₃ : C*(c+4*s) ≤ K := by nlinarith only [hK,hC,mul_nonneg hC hs]
  have h₄ : C*(1+s) ≤ K := by nlinarith only [hK,mul_nonneg hC hc,mul_nonneg hC hs]
  have upM := mul_le_mul_of_nonneg_right pu hX
  have skM := mul_le_mul_of_nonneg_right p₂ (show 0 ≤ s*(δ/ℓ)*W by positivity)
  have upG := mul_le_mul_of_nonneg_right ku (show 0 ≤ c/(ℓ*δ)*W+Y by positivity)
  have skG := mul_le_mul_of_nonneg_right k₂ (show 0 ≤ s/((t*ℓ)*(t*δ))*W+s*(δ/ℓ)*Y by positivity)
  have scG := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right rat hW)
    (mul_le_mul_of_nonneg_right sc hY)) (mul_nonneg hC hr)
  have a₁ := mul_le_mul_of_nonneg_right h₁ (mul_nonneg hD hX)
  have a₂ := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ D*(W*δ/ℓ) by positivity)
  have a₃ := mul_le_mul_of_nonneg_right h₃ (show 0 ≤ ρ*(W/(ℓ*δ)) by positivity)
  have a₄ := mul_le_mul_of_nonneg_right h₄ (mul_nonneg hr hY)
  dsimp only [D] at *
  ring_nf at upM skM upG skG scG a₁ a₂ a₃ a₄ ⊢
  linarith only [upM,skM,upG,skG,scG,a₁,a₂,a₃,a₄]

private theorem state_within_energy {D : Position → SpinMatrix} (rep : ∃ Γ, feasible D Γ) {ε : ℝ} (he : 0 < ε) :
    ∃ Γ, feasible D Γ ∧ localStateEnergy Γ D ≤ energy D + ε := by
  obtain ⟨s,hs⟩ := rep
  let S : Set ℝ := {v | ∃ Γ : MixedState, feasible D Γ ∧ v = Γ.kinetic+Γ.interaction}
  obtain ⟨v,⟨Γ,hΓ,rfl⟩,h⟩ := exists_lt_of_csInf_lt (s := S) ⟨_,s,hs,rfl⟩
    (show sInf S < levyLieb D+ε from lt_add_of_pos_right _ he)
  refine ⟨Γ,hΓ,?_⟩
  dsimp only [energy,localStateEnergy]
  linarith

/-- Both finite-domain upper estimates are obtained from the actual
translated Fock products. The electrostatic coefficient is the only change
between the cubic and quadratic constructions. -/
def CoulombUpperLocalization.of_lattice {η : Mollifier} (H : FiniteEnergyInputs)
    (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients) (diff : SobolevDifferenceBounds)
    (O : TileOrientationLaw) (haar : CubeFrameInvariant O) (tensor : DisjointFockTensorization)
    (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (S : SkeletonFisherAverages η)
    {p : CoulombTilingCost} {A : ℝ} (hA : 0 ≤ A) (variance : CoulombVarianceBound O η p A)
    (regular : ∀ {Ω : Set Position}, IsOpen Ω → Bornology.IsBounded Ω → 0 < regionVolume Ω →
      ∀ (χ : Mollifier) {d : ℝ}, 0 < d → ∀ {M : SpinMatrix}, M.PosSemidef → ∀ q : Position,
      ∀ {ℓ δ : ℝ}, 0 < δ → δ ≤ ℓ/2 → CoulombLatticeIntegrals O η (smoothedIndicator Ω χ d) M q ℓ δ) :
    CoulombUpperLocalization η p := by
  classical
  let c := (H.all_centers_upper W sob diff η).choose
  have spec := (H.all_centers_upper W sob diff η).choose_spec
  have hc : 0 ≤ c := spec.1
  let C := H.window_constants.choose
  have Cspec := H.window_constants.choose_spec
  have hC : 0 ≤ C := Cspec.1
  let K := max (C*(1+c+5*S.coefficient)) A
  have hK : C*(1+c+5*S.coefficient) ≤ K := le_max_left _ _
  have hAK : A ≤ K := le_max_right _ _
  refine ⟨O,K,hA.trans hAK,?_⟩
  intro χ
  obtain ⟨a,ha,total⟩ := spec.2 χ
  refine ⟨a,ha,?_⟩
  intro Ω hop hbd hv d hd g dg ℓ δ hδ hsc M hM q α haα hα ε hε V ρ F B
  let f := smoothedIndicator Ω χ d
  let I := Ω \ B
  have he : 0 < ℓ := by linarith
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have reg := regular hop hbd hv χ hd hM q hδ hsc
  have mass : (∫ x, f x) = V := by
    have hχ : Integrable (Ω.indicator (fun _ => (1:ℝ))) :=
      (integrable_indicator_iff hop.measurableSet).2 (integrableOn_const hbd.measure_lt_top.ne)
    change (∫ x, smoothedIndicator Ω χ d x) = regionVolume Ω
    rw [smoothedIndicator,integral_convolution _ hχ (χ.scaled_integrable hd),
      χ.scaled_mass hd,integral_indicator hop.measurableSet]
    simp [regionVolume]
  have fi := Integrable.of_integral_ne_zero (mass.trans_ne hv.ne')
  have hf := smoothedIndicator_bounds Ω χ hd
  have gf := smoothedIndicator_gradient_memLp sob hop.measurableSet hbd.measure_lt_top.ne χ hd g dg
  let energyCost := K*(ρ*rateGrowth ρ q*(V*δ/ℓ+regionVolume B)+ρ*(V/(ℓ*δ)+∫ x, ‖g x‖^2))
  have repF : ∃ Γ, feasible F Γ := by
    obtain ⟨Γ,hΓ⟩ := H.representable_cutoff (fun x => (hf x).1) fi g dg gf hM
    let s := cutoffRotation f M q ⟨Γ,hΓ⟩
    exact ⟨s.val,s.property⟩
  obtain ⟨c',_,border⟩ := H.boundary_tetrahedron_upper W sob diff η
  have source (t : ℝ) (ht : t ∈ scaleInterval) :
      energy F ≤ upperInteriorEnergy O η I M q ℓ δ t + energyCost+
        latticeVariance O η (fun x => (F x).trace.re) ℓ δ t := by
    have rep (R : Position ≃ₗᵢ[ℝ] Position) (z : Position) := (border hδ hsc ht hf fi g gf dg
      (B := ∅) (by simp) R hM q).1 z
    let L := windowMassCost H ρ q*regionVolume B+
      windowFisherCost H ρ*(c/(ℓ*δ)*V+∫ x, ‖g x‖^2)
    have cut (R : Position ≃ₗᵢ[ℝ] Position) := total hop hbd hv hd g dg hδ hsc ht R hM q
      (by simpa only [mul_sub] using (reg.centers t ht R).div_const (regionVolume (tetrahedron (t*ℓ))))
    have q₀ := upper_from_fixed_shifts H W sob O haar tensor lsc hs S hf fi g gf dg hM q
      hδ hsc ht reg I L rep cut
    rw [mass] at q₀
    obtain ⟨p₁,p₂,k₁,k₂⟩ := Cspec.2 hr q
    have Ypos : 0 ≤ ∫ x, ‖g x‖^2 := integral_nonneg fun x => sq_nonneg _
    have cost := physical_cost_sum hr hC hc S.nonneg hK hv.le (show 0 ≤ regionVolume B from ENNReal.toReal_nonneg)
      Ypos he hδ hsc ht q p₁ p₂ k₁ k₂
    change energy F ≤ _ at q₀
    dsimp only [energyCost,L] at *
    linarith only [q₀,cost]
  let cI := regionVolume I*(1-δ/ℓ)^3
  have tint := coulomb_tileDilationIntegrable (levyLiebBorel_of_lowerSemicontinuous lsc) η H sob diff 0 M hM q
    (ℓ-δ) δ (by linarith) hδ (by linarith)
  have ie : IntegrableOn (fun t => upperInteriorEnergy O η I M q ℓ δ t*scaleWeight t) scaleInterval := by
    refine (tint.const_mul cI).congr ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
    have htp : 0 < t := by linarith [ht.1]
    rw [upperInteriorEnergy_eq O H sob I hM q hδ (by linarith) htp]
    ring
  have global := scale_average_bound haα hα ie reg.directScales source
  have hvb := variance hop hbd χ hd hr hδ hsc α haα hα
  have eqCharge : (fun x => (F x).trace.re) = fun x => f x*ρ := by
    funext x
    simp only [F,f,cutoffSpiral,Matrix.trace_smul,smul_eq_mul,trace_rotate,Complex.re_ofReal_mul,ρ]
  change scaleAverageAt α (latticeVariance O η (fun x => f x*ρ) ℓ δ) ≤ _ at hvb
  rw [← eqCharge] at hvb
  have hp0 := p.cost_nonneg he hδ
  have direct_nonneg : 0 ≤ ∫ x, (F x).trace.re^2 := integral_nonneg fun x => sq_nonneg _
  have coef := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAK hp0) direct_nonneg)
    (Real.log_nonneg ((one_le_inv₀ haα).mpr (by linarith)))
  obtain ⟨Γ,hΓ,hstate⟩ := state_within_energy repF hε
  refine ⟨Γ,hΓ,?_⟩
  change localStateEnergy Γ F ≤ scaleAverageAt α (upperInteriorEnergy O η I M q ℓ δ) +
    energyCost + (K*p.cost ℓ δ)*(∫ x, (F x).trace.re^2)*Real.log α⁻¹+ε
  linarith only [global,hvb,coef,hstate]

end TSGA.ManyBody
