import TSGA.IslandMaskCovariance
import TSGA.IslandChargeDomain
import TSGA.IslandOverlapScales

/-! # Electrostatic fluctuations of the normalized Poisson trial -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set TSGA.Islands

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {intensity : Measure Z} [SFinite intensity] {P : PoissonIslandProcess μ intensity} {v : ℝ}

/-- Only spatial and intensity bounds on individual marks and their diameter
enter the overlap argument. -/
structure IslandOverlapGeometry (H : IslandProfiles P v) (massFull massShell hitShell diam : ℝ) : Prop where
  layer : IslandMarkBound intensity (fun i x => H.layer x i) massFull v
  core : IslandMarkBound intensity (fun i x => H.inner x i) massFull v
  shell : IslandMarkBound intensity (fun i x => H.boundaryMark x i) massShell hitShell
  diameter : ∀ x y, diam ≤ ‖y-x‖ → ∀ i, H.outer x i*H.outer y i = 0

private theorem schur_add {K J : PairSpace → ℝ} {a b : ℝ} (h : IslandSchurKernel K a)
    (j : IslandSchurKernel J b) (t : ℝ) (ht : 0 ≤ t) :
    IslandSchurKernel (fun z => K z+t*J z) (a+t*b) := by
  refine ⟨h.measurable.add (measurable_const.mul j.measurable),
    fun z => add_nonneg (h.nonneg z) (mul_nonneg ht (j.nonneg z)),?_,?_⟩
  · intro x y; rw [h.symm x y,j.symm x y]
  · intro x
    refine ⟨(h.rows x).1.add ((j.rows x).1.const_mul t),?_⟩
    rw [integral_add (h.rows x).1 ((j.rows x).1.const_mul t),integral_const_mul]
    exact add_le_add (h.rows x).2 (mul_le_mul_of_nonneg_left (j.rows x).2 ht)

private theorem expected_of_cov {K : PairSpace → ℝ} {M : ℝ} (H : IslandSchurKernel K M)
    (F : Ω → Position → ℝ) (ρ : Position → ℝ) (c : ℝ)
    (hρ : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (hi : Integrable (fun x => ρ x^2))
    (joint : JointDirectIntegrable μ (fun ω x => c*F ω x*ρ x))
    (cov : ∀ x y, (∫ ω, F ω x*F ω y ∂μ)/‖x-y‖ ≤ K (x,y)) :
    (∫ ω, hartree (fun x => c*F ω x*ρ x) ∂μ) ≤ c^2 * M * (∫ x, ρ x^2)/2 := by
  have hs := H.charge_bound hρ hp hi
  rw [expect_hartree_as_pair joint]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∫ z : PairSpace, c^2*(ρ z.1*ρ z.2*K z) ∂pairVolume := by
      apply integral_mono joint.integral_prod_right (hs.1.const_mul _)
      intro z
      have he (ω : Ω) : directKernel (fun x => c*F ω x*ρ x) (fun x => c*F ω x*ρ x) z =
          (c^2*(ρ z.1*ρ z.2))*(F ω z.1*F ω z.2/‖z.1-z.2‖) := by unfold directKernel; ring
      simp_rw [he]
      rw [integral_const_mul,integral_div]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (cov _ _) (mul_nonneg (sq_nonneg _) (mul_nonneg (hp _) (hp _)))
    _ ≤ _ := by rw [integral_const_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _)

/-- The actual charge of the trial centered by its prescribed mean. -/
def IslandMasks.centered (m : IslandMasks μ v) (B D : Density) (ω : Ω) (x : Position) :=
  (m.outerCharge B ω x + m.innerCharge B D ω x) - (B.charge x + D.charge x)

namespace IslandProfiles
variable (H : IslandProfiles P v)

/-- Raw Schur estimate. The full-mark and thin-shell masses appear with
power 2/3, and the independent-pair contribution carries a squared hit rate. -/
theorem fluctuation_bound {B D : Density} {massFull massShell hitShell diam : ℝ}
    (G : IslandOverlapGeometry H massFull massShell hitShell diam) (mf : 0 < massFull)
    (ms : 0 < massShell) (hr : 0 < diam) (hv : v ≤ 1)
    (M : H.masks.MeasurableFields) (dom : IslandChargeDomain B D)
    (hB : Integrable (fun x => B.charge x^2)) (hD : Integrable (fun x => D.charge x^2))
    (positive : ∀ u, Integrable (directKernel u u) pairVolume → 0 ≤ hartree u) :
    (∫ ω, hartree (H.masks.centered B D ω) ∂μ) ≤ 3/2 *
      (((H.masks.c₁-1)^2 * (islandCoulombConstant * massFull^(2/3:ℝ) * v) +
        (islandCoulombConstant * massShell^(2/3:ℝ) * hitShell +
          Real.exp 1*(v-H.layerIntensity)^2*(islandCoulombConstant*diam^2))) * (∫ x, B.charge x^2) +
        H.masks.c₂^2 * (islandCoulombConstant * massFull^(2/3:ℝ) * v) * (∫ x, D.charge x^2)) := by
  let m := H.masks
  obtain ⟨J₁,J₂,J₃,tri⟩ := m.fluctuation_domains M dom
  have a := expected_of_cov (G.layer.schur mf) (fun ω x => m.first ω x-m.meanFirst) B.charge (m.c₁-1)
    dom.background B.charge_nonneg hB J₁
    (fun x y => div_le_div_of_nonneg_right (H.firstCovariance x y) (norm_nonneg _))
  have b := expected_of_cov (G.core.schur mf) (fun ω x => m.core ω x-m.meanCore) D.charge m.c₂
    dom.added D.charge_nonneg hD J₃
    (fun x y => div_le_div_of_nonneg_right (H.coreCovariance x y) (norm_nonneg _))
  have Js : JointDirectIntegrable μ (fun ω x => 1*H.shellField ω x*B.charge x) := by
    simp only [one_mul]
    exact J₂
  have c := expected_of_cov (schur_add (G.shell.schur ms) (islandNearSchur hr) _
    (mul_nonneg (Real.exp_pos 1).le (sq_nonneg _))) H.shellField B.charge 1 dom.background
    B.charge_nonneg hB Js (H.shellCovarianceBound hv G.diameter)
  simp only [one_mul,one_pow] at c
  let A := fun ω => hartree (m.firstFluct B ω)
  let S := fun ω => hartree (m.shellFluct B ω)
  let C := fun ω => hartree (m.coreFluct D ω)
  change (∫ ω, A ω ∂μ) ≤ _ at a
  change (∫ ω, C ω ∂μ) ≤ _ at b
  change (∫ ω, S ω ∂μ) ≤ _ at c
  have ia : Integrable A μ := integrable_hartree_of_joint J₁
  have ib : Integrable S μ := integrable_hartree_of_joint J₂
  have ic : Integrable C μ := integrable_hartree_of_joint J₃
  obtain ⟨out,ins,det,_,_,_⟩ := m.controls M dom
  have ctr := (out.add ins).sub det
  have cent : JointDirectIntegrable μ (m.centered B D) :=
    ctr.joint ctr (fun x => add_nonneg (B.charge_nonneg x) (D.charge_nonneg x)) dom.direct
  have hsplit : (∫ ω, hartree (m.centered B D ω) ∂μ) ≤ 3*((∫ ω, A ω ∂μ)+(∫ ω, S ω ∂μ)+(∫ ω, C ω ∂μ)) := by
    calc
      _ ≤ ∫ ω, 3 * (A ω + S ω + C ω) ∂μ := by
        apply integral_mono_ae (integrable_hartree_of_joint cent) (((ia.add ib).add ic).const_mul 3)
        filter_upwards [tri] with ω hw
        have eqn : m.centered B D ω = m.firstFluct B ω + m.shellFluct B ω + m.coreFluct D ω :=
          funext (m.fluctuation_split B D ω)
        rw [eqn]
        exact hartree_three_le hw positive
      _ = _ := by
        have iab : Integrable (fun ω => A ω + S ω) μ := ia.add ib
        rw [integral_const_mul, integral_add iab ic, integral_add ia ib]
  apply hsplit.trans
  dsimp only [m] at *
  linarith only [a,b,c]

/-- Appendix C fluctuation estimate at the chosen width. The normalization
bounds and one-mark geometry can be checked before the random trial is built. -/
theorem fluctuation_scaled {B D : Density} (S : MatrixGradient) {ε r δ L denominator : ℝ}
    (G : IslandOverlapGeometry H ((L*r)^3) (L^3*r^2*δ) (L*v*δ/r) (L*r))
    (hL : 1 ≤ L) (he : 0 < ε) (he' : ε ≤ 1) (hr : 1 ≤ r) (hmax : ε*r^2 ≤ 1)
    (hv : v = ε/2) (hden : 1 ≤ denominator) (hw : δ = r^(-(1/5:ℝ))/denominator)
    (h₁ : |H.masks.c₁-1| ≤ L*δ/r) (h₂ : |H.masks.c₂| ≤ L/v)
    (M : H.masks.MeasurableFields) (dom : IslandChargeDomain B D)
    (mass : Integrable B.charge) (hB : Integrable (fun x => B.charge x^2))
    (hD : Integrable (fun x => D.charge x^2))
    (positive : ∀ u, Integrable (directKernel u u) pairVolume → 0 ≤ hartree u) :
    (∫ ω, hartree (H.masks.centered B D ω) ∂μ) ≤
      12*overlapScale L*ε*islandBackground B S + 6*overlapScale L*(r^2/ε)*(∫ x, D.charge x^2) := by
  have w := choose_island_width he he' hr hmax hden
  rw [← hw] at w
  obtain ⟨_,_,hδ,_,_,ws⟩ := w
  have hr' := zero_lt_one.trans_le hr
  have hL' := zero_lt_one.trans_le hL
  have hv' : 0 < v := by linarith only [he,hv]
  have hv₁ : v ≤ 1 := by linarith only [he',hv]
  have bnd := H.fluctuation_bound G (by positivity) (by positivity) (by positivity) hv₁ M dom hB hD positive
  have gap₀ : 0 ≤ v-H.layerIntensity := (H.boundaryMark_hits 0).2 ▸
      (integral_nonneg (fun i => (H.boundaryMark_range 0 i).1))
  have gap : v-H.layerIntensity ≤ L*v*δ/r := (H.boundaryMark_hits 0).2 ▸ (G.shell.hits 0).2
  obtain ⟨hbg,hadd⟩ := island_overlap_coefficients hL hv' hv₁ hr' hδ gap₀ gap h₁ h₂
  let b := ∫ x, B.charge x^2
  let d := ∫ x, D.charge x^2
  have hb : 0 ≤ b := integral_nonneg fun x => sq_nonneg _
  have hd : 0 ≤ d := integral_nonneg fun x => sq_nonneg _
  have g : b ≤ islandBackground B S := by
    unfold islandBackground
    rw [integral_add mass hB]
    have m₀ : 0 ≤ ∫ x, B.charge x := integral_nonneg B.charge_nonneg
    have k₀ : 0 ≤ sqrtKinetic S := integral_nonneg fun _ => sq_nonneg _
    dsimp [b]; linarith only [m₀,k₀]
  have small : δ^2+r^(1/3:ℝ)*δ^(5/3:ℝ) ≤ 4 := by
    linarith only [ws,show 0 ≤ δ^3/r by positivity,show 0 ≤ (ε/2)*r^2 by positivity]
  have hC := overlapScale_nonneg L
  have scale : overlapScale L*v*(δ^2+r^(1/3:ℝ)*δ^(5/3:ℝ))*b ≤ overlapScale L*v*4*b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left small (mul_nonneg hC hv'.le)) hb
  have rcoeff : r^2/v = 2*(r^2/ε) := by rw [hv]; field_simp
  apply bnd.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hbg hb)
    (mul_le_mul_of_nonneg_right hadd hd)) (by norm_num : (0:ℝ) ≤ 3/2)).trans
  have b₁ := mul_le_mul_of_nonneg_left g (mul_nonneg hC he.le)
  have b₀ : 0 ≤ overlapScale L*ε*b := by positivity
  have d₀ : 0 ≤ overlapScale L*(r^2/ε)*d := by positivity
  rw [rcoeff,hv]
  rw [hv] at scale
  linarith only [scale,b₁,b₀,d₀]

end IslandProfiles
end TSGA.ManyBody
