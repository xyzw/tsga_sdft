import TSGA.PhaseLocalization
import TSGA.LocalizationAssembly
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The normalized phase cost of a TSGA comparison tile

On small-oscillation balls the two wavevector errors are the linear and
quadratic Hölder products before Young's inequality. Their root-gradient
factor is multiplied by the minimum squared wavevector. Large-oscillation
balls use the truncated kinetic-energy estimate.
-/

noncomputable section

namespace TSGA.PhaseLocalization

open MeasureTheory Set TSGA.Localization
open scoped ComplexOrder

def tileConstant (p A : ℝ) : ℝ := 3 * A + A * (2 : ℝ)^p * (1 + (2 : ℝ)^p * A^2)

theorem tileConstant_nonneg (p : ℝ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ tileConstant p A := by
  unfold tileConstant
  positivity

def bulkAverage (D : Density) (φ : Phase) (R : ℝ) (c : Position) : ℝ :=
  ballAverage R (fun x => D.charge x + D.charge x^2 + D.charge x*‖φ.grad x‖^2) c

def curvature (D : Density) (φ : Phase) (p : ℝ) (x : Position) : ℝ :=
  D.charge x * φ.hessianNorm x ^ p

/-- The linear and quadratic mixed powers after Hölder and Morrey, with
`ℓ = 1/δ`. The inverse small-parameter power has been factored so that the
two Young estimates have the same pair of pure terms. -/
def wavevectorProducts (p bulk error : ℝ) : ℝ :=
  bulk ^ (1 - 1 / p) * error ^ (1 / p) + bulk ^ (1 - 2 / p) * error ^ (2 / p)

/-- The unsplit wavevector terms. Morrey contributes δ^(−p) in both terms.
The quadratic comparison carries the additional prefactor 1/δ. -/
def morreyProducts (p δ bulk error : ℝ) : ℝ :=
  bulk ^ (1 - 1/p) * (δ ^ (-p) * error) ^ (1/p) +
  bulk ^ (1 - 2/p) * (δ ^ (-p) * error) ^ (2/p) / δ

theorem morreyProducts_eq {p δ B H : ℝ} (hp : 0 < p) (hδ : 0 < δ)
    (hB : 0 ≤ B) (hH : 0 ≤ H) :
    morreyProducts p δ B H = wavevectorProducts p (δ*B) (H/δ^(2*p-1)) := by
  have scaled (u : ℝ) : (δ*B)^(1-u) * (H/δ^(2*p-1))^u =
      δ^(1 - 2*p*u) * (B^(1-u) * H^u) := by
    rw [Real.mul_rpow hδ.le hB, Real.div_rpow hH (Real.rpow_nonneg hδ.le _),
      ← Real.rpow_mul hδ.le]
    have he : 1 - 2*p*u = (1-u) - (2*p-1)*u := by ring
    rw [he, Real.rpow_sub hδ (1-u) ((2*p-1)*u)]
    ring
  have raw (u : ℝ) : (δ^(-p) * H)^u = δ^((-p)*u) * H^u := by
    rw [Real.mul_rpow (Real.rpow_nonneg hδ.le _) hH, ← Real.rpow_mul hδ.le]
  have h₁ : -p*(1/p) = 1 - 2*p*(1/p) := by field_simp; ring
  have h₂ : 1-2*p*(2/p) = -p*(2/p)-1 := by field_simp; ring
  rw [morreyProducts, wavevectorProducts, scaled, scaled, raw, raw, h₁, h₂, Real.rpow_sub hδ ((-p)*(2/p)) 1,
    Real.rpow_one]
  ring

private theorem holder_cost {p B H : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    wavevectorProducts p B H ≤ 2 * (B+H) := by
  have hp₀ : 0 < p := by linarith
  have young {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
      B^(1-u) * H^u ≤ B+H := by
    have hy := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hu') hu hB hH
      (show 1-u+u = 1 by ring)
    exact hy.trans (add_le_add (mul_le_of_le_one_left hB (by linarith))
      (mul_le_of_le_one_left hH hu'))
  have h1 := young (u := 1/p) (by positivity) ((div_le_one hp₀).2 (by linarith))
  have h2 := young (u := 2/p) (by positivity) ((div_le_one hp₀).2 hp)
  unfold wavevectorProducts
  linarith

/-- Finite phase estimates on the comparison ball at one center. In the small
case Hölder and local comparison give the mixed products; an unweighted
Morrey integral is needed only at a strictly positive squared minimum `m`.
In the large case the input is the finite a priori kinetic cost. -/
inductive TileInput (D : Density) (φ : Phase) (G : MatrixGradient) (p δ A R : ℝ)
    (c : Position) (X : ℝ) : Prop
  | small (m : ℝ) (nonneg : 0 ≤ m)
      (minimum : ∀ x ∈ Metric.ball c R, m ≤ ‖φ.grad x‖ ^ 2)
      (regular : m = 0 ∨ IntegrableOn (rootPower G p) (Metric.ball c R))
      (comparison : X ≤ A * (δ * bulkAverage D φ R c +
        morreyProducts p δ (bulkAverage D φ R c)
          (ballAverage R (curvature D φ p) c + m * ballAverage R (rootPower G p) c))) : TileInput D φ G p δ A R c X
  | large (osc : LargeOscillationData (Metric.closedBall c R) D φ G p δ A)
      (comparison : X ≤ A * ballAverage R (fun x => D.charge x * ‖φ.grad x‖ ^ 2) c) :
      TileInput D φ G p δ A R c X

private theorem closedBall_integral (c : Position) (R : ℝ) (f : Position → ℝ) :
    (∫ x in Metric.closedBall c R, f x) = ballIntegral R f c := by
  apply setIntegral_congr_set
  apply ae_eq_set.mpr
  constructor
  · rw [Metric.closedBall_sdiff_ball]
    exact Measure.addHaar_sphere volume c R
  · rw [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty]

private theorem ball_nonneg {f : Position → ℝ} (hf : ∀ x, 0 ≤ f x) (R : ℝ) (c : Position) :
    0 ≤ ballAverage R f c :=
  div_nonneg (integral_nonneg hf) ENNReal.toReal_nonneg

/-- Normalize both oscillation regimes into the phase error used in the global
assembly of Theorem 3.3. The constant depends only on `p` and the finite
comparison constant `A`. -/
theorem TileInput.bound {D : Density} {φ : Phase} {G : MatrixGradient} {p δ A R : ℝ}
    {c : Position} {X : ℝ} (h : TileInput D φ G p δ A R c X)
    (hp : 3 < p) (hδ : 0 < δ) (hδle : δ ≤ 1) (hA : 1 ≤ A) (hR : 0 < R)
    (hρ : Integrable D.charge)
    (hbase : Integrable (fun x => D.charge x + D.charge x^2 + D.charge x*‖φ.grad x‖^2))
    (hφ : PhaseAdmissible D p φ G) :
    X ≤ tileConstant p A *
      (δ * ballAverage R (fun x => D.charge x + D.charge x^2 + D.charge x*‖φ.grad x‖^2) c +
       ballAverage R (fun x => D.charge x * φ.hessianNorm x ^ p + weightedRoot φ G p x) c /
         δ ^ (2 * p - 1)) := by
  let B := δ * bulkAverage D φ R c
  let U := ballAverage R (weightedRoot φ G p) c
  let H := ballAverage R (curvature D φ p) c
  let den := δ ^ (2*p-1)
  let J := (H + U) / den
  let T := (2 : ℝ) ^ p
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hA₀ : 0 ≤ A := by linarith
  have hd : 0 < den := Real.rpow_pos_of_pos hδ _
  have hU : 0 ≤ U := ball_nonneg (weightedRoot_nonneg φ G p) R c
  have hH : 0 ≤ H := ball_nonneg (fun x =>
    mul_nonneg (D.charge_nonneg x) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)) R c
  have hb₀ : 0 ≤ bulkAverage D φ R c := ball_nonneg (fun x => by
    have := D.charge_nonneg x
    positivity) R c
  have hB : 0 ≤ B := mul_nonneg hδ.le hb₀
  have hJ : 0 ≤ J := div_nonneg (add_nonneg hH hU) hd.le
  have hsum : 0 ≤ B+J := add_nonneg hB hJ
  change X ≤ tileConstant p A *
    (B + ballAverage R (fun x => curvature D φ p x + weightedRoot φ G p x) c / den)
  rw [ballAverage_add R (f := curvature D φ p) (g := weightedRoot φ G p) hφ.curvature
    (integrable_weightedRoot hφ)]
  change X ≤ tileConstant p A * (B+J)
  have h₃ : 3*A ≤ tileConstant p A := le_add_of_nonneg_right (by positivity)
  have hL : A*T*(1+T*A^2) ≤ tileConstant p A := le_add_of_nonneg_left (by positivity)
  cases h with
  | small m hm hmin hregular hcomp =>
    let U₀ := m * ballAverage R (rootPower G p) c
    have hU₀ : 0 ≤ U₀ := mul_nonneg hm (ball_nonneg (rootPower_nonneg G p) R c)
    have hpush : U₀ ≤ U := by
      rcases hregular with rfl | hi
      · simpa [U₀] using hU
      · have hh := minimum_mul_rootPower_le hφ Metric.isOpen_ball.measurableSet hmin hi
        simpa only [U₀, U, ballAverage, ballIntegral, mul_div_assoc] using
          div_le_div_of_nonneg_right hh (ballVolume_pos hR).le
    let J₀ := (H+U₀)/den
    have hJ₀ : 0 ≤ J₀ := div_nonneg (add_nonneg hH hU₀) hd.le
    have hJJ : J₀ ≤ J := div_le_div_of_nonneg_right (add_le_add (le_refl H) hpush) hd.le
    have hy := holder_cost (by linarith : 2 ≤ p) hB hJ₀
    calc
      X ≤ A*(B+wavevectorProducts p B J₀) := by
        rw [morreyProducts_eq (by linarith : 0 < p) hδ hb₀ (add_nonneg hH hU₀)] at hcomp
        exact hcomp
      _ ≤ A*(3*(B+J)) := mul_le_mul_of_nonneg_left (by linarith) hA₀
      _ = (3*A)*(B+J) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h₃ hsum
  | large osc hcomp =>
    have hh := largeOscillation_kinetic (isCompact_closedBall c R) (by linarith : 1 ≤ p)
      hδ hδle hA hρ hφ osc
    simp only [closedBall_integral] at hh
    have hn := div_le_div_of_nonneg_right hh (ballVolume_pos hR).le
    have heq : (fun x => D.charge x * φ.hessianNorm x ^ p) = curvature D φ p := rfl
    rw [heq] at hn
    have hn' : ballAverage R (fun x => D.charge x * ‖φ.grad x‖ ^ 2) c ≤
        T*(δ*ballAverage R D.charge c + T*A^2*J) := by
      apply hn.trans_eq
      dsimp only [T, J, U, H, den, ballAverage]
      ring
    have hcharge : δ * ballAverage R D.charge c ≤ B := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      apply ballAverage_mono R hρ hbase
      exact ae_of_all _ (fun x => le_add_of_nonneg_right
        (sq_nonneg (D.charge x)) |>.trans (le_add_of_nonneg_right (mul_nonneg (D.charge_nonneg x)
          (sq_nonneg ‖φ.grad x‖))))
    calc
      X ≤ _ := hcomp
      _ ≤ A*(T*(δ*ballAverage R D.charge c + T*A^2*J)) := mul_le_mul_of_nonneg_left hn' hA₀
      _ ≤ A*(T*((1+T*A^2)*(B+J))) := by
        apply mul_le_mul_of_nonneg_left _ hA₀
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith [mul_nonneg (mul_nonneg hT (sq_nonneg A)) hB]
      _ = (A*T*(1+T*A^2))*(B+J) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hL hsum

/-- A comparison ball may use the Sobolev representative of the density when
evaluating a pointwise maximum or a Morrey bound. Its matrix agrees almost
everywhere with the density used in the energy inequality. -/
def RepresentativeTileInput (D : Density) (φ : Phase) (G : MatrixGradient) (p δ A R : ℝ)
    (c : Position) (X : ℝ) : Prop :=
  ∃ D' : Density, D'.matrix =ᵐ[volume] D.matrix ∧ TileInput D' φ G p δ A R c X

theorem TileInput.toRepresentative {D : Density} {φ : Phase} {G : MatrixGradient} {p δ A R : ℝ}
    {c : Position} {X : ℝ} (h : TileInput D φ G p δ A R c X) :
    RepresentativeTileInput D φ G p δ A R c X :=
  ⟨D, Filter.EventuallyEq.rfl, h⟩

private theorem rootRegular_congr {U : Set Position} {D D' : Density} {p : ℝ} {G : MatrixGradient}
    (heq : D.matrix =ᵐ[volume] D'.matrix) (h : RootRegularOn U D p G) : RootRegularOn U D' p G := by
  have cfc_eq {M N : SpinMatrix} (e : M = N) (hM : M.PosSemidef) (hN : N.PosSemidef) :
      hM.isHermitian.cfc (fun t => t ^ (1/p)) = hN.isHermitian.cfc (fun t => t ^ (1/p)) := by
    subst N
    rfl
  have hpow : D.power (1/p) =ᵐ[volume] D'.power (1/p) :=
    heq.mono fun x hx => cfc_eq hx (D.positive x) (D'.positive x)
  intro x hx
  obtain ⟨r, hr, hball, hgrad, hLp, hG⟩ := h x hx
  let B := Metric.ball x r
  have hentry (j k : Fin 2) : (fun y => D.power (1/p) y j k) =ᵐ[volume.restrict B]
      (fun y => D'.power (1/p) y j k) :=
    ae_restrict_of_ae (hpow.mono fun y hy => congrArg (fun M : SpinMatrix => M j k) hy)
  refine ⟨r, hr, hball, ?_, fun j k => (memLp_congr_ae (hentry j k)).mp (hLp j k), hG⟩
  intro i j k
  obtain ⟨hi, hg, hw⟩ := hgrad i j k
  refine ⟨LocallyIntegrableOn.congr (hentry j k) hi, hg, ?_⟩
  intro ψ hψ hc hs
  apply Eq.trans _ (hw ψ hψ hc hs)
  exact integral_congr_ae ((hentry j k).symm.mono fun y hy => congrArg (_ • ·) hy)

/-- A pointwise comparison for a Sobolev representative bounds the integral
costs of the original density, including the curvature and active-set terms. -/
theorem RepresentativeTileInput.bound {D : Density} {φ : Phase} {G : MatrixGradient} {p δ A R : ℝ}
    {c : Position} {X : ℝ} (h : RepresentativeTileInput D φ G p δ A R c X)
    (hp : 3 < p) (hδ : 0 < δ) (hδle : δ ≤ 1) (hA : 1 ≤ A) (hR : 0 < R)
    (hρ : Integrable D.charge)
    (hbase : Integrable (fun x => D.charge x + D.charge x^2 + D.charge x*‖φ.grad x‖^2))
    (hφ : PhaseAdmissible D p φ G) :
    X ≤ tileConstant p A *
      (δ * ballAverage R (fun x => D.charge x + D.charge x^2 + D.charge x*‖φ.grad x‖^2) c +
       ballAverage R (fun x => D.charge x * φ.hessianNorm x ^ p + weightedRoot φ G p x) c /
         δ ^ (2 * p - 1)) := by
  obtain ⟨D', heq, ht⟩ := h
  have hc : D'.charge =ᵐ[volume] D.charge :=
    heq.mono fun x hx => congrArg (fun M : SpinMatrix => M.trace.re) hx
  have hb : (fun x => D'.charge x + D'.charge x^2 + D'.charge x*‖φ.grad x‖^2) =ᵐ[volume]
      (fun x => D.charge x + D.charge x^2 + D.charge x*‖φ.grad x‖^2) :=
    hc.mono fun x hx => congrArg (fun t : ℝ => t + t^2 + t*‖φ.grad x‖^2) hx
  have hφ' : PhaseAdmissible D' p φ G :=
    ⟨hφ.regular, rootRegular_congr heq.symm hφ.root_regular,
      hφ.kinetic.congr (hc.symm.mul Filter.EventuallyEq.rfl),
      hφ.curvature.congr (hc.symm.mul Filter.EventuallyEq.rfl), hφ.root_weighted⟩
  have havg {f g : Position → ℝ} (e : f =ᵐ[volume] g) :
      ballAverage R f c = ballAverage R g c :=
    congrArg (· / ballVolume R) (integral_congr_ae (ae_restrict_of_ae (s := Metric.ball c R) e))
  have bound := ht.bound hp hδ hδle hA hR (hρ.congr hc.symm) (hbase.congr hb.symm) hφ'
  rw [havg hb, havg (f := fun x => D'.charge x * φ.hessianNorm x ^ p + weightedRoot φ G p x)
    (g := fun x => D.charge x * φ.hessianNorm x ^ p + weightedRoot φ G p x)
    (hc.mono fun x hx => congrArg (fun t : ℝ => t * φ.hessianNorm x ^ p + weightedRoot φ G p x) hx)]
    at bound
  exact bound

end TSGA.PhaseLocalization
