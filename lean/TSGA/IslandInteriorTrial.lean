import TSGA.IslandMasks
import TSGA.PhysicalTSGA
import Mathlib.Analysis.MeanInequalitiesPow

/-! # The state inside the Poisson islands

The occupied density is the sum of two positive scalar multiples of the input
spin densities. Its Fisher estimate uses the derivative of the combined
density, so no derivative of the square root of the added density is needed.
-/

noncomputable section
namespace TSGA.ManyBody
universe u
open MeasureTheory Matrix TSGA.Localization
open scoped ComplexOrder MatrixOrder

/-- Uniform cost of the layer trial with layer parameter one. -/
def FiniteEnergyInputs.interiorConstant (H : FiniteEnergyInputs) : ℝ :=
  H.cTF * (1+H.κ₁) + 8*(1+H.κ₂)

theorem FiniteEnergyInputs.interiorConstant_nonneg (H : FiniteEnergyInputs) :
    0 ≤ H.interiorConstant := by
  unfold interiorConstant
  have := H.κ₁_nonneg
  have := H.κ₂_nonneg
  have := H.cTF_nonneg
  positivity

/-- Realize the layer projector as an actual mixed state. Its exchange term
has the favorable sign before averaging over the random interiors. -/
theorem FiniteEnergyInputs.exists_island_state (H : FiniteEnergyInputs)
    (D : Density) (S : MatrixGradient) (hD : SqrtRegular D S)
    (hq : Integrable (fun x => D.charge x ^ (5/3 : ℝ))) :
    ∃ Γ : MixedState, feasible D.matrix Γ ∧
      Γ.kinetic ≤ H.interiorConstant*(chargeMoment D (5/3) + sqrtKinetic S) ∧
      Γ.interaction ≤ hartree D.charge := by
  obtain ⟨w⟩ := H.trials D S hD 1 zero_lt_one
  obtain ⟨Γ,hΓ,hkin,hint⟩ := H.quasiFree w.gamma
  refine ⟨Γ,hΓ.trans w.density,?_,?_⟩
  · have hI : Integrable (kineticDensity S) := by
      change Integrable (fun x => matrixGradNorm S x ^ 2)
      simpa only [Real.norm_eq_abs, sq_abs] using
        (hD.grad.integrable_norm_pow (p := 2) (by decide))
    have hg := integral_mono_ae w.integrable (hI.const_mul _) w.gradient_estimate
    rw [integral_const_mul] at hg
    have ht : traceMoment D (5/3) ≤ chargeMoment D (5/3) :=
      integral_mono_of_nonneg (ae_of_all _ fun x => tracePower_nonneg D x _) hq
        (ae_of_all _ fun x => tracePower_le_charge D x (by norm_num))
    have ht₀ : 0 ≤ traceMoment D (5/3) := integral_nonneg fun x => tracePower_nonneg D x _
    have hkin₀ : 0 ≤ sqrtKinetic S := integral_nonneg fun _ => sq_nonneg _
    have hq₀ : 0 ≤ chargeMoment D (5/3) :=
      integral_nonneg fun x => Real.rpow_nonneg (D.charge_nonneg x) _
    have hf := w.stiffness_bound
    norm_num only [Real.sqrt_one, mul_one, div_one] at hf
    have hgradCoeff : (1+√(trialStiffness w.profile))^2 ≤ 8*(1+H.κ₂) := by
      nlinarith [Real.sq_sqrt (trialStiffness_nonneg w.profile), sq_nonneg (1-√(trialStiffness w.profile))]
    have hm := w.moment_bound
    rw [mul_one] at hm
    change (∫ x, layerCost w.gradient x) ≤ _ * sqrtKinetic S at hg
    rw [hkin, w.kinetic_trace]
    unfold interiorConstant
    have htf := mul_le_mul_of_nonneg_left ht
      (mul_nonneg H.cTF_nonneg (add_nonneg zero_le_one H.κ₁_nonneg))
    have hm' := mul_le_mul_of_nonneg_left hm (mul_nonneg H.cTF_nonneg ht₀)
    have hg' := mul_le_mul_of_nonneg_right hgradCoeff hkin₀
    nlinarith only [hg,hg',hm',htf,
      mul_nonneg (mul_nonneg H.cTF_nonneg (add_nonneg zero_le_one H.κ₁_nonneg)) hkin₀,
      mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (8:ℝ)) (add_nonneg zero_le_one H.κ₂_nonneg)) hq₀]
  · rw [hint,hartree_congr (w.density.mono fun x hx => congrArg (fun A : SpinMatrix => A.trace.re) hx)]
    exact sub_le_self _ w.gamma.exchange_nonneg

/-- Positive spin density carried by the two nested island cutoffs. -/
def islandInteriorDensity (B D : Density) (a b : Position → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) : Density where
  matrix x := a x • B.matrix x + b x • D.matrix x
  positive x := ((B.positive x).smul (ha x)).add ((D.positive x).smul (hb x))

@[simp] theorem islandInteriorDensity_charge (B D : Density) (a b : Position → ℝ) (ha hb)
    (x : Position) : (islandInteriorDensity B D a b ha hb).charge x =
      a x*B.charge x + b x*D.charge x := by
  simp [Density.charge,islandInteriorDensity,Matrix.trace_add,Matrix.trace_smul,Complex.real_smul]

/-- A positive matrix tangent is a derivative of a square, including at a
singular density. -/
def RootTangent (M Y : SpinMatrix) : Prop :=
  ∃ Z : SpinMatrix, Y = CFC.sqrt M * Z + Z * CFC.sqrt M

/-- The seminorm of the inverse Sylvester operator on square-root
tangents. The order estimate is the monotonicity and homogeneity of the
matrix Fisher form. Its right-hand direction is always compatible even at
a kernel. -/
structure RootFisherForm where
  sq : SpinMatrix → SpinMatrix → ℝ
  nonneg : ∀ A Y, 0 ≤ sq A Y
  add_four : ∀ A U V W X, sq A (U+V+W+X) ≤ 4*(sq A U+sq A V+sq A W+sq A X)
  order : ∀ {A M Y : SpinMatrix} {a b u : ℝ}, A.PosSemidef → M.PosSemidef →
    RootTangent A Y → 0 ≤ a → 0 ≤ b → a • A ≤ M → u^2 ≤ a*b → sq M (u • Y) ≤ b*sq A Y
  radial : ∀ A : SpinMatrix, A.PosSemidef → sq A A ≤ A.trace.re / 4

private theorem tangent_self {A : SpinMatrix} (h : A.PosSemidef) : RootTangent A A := by
  refine ⟨(1/2:ℝ) • CFC.sqrt A,?_⟩
  rw [Matrix.mul_smul,Matrix.smul_mul,CFC.sqrt_mul_sqrt_self _ h.nonneg,← add_smul]
  norm_num

/-- The derivative is expressed in terms of the background B and the
available combined density E = D + ε B, even where √D has no derivative. -/
def interiorDerivative (B D dB dE : SpinMatrix) (ε c₁ c₂ χ₁ χ₂ g₁ g₂ : ℝ) : SpinMatrix :=
  (c₂*χ₂) • dE + (c₁*χ₁-ε*c₂*χ₂) • dB +
    (2*c₁*√χ₁*g₁) • B + (2*c₂*√χ₂*g₂) • D

/-- Pointwise Fisher bound for the two nested cutoffs. It also holds when
one cutoff vanishes or one of the spin densities has rank one. -/
theorem interior_fisher_bound (Q : RootFisherForm) {B D dB dE : SpinMatrix}
    (hB : B.PosSemidef) (hD : D.PosSemidef) {ε c₁ c₂ χ₁ χ₂ g₁ g₂ K : ℝ}
    (he : 0 ≤ ε) (hK : 1 ≤ K) (hc₁ : 1 ≤ c₁) (hc₁' : c₁ ≤ K) (hc₂ : 0 ≤ c₂)
    (hεc : ε*c₂ ≤ K) (h₂ : 0 ≤ χ₂) (hn : χ₂ ≤ χ₁)
    (hdB : RootTangent B dB) (hdE : RootTangent (D+ε • B) dE) :
    Q.sq ((c₁*χ₁) • B+(c₂*χ₂) • D) (interiorDerivative B D dB dE ε c₁ c₂ χ₁ χ₂ g₁ g₂) ≤
      4*(K*c₂*χ₂*Q.sq (D+ε • B) dE + 4*K^2*χ₁*Q.sq B dB +
        c₁*g₁^2*B.trace.re + c₂*g₂^2*D.trace.re) := by
  let a := c₁*χ₁
  let b := c₂*χ₂
  have hKp : 0 < K := by linarith
  have hc₁₀ := zero_le_one.trans hc₁
  have h₁ := h₂.trans hn
  have ha : 0 ≤ a := mul_nonneg hc₁₀ h₁
  have hb : 0 ≤ b := mul_nonneg hc₂ h₂
  have hp := (hB.smul ha).add (hD.smul hb)
  have haord : a • B ≤ a • B + b • D := le_add_of_nonneg_right (hD.smul hb).nonneg
  have hbord : b • D ≤ a • B + b • D := le_add_of_nonneg_left (hB.smul ha).nonneg
  have hbc : ε*b ≤ K*χ₁ := by
    exact (show ε*b = (ε*c₂)*χ₂ by dsimp [b]; ring) ▸
      (mul_le_mul_of_nonneg_right hεc h₂).trans (mul_le_mul_of_nonneg_left hn hKp.le)
  have ha' : χ₁ ≤ a := by simpa [a] using mul_le_mul_of_nonneg_right hc₁ h₁
  have hbase : (b/K) • (D+ε • B) ≤ a • B+b • D := by
    have hsmall : b/K ≤ b := div_le_self hb hK
    have hbg : b/K*ε ≤ a := by
      rw [div_mul_eq_mul_div,div_le_iff₀ hKp]
      nlinarith only [hbc,mul_le_mul_of_nonneg_left ha' hKp.le]
    rw [smul_add,smul_smul,add_comm]
    exact add_le_add (smul_le_smul_of_nonneg_right hbg hB.nonneg)
      (smul_le_smul_of_nonneg_right hsmall hD.nonneg)
  have h₀ := Q.order (hD.add (hB.smul he)) hp hdE (div_nonneg hb hKp.le)
    (mul_nonneg hKp.le hb) hbase (show b^2 ≤ b/K*(K*b) by field_simp; rfl)
  have hsq : (a-ε*b)^2 ≤ a*(4*K^2*χ₁) := by
    have ham : a ≤ K*χ₁ := mul_le_mul_of_nonneg_right hc₁' h₁
    have hpos := mul_nonneg he hb
    have ab : |a-ε*b| ≤ K*χ₁ := abs_le.mpr ⟨by linarith,by linarith⟩
    have hab := pow_le_pow_left₀ (abs_nonneg _) ab 2
    rw [sq_abs] at hab
    nlinarith only [hab, mul_le_mul_of_nonneg_right ha' (mul_nonneg (sq_nonneg K) h₁),
      mul_nonneg ha (mul_nonneg (sq_nonneg K) h₁)]
  have h₁' := Q.order hB hp hdB ha (by positivity : 0 ≤ 4*K^2*χ₁) haord hsq
  have radialB := Q.order hB hp (tangent_self hB) ha (by positivity : 0 ≤ 4*c₁*g₁^2) haord
    (show (2*c₁*√χ₁*g₁)^2 ≤ a*(4*c₁*g₁^2) by dsimp [a]; simp only [mul_pow,Real.sq_sqrt h₁]; ring_nf; rfl)
  have radialD := Q.order hD hp (tangent_self hD) hb (by positivity : 0 ≤ 4*c₂*g₂^2) hbord
    (show (2*c₂*√χ₂*g₂)^2 ≤ b*(4*c₂*g₂^2) by dsimp [b]; simp only [mul_pow,Real.sq_sqrt h₂]; ring_nf; rfl)
  have b₁ := mul_le_mul_of_nonneg_left (Q.radial _ hB) (show 0 ≤ 4*c₁*g₁^2 by positivity)
  have b₂ := mul_le_mul_of_nonneg_left (Q.radial _ hD) (show 0 ≤ 4*c₂*g₂^2 by positivity)
  unfold interiorDerivative
  dsimp only [a,b] at h₀ h₁' radialB radialD
  rw [← mul_assoc ε c₂ χ₂] at h₁'
  have adds := Q.add_four ((c₁*χ₁) • B+(c₂*χ₂) • D)
    ((c₂*χ₂) • dE) ((c₁*χ₁-ε*c₂*χ₂) • dB) ((2*c₁*√χ₁*g₁) • B) ((2*c₂*√χ₂*g₂) • D)
  nlinarith only [adds,h₀,h₁',radialB,radialD,b₁,b₂]

/-- One nonnegative random multiplier tested against an integrable
deterministic energy density. -/
structure IslandMultiplier {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (w : Ω → Position → ℝ) (m : ℝ) : Prop where
  pos : ∀ ω x, 0 ≤ w ω x
  measurable : AEStronglyMeasurable (fun z : Ω × Position => w z.1 z.2) (μ.prod volume)
  mean : ∀ᵐ x, Integrable (fun ω => w ω x) μ ∧ (∫ ω, w ω x ∂μ) ≤ m

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem IslandMultiplier.weighted {w m} (H : IslandMultiplier μ w m)
    {a : Position → ℝ} (ha : Integrable a) (a₀ : ∀ x, 0 ≤ a x) :
    Integrable (fun z : Ω × Position => w z.1 z.2*a z.2) (μ.prod volume) ∧
      (∫ ω, ∫ x, w ω x*a x ∂volume ∂μ) ≤ m*(∫ x, a x) := by
  let f (z : Ω × Position) := w z.1 z.2 * a z.2
  have hm : AEStronglyMeasurable f (μ.prod volume) := H.measurable.mul ha.1.comp_snd
  have hp (ω x) : 0 ≤ f (ω,x) := mul_nonneg (H.pos ω x) (a₀ x)
  have av : ∀ᵐ x : Position, (∫ ω, f (ω,x) ∂μ) ≤ m*a x := by
    filter_upwards [H.mean] with x hx
    change (∫ ω, w ω x*a x ∂μ) ≤ _
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hx.2 (a₀ x)
  have hi : Integrable f (μ.prod volume) := by
    refine (integrable_prod_iff' hm).2 ⟨H.mean.mono fun x hx => hx.1.mul_const (a x),?_⟩
    apply (ha.const_mul m).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [av] with x hx
    change ‖∫ ω, ‖f (ω,x)‖ ∂μ‖ ≤ _
    simp only [Real.norm_eq_abs,abs_of_nonneg (hp _ _),abs_of_nonneg (show 0 ≤ ∫ ω, f (ω,x) ∂μ from integral_nonneg fun ω => hp ω x)]
    exact hx
  refine ⟨hi,?_⟩
  rw [integral_integral_swap hi,← integral_const_mul]
  exact integral_mono_ae hi.integral_prod_right (ha.const_mul m) av

private theorem charge53_point {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^(5/3:ℝ) ≤ 4*(a^(5/3:ℝ)+b^(5/3:ℝ)) := by
  have aux {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ≤ v) :
      (u+v)^(5/3:ℝ) ≤ 4*v^(5/3:ℝ) := by
    have hh := Real.rpow_le_rpow (add_nonneg hu hv) (by linarith : u+v ≤ 2*v) (by norm_num : (0:ℝ) ≤ 5/3)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hv] at hh
    have H := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (5/3:ℝ) ≤ 2)
    rw [Real.rpow_two] at H
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : (2:ℝ)^(5/3:ℝ) ≤ 4) (Real.rpow_nonneg hv _))
  rcases le_total a b with hab | hba
  · linarith [aux ha hb hab,Real.rpow_nonneg ha (5/3)]
  · rw [add_comm a b]
    linarith [aux hb ha hba,Real.rpow_nonneg hb (5/3)]

/-- Spatially stationary one-point means give the fractional-power gain in
the Thomas–Fermi term. In particular the coefficient of the added
population is c₂^(2/3), since c₂ times its mean cutoff equals one. -/
theorem interior_charge_average (B D : Density) {c₁ c₂ m₁ m₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (χ₁ χ₂ : Ω → Position → ℝ) (h₁ : IslandMultiplier μ χ₁ m₁) (h₂ : IslandMultiplier μ χ₂ m₂)
    (range₁ : ∀ ω x, χ₁ ω x ≤ 1) (range₂ : ∀ ω x, χ₂ ω x ≤ 1)
    (mass : c₂*m₂=1) (bi : Integrable fun x => B.charge x^(5/3:ℝ))
    (di : Integrable fun x => D.charge x^(5/3:ℝ)) :
    let f ω x := ((c₁*χ₁ ω x)*B.charge x+(c₂*χ₂ ω x)*D.charge x)^(5/3:ℝ)
    Integrable (fun z : Ω × Position => f z.1 z.2) (μ.prod volume) ∧
    (∫ ω, ∫ x, f ω x ∂volume ∂μ) ≤
      4*(c₁^(5/3:ℝ)*m₁*chargeMoment B (5/3) + c₂^(2/3:ℝ)*chargeMoment D (5/3)) := by
  intro f
  let a (z : Ω × Position) := c₁^(5/3:ℝ)*(χ₁ z.1 z.2*B.charge z.2^(5/3:ℝ))
  let b (z : Ω × Position) := c₂^(5/3:ℝ)*(χ₂ z.1 z.2*D.charge z.2^(5/3:ℝ))
  have ah := h₁.weighted bi (fun x => Real.rpow_nonneg (B.charge_nonneg x) _)
  have bh := h₂.weighted di (fun x => Real.rpow_nonneg (D.charge_nonneg x) _)
  have ai : Integrable a (μ.prod volume) := ah.1.const_mul _
  have bj : Integrable b (μ.prod volume) := bh.1.const_mul _
  have hpow {c χ ρ : ℝ} (hc : 0 ≤ c) (hχ : 0 ≤ χ) (hχ' : χ ≤ 1) (hρ : 0 ≤ ρ) :
      ((c*χ)*ρ)^(5/3:ℝ) ≤ c^(5/3:ℝ)*(χ*ρ^(5/3:ℝ)) := by
    rw [Real.mul_rpow (mul_nonneg hc hχ) hρ,Real.mul_rpow hc hχ,mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_le_one hχ hχ' (by norm_num)) (Real.rpow_nonneg hρ _)) (Real.rpow_nonneg hc _)
  have f₀ (z : Ω × Position) : 0 ≤ f z.1 z.2 := Real.rpow_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hc₁ (h₁.pos _ _)) (B.charge_nonneg _))
                (mul_nonneg (mul_nonneg hc₂.le (h₂.pos _ _)) (D.charge_nonneg _))) _
  have fle (z : Ω × Position) : f z.1 z.2 ≤ 4*(a z+b z) :=
    (charge53_point (mul_nonneg (mul_nonneg hc₁ (h₁.pos _ _)) (B.charge_nonneg _))
                (mul_nonneg (mul_nonneg hc₂.le (h₂.pos _ _)) (D.charge_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hpow hc₁ (h₁.pos _ _) (range₁ _ _) (B.charge_nonneg _))
          (hpow hc₂.le (h₂.pos _ _) (range₂ _ _) (D.charge_nonneg _))) (by norm_num))
  have bm : AEStronglyMeasurable B.charge volume := by
    apply (bi.1.aemeasurable.pow_const (3/5 : ℝ)).aestronglyMeasurable.congr
    apply ae_of_all
    intro x
    change (B.charge x ^ (5/3:ℝ)) ^ (3/5:ℝ) = B.charge x
    rw [← Real.rpow_mul (B.charge_nonneg x)]
    norm_num
  have dm : AEStronglyMeasurable D.charge volume := by
    apply (di.1.aemeasurable.pow_const (3/5 : ℝ)).aestronglyMeasurable.congr
    apply ae_of_all
    intro x
    change (D.charge x ^ (5/3:ℝ)) ^ (3/5:ℝ) = D.charge x
    rw [← Real.rpow_mul (D.charge_nonneg x)]
    norm_num
  have fm : AEStronglyMeasurable (fun z : Ω × Position => f z.1 z.2) (μ.prod volume) :=
    ((((h₁.measurable.const_mul c₁).mul bm.comp_snd).add
      ((h₂.measurable.const_mul c₂).mul dm.comp_snd)).aemeasurable.pow_const _).aestronglyMeasurable
  have F := ((ai.add bj).const_mul 4).mono' fm
    (ae_of_all _ (fun z => by rw [Real.norm_of_nonneg (f₀ z)]; exact fle z))
  refine ⟨F,?_⟩
  rw [← integral_prod _ F]
  have H := integral_mono F ((ai.add bj).const_mul 4) fle
  erw [integral_const_mul, integral_add ai bj, integral_prod _ ai,integral_prod _ bj] at H
  simp only [a,b,integral_const_mul] at H
  have e₂ : c₂^(5/3:ℝ)*m₂ = c₂^(2/3:ℝ) := by
    rw [show (5/3:ℝ)=2/3+1 by norm_num, Real.rpow_add_one hc₂.ne',mul_assoc,mass,mul_one]
  rw [← e₂]
  dsimp only [chargeMoment]
  linarith only [H,mul_le_mul_of_nonneg_left ah.2 (Real.rpow_nonneg hc₁ (5/3)),
    mul_le_mul_of_nonneg_left bh.2 (Real.rpow_nonneg hc₂.le (5/3))]



/-- A jointly integrable majorant and its full integral. -/
structure IslandIntegral (μ : Measure Ω) (w : Ω → Position → ℝ) (m : ℝ) : Prop where
  joint : Integrable (fun z : Ω × Position => w z.1 z.2) (μ.prod volume)
  bound : (∫ z : Ω × Position, w z.1 z.2 ∂μ.prod volume) ≤ m

namespace IslandIntegral
theorem of_weight {w m} (wH : IslandMultiplier μ w m) {a : Position → ℝ}
    (ha : Integrable a) (h₀ : ∀ x, 0 ≤ a x) :
    IslandIntegral μ (fun ω x => w ω x*a x) (m*(∫ x, a x)) := by
  obtain ⟨hi,hb⟩ := wH.weighted ha h₀
  exact ⟨hi, by rw [integral_prod _ hi]; exact hb⟩

omit [IsProbabilityMeasure μ] in
theorem add {w u m n} (A : IslandIntegral μ w m) (B : IslandIntegral μ u n) :
    IslandIntegral μ (fun ω x => w ω x+u ω x) (m+n) := by
  exact ⟨A.joint.add B.joint, by rw [integral_add A.joint B.joint]; exact add_le_add A.bound B.bound⟩

omit [IsProbabilityMeasure μ] in
theorem scale {w m} (A : IslandIntegral μ w m) (c : ℝ) (hc : 0 ≤ c) :
    IslandIntegral μ (fun ω x => c*w ω x) (c*m) :=
  ⟨A.joint.const_mul _, by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left A.bound hc⟩
end IslandIntegral

def squareDerivative (D : Density) (G : MatrixGradient) (x : Position) (i : Fin 3) : SpinMatrix :=
  CFC.sqrt (D.matrix x)*G x i + G x i*CFC.sqrt (D.matrix x)

/-- Weak product and chain rules for arbitrary positive matrix fields.
The regularization clause is the square-root Sobolev criterion obtained
by adding a positive scalar to the matrix and passing to the limit.
The derivative representative can be fixed by difference quotients. -/
structure FisherSobolevCalculus extends RootFisherForm where
  gradient : Density → MatrixGradient
  square_weak : ∀ D S, SqrtRegular D S →
    IsMatrixGradientOn Set.univ D.matrix (squareDerivative D S)
  square_cost : ∀ D S, SqrtRegular D S → ∀ᵐ x,
    (∑ i, sq (D.matrix x) (squareDerivative D S x i)) ≤ kineticDensity S x
  subtract : ∀ (A B : Position → SpinMatrix) (dA dB : MatrixGradient) (c : ℝ),
    IsMatrixGradientOn Set.univ A dA → IsMatrixGradientOn Set.univ B dB →
    IsMatrixGradientOn Set.univ (fun x => A x-c • B x) (fun x i => dA x i-c • dB x i)
  product_rule : ∀ (A B : Position → SpinMatrix) (dA dB : MatrixGradient)
    (f g : Position → ℝ) (df dg : Position → Fin 3 → ℝ) (a b : ℝ),
    IsMatrixGradientOn Set.univ A dA → IsMatrixGradientOn Set.univ B dB →
    LocallyLipschitz f → LocallyLipschitz g →
    (∀ i, WeakPartialOn Set.univ i f (fun x => df x i)) →
    (∀ i, WeakPartialOn Set.univ i g (fun x => dg x i)) →
    IsMatrixGradientOn Set.univ (fun x => (a*(f x)^2) • A x+(b*(g x)^2) • B x)
      (fun x i => (a*(f x)^2) • dA x i + (b*(g x)^2) • dB x i +
        (2*a*f x*df x i) • A x + (2*b*g x*dg x i) • B x)
  regularize : ∀ N Z (w : Position → ℝ), Integrable N.charge → IsMatrixGradientOn Set.univ N.matrix Z →
    Integrable w → (∀ᵐ x, (∑ i, sq (N.matrix x) (Z x i)) ≤ w x) →
    SqrtRegular N (gradient N) ∧ ∀ᵐ x, kineticDensity (gradient N) x ≤ w x
  kinetic_measurable : ∀ {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (N : Λ → Density), (∀ i j, AEStronglyMeasurable (fun z : Λ × Position => (N z.1).matrix z.2 i j)
      (ν.prod volume)) → AEStronglyMeasurable (fun ω => sqrtKinetic (gradient (N ω))) ν

/-- Scalar information on the two interior profiles. All spatial expectations
here test a single point and do not depend on either spin density. -/
structure InteriorMaskData {ε : ℝ} (m : IslandMasks μ (ε/2)) (r K : ℝ) where
  K_ge : 1 ≤ K
  lower₁ : 1 ≤ m.c₁
  upper₁ : m.c₁ ≤ K
  upper₂ : ε*m.c₂ ≤ K
  first_small : m.meanFirst ≤ ε
  first_measurable : AEStronglyMeasurable (fun z : Ω × Position => m.first z.1 z.2) (μ.prod volume)
  core_measurable : AEStronglyMeasurable (fun z : Ω × Position => m.core z.1 z.2) (μ.prod volume)
  g₁ : Ω → Position → Fin 3 → ℝ
  g₂ : Ω → Position → Fin 3 → ℝ
  lip₁ : ∀ᵐ ω ∂μ, LocallyLipschitz (fun x => Real.sqrt (m.first ω x))
  lip₂ : ∀ᵐ ω ∂μ, LocallyLipschitz (fun x => Real.sqrt (m.core ω x))
  weak₁ : ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (m.first ω x)) (fun x => g₁ ω x i)
  weak₂ : ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (m.core ω x)) (fun x => g₂ ω x i)
  shell : IslandMultiplier μ (fun ω x => ∑ i, (g₁ ω x i)^2) (K*ε)
  core : IslandMultiplier μ (fun ω x => ∑ i, (g₂ ω x i)^2) (K*ε*r⁻¹^2)

namespace InteriorMaskData
variable {B D : Density} {ε r K : ℝ} {m : IslandMasks μ (ε/2)} (L : InteriorMaskData m r K)

omit [IsProbabilityMeasure μ] in
theorem c₂_pos : 0 < m.c₂ := one_div_pos.mpr m.core_pos

def localDensity (B D : Density) (ω : Ω) : Density :=
  islandInteriorDensity B D (fun x => m.c₁*m.first ω x) (fun x => m.c₂*m.core ω x)
    (fun x => mul_nonneg (zero_le_one.trans L.lower₁) (m.first_range ω x).1)
    (fun x => mul_nonneg (c₂_pos (m := m)).le (m.core_range ω x).1)

include L in
omit [IsProbabilityMeasure μ] in
theorem first_weight : IslandMultiplier μ m.first m.meanFirst :=
  ⟨fun ω x => (m.first_range ω x).1,L.first_measurable,
    ae_of_all _ fun x => ⟨(m.first_mean x).1,(m.first_mean x).2.le⟩⟩

include L in
omit [IsProbabilityMeasure μ] in
theorem core_weight : IslandMultiplier μ m.core m.meanCore :=
  ⟨fun ω x => (m.core_range ω x).1,L.core_measurable,
    ae_of_all _ fun x => ⟨(m.core_mean x).1,(m.core_mean x).2.le⟩⟩

def majorant (G : IslandGradients B D ε) (ω : Ω) (x : Position) :=
  4*((K*m.c₂)*(m.core ω x*kineticDensity G.mixed x) +
    (4*K^2)*(m.first ω x*kineticDensity G.background x) +
    m.c₁*((∑ i, (L.g₁ ω x i)^2)*B.charge x) + m.c₂*((∑ i, (L.g₂ ω x i)^2)*D.charge x))

theorem majorant_integral (G : IslandGradients B D ε) (d : Integrable D.charge) :
    IslandIntegral μ (L.majorant G) (4*((K*m.c₂)*(m.meanCore*sqrtKinetic G.mixed) +
      (4*K^2)*(m.meanFirst*sqrtKinetic G.background) + m.c₁*((K*ε)*(∫ x, B.charge x)) +
      m.c₂*((K*ε*r⁻¹^2)*(∫ x, D.charge x)))) := by
  have hk := zero_le_one.trans L.K_ge
  have hc := (c₂_pos (m := m)).le
  have E := (IslandIntegral.of_weight L.core_weight G.mixed_regular.grad.integrable_sq
    (fun x => sq_nonneg (matrixGradNorm G.mixed x))).scale (K*m.c₂) (mul_nonneg hk hc)
  have A := (IslandIntegral.of_weight L.first_weight G.background_regular.grad.integrable_sq
    (fun x => sq_nonneg (matrixGradNorm G.background x))).scale (4*K^2) (by positivity)
  have V := (IslandIntegral.of_weight L.shell G.background_regular.charge B.charge_nonneg).scale
    m.c₁ (zero_le_one.trans L.lower₁)
  have W := (IslandIntegral.of_weight L.core d D.charge_nonneg).scale m.c₂ hc
  exact (((E.add A).add V).add W).scale 4 (by norm_num)

theorem field_regular (F : FisherSobolevCalculus.{u}) (G : IslandGradients B D ε) (he : 0 ≤ ε)
    (d : Integrable D.charge) : ∀ᵐ ω ∂μ,
    SqrtRegular (L.localDensity B D ω) (F.gradient (L.localDensity B D ω)) ∧
      ∀ᵐ x, kineticDensity (F.gradient (L.localDensity B D ω)) x ≤ L.majorant G ω x := by
  let A := squareDerivative B G.background
  let E := squareDerivative G.combined G.mixed
  have hA := F.square_weak _ _ G.background_regular
  have hE := F.square_weak _ _ G.mixed_regular
  have hD := F.subtract _ _ _ _ ε hE hA
  have subfield : (fun x => G.combined.matrix x-ε • B.matrix x) = D.matrix := by
    funext x; rw [G.combined_matrix,add_sub_cancel_right]
  rw [subfield] at hD
  have hb := L.first_weight.weighted G.background_regular.charge B.charge_nonneg
  have hd := L.core_weight.weighted d D.charge_nonneg
  have charge := ((hb.1.const_mul m.c₁).add (hd.1.const_mul m.c₂)).prod_right_ae
  filter_upwards [L.lip₁,L.lip₂,L.weak₁,L.weak₂,(L.majorant_integral G d).joint.prod_right_ae,
    charge] with ω l₁ l₂ f₁ f₂ hmajor hcharge
  let X := fun x i => interiorDerivative (B.matrix x) (D.matrix x) (A x i) (E x i) ε
    m.c₁ m.c₂ (m.first ω x) (m.core ω x) (L.g₁ ω x i) (L.g₂ ω x i)
  apply F.regularize _ X _ _ _ hmajor
  · filter_upwards [F.square_cost _ _ G.background_regular,F.square_cost _ _ G.mixed_regular]
      with x hBg hCo
    have hn : m.core ω x ≤ m.first ω x := by
      by_cases h : m.core ω x = 0
      · exact h ▸ (m.first_range ω x).1
      · rw [m.nested _ _ h]; exact (m.core_range ω x).2
    have epos := zero_le_one.trans L.K_ge
    have cpos := (c₂_pos (m := m)).le
    have h (i : Fin 3) := interior_fisher_bound F.toRootFisherForm
      (hB := B.positive x) (hD := D.positive x) (g₁ := L.g₁ ω x i) (g₂ := L.g₂ ω x i)
      he L.K_ge L.lower₁ L.upper₁ cpos L.upper₂ (m.core_range ω x).1 hn
      (show RootTangent (B.matrix x) (A x i) from ⟨G.background x i,rfl⟩)
      (show RootTangent (D.matrix x+ε • B.matrix x) (E x i) by
        rw [← G.combined_matrix]; exact ⟨G.mixed x i,rfl⟩)
    have S := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
    simp only [← G.combined_matrix] at S
    change _ ≤ 4*(_+_+_+_)
    dsimp only [localDensity,islandInteriorDensity,X,A,E,majorant] at *
    simp only [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_add_distrib] at S
    have h1 := mul_le_mul_of_nonneg_left hBg
      (show 0 ≤ 4*K^2*m.first ω x from mul_nonneg (by positivity) (m.first_range ω x).1)
    have h2 := mul_le_mul_of_nonneg_left hCo
      (show 0 ≤ K*m.c₂*m.core ω x from mul_nonneg (mul_nonneg epos cpos) (m.core_range ω x).1)
    dsimp only [Density.charge]
    linarith only [S,h1,h2]
  · apply hcharge.congr
    filter_upwards with x
    simp [localDensity,mul_assoc]
  · have hh := F.product_rule _ _ _ _ _ _ _ _ m.c₁ m.c₂ hA hD l₁ l₂ f₁ f₂
    simp only [Real.sq_sqrt (m.first_range _ _).1,Real.sq_sqrt (m.core_range _ _).1] at hh
    have eqX : X = fun x i => (m.c₁*m.first ω x) • A x i + (m.c₂*m.core ω x) • (E x i-ε • A x i) +
        (2*m.c₁*√(m.first ω x)*L.g₁ ω x i) • B.matrix x +
        (2*m.c₂*√(m.core ω x)*L.g₂ ω x i) • D.matrix x := by
      funext x i
      dsimp only [X,interiorDerivative]
      module
    rw [eqX]
    exact hh


theorem kinetic_measurable (F : FisherSobolevCalculus.{u}) (G : IslandGradients B D ε) :
    AEStronglyMeasurable (fun ω => sqrtKinetic (F.gradient (L.localDensity B D ω))) μ := by
  have b := F.square_weak _ _ G.background_regular
  have e := F.square_weak _ _ G.mixed_regular
  apply F.kinetic_measurable μ
  intro i j
  have bm := (locallyIntegrableOn_univ.mp (b 0 i j).1).aestronglyMeasurable
  have em := (locallyIntegrableOn_univ.mp (e 0 i j).1).aestronglyMeasurable
  have dm : AEStronglyMeasurable (fun x => D.matrix x i j) volume := by
    apply (em.sub (bm.const_smul ε)).congr
    filter_upwards with x
    simp [G.combined_matrix]
  exact ((L.first_measurable.const_mul m.c₁).smul bm.comp_snd).add
    ((L.core_measurable.const_mul m.c₂).smul dm.comp_snd)

theorem charge_estimate (G : IslandGradients B D ε) (he : 0 < ε) (b₂ : MemLp B.charge 2)
    (di : Integrable fun x => D.charge x^(5/3:ℝ)) :
    (∀ᵐ ω ∂μ, Integrable fun x => (L.localDensity B D ω).charge x^(5/3:ℝ)) ∧
    Integrable (fun ω => chargeMoment (L.localDensity B D ω) (5/3)) μ ∧
    (∫ ω, chargeMoment (L.localDensity B D ω) (5/3) ∂μ) ≤
      (16*K^2)*(ε*islandBackground B G.background + ε^(-(2/3:ℝ))*chargeMoment D (5/3)) := by
  have hm := G.background_regular.charge
  have hb (x : Position) : B.charge x^(5/3:ℝ) ≤ B.charge x+B.charge x^2 := by
    rcases (B.charge_nonneg x).eq_or_lt with h|h
    · simp [← h,Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
    · exact BulkRegime.density_power_le h (by constructor <;> norm_num)
  have hbi : Integrable fun x => B.charge x^(5/3:ℝ) :=
    (hm.add b₂.integrable_sq).mono' (hm.1.aemeasurable.pow_const _).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_of_nonneg (Real.rpow_nonneg (B.charge_nonneg x) _)).le.trans (hb x))
  have hB : chargeMoment B (5/3) ≤ islandBackground B G.background := by
    exact (integral_mono hbi (hm.add b₂.integrable_sq) hb).trans
      (le_add_of_nonneg_right (show 0 ≤ sqrtKinetic G.background from integral_nonneg fun _ => sq_nonneg _))
  have c₁ := zero_le_one.trans L.lower₁
  have c₂ := c₂_pos (m := m)
  have X := interior_charge_average B D c₁ c₂ m.first m.core L.first_weight L.core_weight
    (fun ω x => (m.first_range ω x).2) (fun ω x => (m.core_range ω x).2) m.normalized.2 hbi di
  simp only [localDensity,islandInteriorDensity_charge,chargeMoment] at X ⊢
  refine ⟨X.1.prod_right_ae,X.1.integral_prod_left,X.2.trans ?_⟩
  have h₁ : m.c₁^(5/3:ℝ) ≤ K^2 := by
    have := Real.rpow_le_rpow_of_exponent_le L.lower₁ (by norm_num : (5/3:ℝ) ≤ 2)
    rw [Real.rpow_two] at this
    exact this.trans (pow_le_pow_left₀ c₁ L.upper₁ 2)
  have k₀ := zero_le_one.trans L.K_ge
  have h₂ : m.c₂^(2/3:ℝ) ≤ K^2*ε^(-(2/3:ℝ)) := by
    have cmax : m.c₂ ≤ K*ε⁻¹ := by
      rw [← div_eq_mul_inv,le_div_iff₀ he,mul_comm]; exact L.upper₂
    have h := Real.rpow_le_rpow c₂.le cmax (by norm_num : (0:ℝ) ≤ 2/3)
    rw [Real.mul_rpow k₀ (inv_nonneg.mpr he.le),← Real.rpow_neg_eq_inv_rpow] at h
    have k := Real.rpow_le_rpow_of_exponent_le L.K_ge (by norm_num : (2/3:ℝ) ≤ 2)
    rw [Real.rpow_two] at k
    exact h.trans (mul_le_mul_of_nonneg_right k (Real.rpow_nonneg he.le _))
  have qb : 0 ≤ chargeMoment B (5/3) := integral_nonneg fun x => Real.rpow_nonneg (B.charge_nonneg x) _
  have qd : 0 ≤ chargeMoment D (5/3) := integral_nonneg fun x => Real.rpow_nonneg (D.charge_nonneg x) _
  have q1 := mul_le_mul (mul_le_mul h₁ L.first_small m.first_pos.le (sq_nonneg K)) hB qb
    (mul_nonneg (sq_nonneg K) he.le)
  have q2 := mul_le_mul_of_nonneg_right h₂ qd
  dsimp only [chargeMoment] at *
  nlinarith only [q1,q2,mul_nonneg (mul_nonneg (sq_nonneg K) he.le) (qb.trans hB),
    mul_nonneg (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg he.le (-(2/3:ℝ)))) qd]

theorem kinetic_estimate (F : FisherSobolevCalculus.{u}) (G : IslandGradients B D ε) (he : 0 ≤ ε)
    (b₂ : MemLp B.charge 2) (d : Integrable D.charge) :
    Integrable (fun ω => sqrtKinetic (F.gradient (L.localDensity B D ω))) μ ∧
    (∫ ω, sqrtKinetic (F.gradient (L.localDensity B D ω)) ∂μ) ≤
      (16*K^2)*(ε*islandBackground B G.background + sqrtKinetic G.mixed + r⁻¹^2*(∫ x, D.charge x)) := by
  have J := L.majorant_integral G d
  have h (ω : Ω) : 0 ≤ sqrtKinetic (F.gradient (L.localDensity B D ω)) := integral_nonneg fun _ => sq_nonneg _
  have hb : ∀ᵐ ω ∂μ, sqrtKinetic (F.gradient (L.localDensity B D ω)) ≤ ∫ x, L.majorant G ω x := by
    filter_upwards [L.field_regular F G he d,J.joint.prod_right_ae] with ω hr hi
    exact integral_mono_ae hr.1.grad.integrable_sq hi hr.2
  have integ := J.joint.integral_prod_left.mono' (L.kinetic_measurable F G)
    (hb.mono fun ω hx => (Real.norm_of_nonneg (h ω)).le.trans hx)
  refine ⟨integ, (integral_mono_ae integ J.joint.integral_prod_left hb).trans ?_⟩
  rw [← integral_prod _ J.joint]
  apply J.bound.trans
  have hm := G.background_regular.charge
  have kk := L.K_ge
  have k₀ := zero_le_one.trans kk
  have kb : K ≤ K^2 := by nlinarith only [mul_nonneg k₀ (sub_nonneg.mpr kk)]
  have te : 0 ≤ sqrtKinetic G.mixed := integral_nonneg fun _ => sq_nonneg _
  have tb : 0 ≤ sqrtKinetic G.background := integral_nonneg fun _ => sq_nonneg _
  have mb : 0 ≤ ∫ x, B.charge x := integral_nonneg B.charge_nonneg
  have md : 0 ≤ ∫ x, D.charge x := integral_nonneg D.charge_nonneg
  have sb : 0 ≤ ∫ x, B.charge x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [islandBackground,integral_add hm b₂.integrable_sq]
  have τ := mul_le_mul_of_nonneg_right L.first_small (mul_nonneg (sq_nonneg K) tb)
  have β := mul_le_mul_of_nonneg_right L.upper₁ (mul_nonneg k₀ (mul_nonneg he mb))
  have δ := mul_le_mul_of_nonneg_right L.upper₂ (mul_nonneg k₀ (mul_nonneg (sq_nonneg r⁻¹) md))
  have norm := m.normalized.2
  rw [show K*m.c₂*(m.meanCore*sqrtKinetic G.mixed) = K*(m.c₂*m.meanCore)*sqrtKinetic G.mixed by ring,norm,mul_one]
  nlinarith only [τ,β,δ,mul_le_mul_of_nonneg_right kb te,
    mul_nonneg (sq_nonneg K) te, mul_nonneg (sq_nonneg K) (mul_nonneg he mb),
    mul_nonneg (sq_nonneg K) (mul_nonneg he sb),mul_nonneg (sq_nonneg K) (mul_nonneg (sq_nonneg r⁻¹) md)]

/-- Assemble the interior estimate for any jointly chosen realizations of
the one-body layer trial. The only hypothesis on their energies is the
per-realization kinetic and exchange inequality. -/
def interior (F : FisherSobolevCalculus.{u}) (H : FiniteEnergyInputs) (G : IslandGradients B D ε)
    (t : IslandTrial μ (B.matrix+D.matrix)) (he : 0 < ε) (b₂ : MemLp B.charge 2)
    (d : Integrable D.charge) (di : Integrable fun x => D.charge x^(5/3:ℝ)) {C : ℝ}
    (hC : 16*K^2 ≤ C) (hH : H.interiorConstant ≤ C)
    (chosen : ∀ᵐ ω ∂μ, feasible (L.localDensity B D ω).matrix (t.inside ω) ∧
      (t.inside ω).kinetic ≤ H.interiorConstant*(chargeMoment (L.localDensity B D ω) (5/3) +
        sqrtKinetic (F.gradient (L.localDensity B D ω))) ∧
      (t.inside ω).interaction ≤ hartree (L.localDensity B D ω).charge) : IslandInterior t G r C := by
  have tf := L.charge_estimate G he b₂ di
  have ke := L.kinetic_estimate F G he.le b₂ d
  have qb (N : Density) : 0 ≤ chargeMoment N (5/3) := integral_nonneg fun x => Real.rpow_nonneg (N.charge_nonneg x) _
  have ks (S : MatrixGradient) : 0 ≤ sqrtKinetic S := integral_nonneg fun _ => sq_nonneg _
  have bg : 0 ≤ ε*islandBackground B G.background := mul_nonneg he.le (add_nonneg
    (integral_nonneg fun x => add_nonneg (B.charge_nonneg x) (sq_nonneg _)) (ks _))
  refine ⟨L.localDensity B D,chosen.mono (fun _ h => h.1.symm),_,(L.field_regular F G he.le d).mono
    (fun _ h => h.1),?_,tf.2.2.trans (mul_le_mul_of_nonneg_right hC
      (add_nonneg bg (mul_nonneg (Real.rpow_nonneg he.le _) (qb D)))),
    ke.2.trans (mul_le_mul_of_nonneg_right hC
      (add_nonneg (add_nonneg bg (ks _)) (mul_nonneg (sq_nonneg _) (integral_nonneg D.charge_nonneg))))⟩
  have ht := (tf.2.1.add ke.1).const_mul C
  unfold IslandTrial.insideEnergy
  erw [← integral_add tf.2.1 ke.1,← integral_const_mul]
  apply integral_mono_ae (t.hin.sub (integrable_hartree_of_joint t.hg)) ht
  filter_upwards [chosen,t.g_density] with ω hc hg
  have tr := hc.1.mono (fun x hx => congrArg (fun A : SpinMatrix => A.trace.re) hx)
  change (t.inside ω).kinetic+(t.inside ω).interaction-hartree (t.g ω) ≤ C*(_+_)
  rw [hartree_congr (hg.trans tr)]
  have hk := hc.2.1.trans (mul_le_mul_of_nonneg_right hH (add_nonneg (qb _) (ks _)))
  exact (sub_le_iff_le_add.mpr (add_le_add hk hc.2.2))

end InteriorMaskData
end TSGA.ManyBody
