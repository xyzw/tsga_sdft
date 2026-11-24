import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exterior indirect Coulomb energy in Appendix C

The two integrands are the pair density and the direct density divided by
twice the interparticle distance. They are individually nonnegative.
-/

noncomputable section

namespace TSGA.Islands
open MeasureTheory

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- Estimate the exponential two-point weight before applying the
smeared Graf–Schenker inequality. -/
theorem exponential_indirect {v : ℝ} {p d h : Z → ℝ}
    (hh : ∀ᵐ z ∂μ, h z ∈ Set.Icc 0 1)
    (hp : ∀ᵐ z ∂μ, 0 ≤ p z) (hd : ∀ᵐ z ∂μ, 0 ≤ d z)
    (hi : Integrable (fun z => p z-d z) μ)
    (hj : Integrable (fun z => h z*(p z-d z)) μ)
    (hk : Integrable (fun z => h z*d z) μ)
    (he : Integrable (fun z => Real.exp (v*h z)*(p z-d z)) μ) :
    (∫ z, Real.exp (v*h z)*(p z-d z) ∂μ) ≤
      (∫ z, p z-d z ∂μ) + (Real.exp v-1)*(∫ z, h z*(p z-d z) ∂μ) +
      (Real.exp v-1-v)*(∫ z, h z*d z ∂μ) := by
  erw [← integral_const_mul, ← integral_const_mul, ← integral_add hi (hj.const_mul (Real.exp v-1)),
    ← integral_add (hi.add (hj.const_mul (Real.exp v-1))) (hk.const_mul (Real.exp v-1-v))]
  apply integral_mono_ae he ((hi.add (hj.const_mul _)).add (hk.const_mul _))
  filter_upwards [hh,hp,hd] with z hz hpair hdir
  have hchord := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ v)
    (sub_nonneg.mpr hz.2) hz.1 (by ring : 1-h z+h z=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hchord
  rw [mul_comm (h z) v] at hchord
  have htan := Real.add_one_le_exp (v*h z)
  change Real.exp (v*h z)*(p z-d z) ≤ (p z-d z) +
    (Real.exp v-1)*(h z*(p z-d z)) + (Real.exp v-1-v)*(h z*d z)
  nlinarith only [mul_le_mul_of_nonneg_right hchord hpair, mul_le_mul_of_nonneg_right htan hdir]

/-- The indirect energy can have either sign. Its coefficient differs
from one by at most 4v after combining the two-point law with the
smeared Graf–Schenker lower bound. -/
theorem exterior_energy {v κ T I W H J X : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1/2)
    (hκ : κ ≤ 1/2) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hX : 0 ≤ X)
    (hweight : W ≤ I + (Real.exp v-1)*H + (Real.exp v-1-v)*J)
    (hGS : (1-κ)*H-X ≤ I) :
    Real.exp (-v)*T + Real.exp (-(2*v))*W ≤ T+I + 4*v*(|I|+X) + v^2*J := by
  let m := Real.exp (-(2*v))
  let a := Real.exp v-1
  let b := m*a/(1-κ)
  have hm : 0 ≤ m := (Real.exp_pos _).le
  have hm' : m ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hmlo : 1-2*v ≤ m := Real.one_sub_le_exp_neg _
  have ha : 0 ≤ a := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hv)
  have hav : |v| ≤ 1 := by rw [abs_of_nonneg hv]; linarith
  have ha' : a ≤ 2*v := by simpa [a, abs_of_nonneg hv, abs_of_nonneg ha] using Real.abs_exp_sub_one_le hav
  have hrest := (le_abs_self (Real.exp v-1-v)).trans (Real.abs_exp_sub_one_sub_id_le hav)
  have hden : 0 < 1-κ := by linarith
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hm ha) hden.le
  have hb' : b ≤ 4*v := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [mul_le_of_le_one_left ha hm', ha', mul_nonneg hv (sub_nonneg.mpr hκ)]
  have hmult : b*(1-κ) = m*a := div_mul_cancel₀ _ hden.ne'
  have hcoef : |m+b-1| ≤ 4*v := abs_le.mpr ⟨by linarith, by linarith⟩
  have hI : (m+b-1)*I ≤ (4*v)*|I| := by
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg I))
  have hrem : m*(Real.exp v-1-v)*J ≤ v^2*J := by
    apply mul_le_mul_of_nonneg_right _ hJ
    exact (mul_le_mul_of_nonneg_left hrest hm).trans (mul_le_of_le_one_left (sq_nonneg _) hm')
  have hp := mul_le_mul_of_nonneg_left hweight hm
  have hg := mul_le_mul_of_nonneg_left hGS hb
  have hk := mul_le_of_le_one_left hT (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv))
  have hX' := mul_le_mul_of_nonneg_right hb' hX
  change Real.exp (-v)*T + m*W ≤ _
  change W ≤ I + a*H + (Real.exp v-1-v)*J at hweight
  change m*W ≤ m*(I + a*H + (Real.exp v-1-v)*J) at hp
  nlinarith only [hp, hg, hk, hI, hrem, hX',
    congrArg (fun x : ℝ => x*H) hmult]

/-- Exterior kinetic and indirect energy with the Poisson two-point
weight. The geometric input is the smeared Graf–Schenker inequality.
Here `X` is its error and `J` is the truncated direct integral. -/
theorem exterior_indirect_bound {v κ T X : ℝ} {p d h : Z → ℝ}
    (hv : 0 ≤ v) (hv' : v ≤ 1/2) (hκ : κ ≤ 1/2) (hT : 0 ≤ T) (hX : 0 ≤ X)
    (hh : ∀ᵐ z ∂μ, h z ∈ Set.Icc 0 1) (hp : ∀ᵐ z ∂μ, 0 ≤ p z) (hd : ∀ᵐ z ∂μ, 0 ≤ d z)
    (hi : Integrable (fun z => p z-d z) μ) (hj : Integrable (fun z => h z*(p z-d z)) μ)
    (hk : Integrable (fun z => h z*d z) μ) (he : Integrable (fun z => Real.exp (v*h z)*(p z-d z)) μ)
    (hGS : (1-κ)*(∫ z, h z*(p z-d z) ∂μ) - X ≤ ∫ z, p z-d z ∂μ) :
    Real.exp (-v)*T + Real.exp (-(2*v))*(∫ z, Real.exp (v*h z)*(p z-d z) ∂μ) ≤
      T + (∫ z, p z-d z ∂μ) + 4*v*(|∫ z, p z-d z ∂μ|+X) + v^2*(∫ z, h z*d z ∂μ) :=
  exterior_energy hv hv' hκ hT (integral_nonneg_of_ae (hh.and hd |>.mono fun _ hz => mul_nonneg hz.1.1 hz.2))
    hX (exponential_indirect hh hp hd hi hj hk he) hGS

end TSGA.Islands
