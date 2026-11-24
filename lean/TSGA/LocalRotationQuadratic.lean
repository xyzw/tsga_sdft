import TSGA.GaugeEnergy

/-! # Kinetic forms for multiplication of a sector wave by a local spin unitary

Polarizing the squared norm of the weak Leibniz derivative gives its cross
term. The same positivity argument applies before and after mixing sectors.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

/-- A positive real quadratic polynomial has a Cauchy–Schwarz cross term. -/
theorem localForm_schwarz {k g j : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g)
    (h : ∀ t : ℝ, 0 ≤ k + 2*t*j + t^2*g) : j^2 ≤ k*g := by
  by_cases hz : g = 0
  · subst g
    by_contra! hn
    have hj : j ≠ 0 := by intro hj; simpa [hj] using hn
    have he : 2*(-(k+1)/(2*j))*j = -(k+1) := by field_simp
    have := h (-(k+1)/(2*j))
    linarith only [this,he]
  · have hpos := lt_of_le_of_ne hg (Ne.symm hz)
    have hmul := mul_nonneg (h (-j/g)) hg
    have hpoly : (k + 2*(-j/g)*j + (-j/g)^2*g)*g = k*g-j^2 := by field_simp; ring
    linarith only [hmul,hpoly]

abbrev LocalSectorGradient (n : ℕ) := Spins n → Space n → Fin n → Fin 3 → ℂ

def localGradientForm {n : ℕ} (a : LocalSectorGradient n) : ℝ :=
  ∑ s, ∑ i, ∑ j, ∫ x, ‖a s x i j‖^2

def localGradientCross {n : ℕ} (a b : LocalSectorGradient n) : ℝ :=
  ∑ s, ∑ i, ∑ j, ∫ x, ((a s x i j) * star (b s x i j)).re

def LocalGradientL2 {n : ℕ} (a : LocalSectorGradient n) :=
  ∀ s i j, MemLp (fun x => a s x i j) 2 volume

theorem localGradientForm_nonneg {n : ℕ} (a : LocalSectorGradient n) : 0 ≤ localGradientForm a := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => sq_nonneg _

theorem Wave.kinetic_eq_localForm {n : ℕ} (ψ : Wave n) : ψ.kinetic = localGradientForm ψ.gradient := by
  unfold kinetic sectorIntegral localGradientForm
  apply Finset.sum_congr rfl
  intro s _
  have hi (i j) := (ψ.gradient_L2 s i j).integrable_norm_pow (p := 2) (by decide)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]

theorem localGradientForm_polar {n : ℕ} (a b : LocalSectorGradient n)
    (ha : LocalGradientL2 a) (hb : LocalGradientL2 b) (t : ℝ) :
    localGradientForm (fun s x i j => a s x i j + (t : ℂ)*b s x i j) =
      localGradientForm a + 2*t*localGradientCross a b + t^2*localGradientForm b := by
  have hs (z v : ℂ) : ‖z+(t:ℂ)*v‖^2 = ‖z‖^2 + 2*t*(z*star v).re + t^2*‖v‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  have entry (s : Spins n) (i : Fin n) (j : Fin 3) :
      (∫ x, ‖a s x i j+(t:ℂ)*b s x i j‖^2) = (∫ x, ‖a s x i j‖^2) +
        2*t*(∫ x, (a s x i j*star (b s x i j)).re) + t^2*∫ x, ‖b s x i j‖^2 := by
    have hi := (ha s i j).integrable_norm_pow (p := 2) (by decide)
    have hj := (hb s i j).integrable_norm_pow (p := 2) (by decide)
    have hcross : Integrable (fun x => (a s x i j*star (b s x i j)).re) := by
      exact ((ha s i j).integrable_mul ((hb s i j).star)).re
    simp_rw [hs]
    have hp := integral_add (hi.add (hcross.const_mul (2*t))) (hj.const_mul (t^2))
    simp only [Pi.add_apply] at hp
    rw [hp,integral_add hi (hcross.const_mul (2*t)),integral_const_mul,integral_const_mul]
  unfold localGradientForm localGradientCross
  simp only [entry, Finset.sum_add_distrib, Finset.mul_sum]

end TSGA.ManyBody
