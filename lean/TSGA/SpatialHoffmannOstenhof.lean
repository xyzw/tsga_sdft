import TSGA.SpatialOrbitalDiagonal
import TSGA.HoffmannOstenhof

/-! # Spin Hoffmann–Ostenhof inequality in arbitrary spatial dimension

Only the rank-one Sobolev chain rule and convexity of the matrix Fisher
integral enter the proof. The spinor calculation is independent of space.
-/

noncomputable section
namespace TSGA.ManyBody.Spatial
open MeasureTheory Matrix
open scoped ComplexConjugate ComplexOrder

variable {d : ℕ}

def orbitalDensity (v : Point d → OrbitalValue) : Density d :=
  ⟨fun x => vecMulVec (v x) (star (v x)), fun x => posSemidef_vecMulVec_self_star (v x)⟩

/-- The weak product rule for the rank-one root, including the zero set. -/
def RankOneRootChain (d : ℕ) : Prop :=
  ∀ (v : Point d → OrbitalValue) (w : Point d → Fin d → OrbitalValue),
    (∀ i j, WeakPartial i (fun x => v x j) (fun x => w x i j)) →
    ∃ S : Gradient d, IsMatrixGradient ((orbitalDensity v).power (1/2)) S ∧
      ∀ᵐ x, (v x = 0 ∧ ∀ i, S x i = 0) ∨
        ∃ z : OrbitalValue, spinSq z = 1 ∧ v x = √(spinSq (v x)) • z ∧
          ∀ i, S x i = rootVariation z (w x i)

/-- Countable convexity and positive homogeneity of the matrix Fisher integral. -/
def CountableFisherConvexity (d : ℕ) : Prop :=
  ∀ (D : Density d) (S : Gradient d), SqrtRegular D S →
    ∀ (A : ℕ → Density d) (V : ℕ → Gradient d) (n : ℕ → ℝ), (∀ k, 0 ≤ n k) →
      (∀ k, IsMatrixGradient ((A k).power (1/2)) (V k)) →
      (∀ k, Integrable (kineticDensity (V k))) →
      (∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (A k).matrix x i j) (D.matrix x i j)) →
      Summable (fun k => n k * sqrtKinetic (V k)) →
      sqrtKinetic S ≤ ∑' k, n k * sqrtKinetic (V k)

/-- The weak root gradient of one orbital has finite energy and costs at most
twice its orbital kinetic energy. -/
theorem singleOrbital_bound (chain : RankOneRootChain d)
    (v : Point d → OrbitalValue) (w : Point d → Fin d → OrbitalValue)
    (hw : ∀ i j, WeakPartial i (fun x => v x j) (fun x => w x i j))
    (hl : ∀ i j, MemLp (fun x => w x i j) 2 volume) :
    ∃ S : Gradient d, IsMatrixGradient ((orbitalDensity v).power (1/2)) S ∧
      Integrable (kineticDensity S) ∧ sqrtKinetic S ≤ 2 * ∑ j, ∑ i, ∫ x, ‖w x i j‖ ^ 2 := by
  obtain ⟨S, hS, hform⟩ := chain v w hw
  have hbound : ∀ᵐ x, kineticDensity S x ≤ 2 * ∑ i, spinSq (w x i) := by
    filter_upwards [hform] with x hx
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change entrySq (S x i) ≤ _
    rcases hx with ⟨_, hz⟩ | ⟨z, hunit, _, hvar⟩
    · simp only [hz, entrySq, Matrix.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero]
      unfold spinSq
      positivity
    · rw [hvar]
      exact rankOne_variation_le hunit _
  have hnorm (i j) := (hl i j).integrable_norm_pow (p := 2) (by decide)
  have hspin (i) : Integrable (fun x => spinSq (w x i)) volume :=
    integrable_finsetSum _ (fun j _ => hnorm i j)
  have hmajor := (integrable_finsetSum Finset.univ (fun i _ => hspin i)).const_mul 2
  have hmeas : AEMeasurable (kineticDensity S) volume :=
    Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      Finset.aemeasurable_fun_sum _ fun k _ => (hS i j k).2.1.aestronglyMeasurable.aemeasurable.norm.pow_const 2
  have hint := hmajor.mono' hmeas.aestronglyMeasurable
    (hbound.mono fun x hx => by simpa only [Real.norm_of_nonneg (kineticDensity_nonneg S x)] using hx)
  refine ⟨S, hS, hint, ?_⟩
  have h := integral_mono_ae hint hmajor hbound
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hspin i)] at h
  simp only [spinSq, integral_finsetSum _ (fun j _ => hnorm _ j)] at h
  rw [Finset.sum_comm]
  exact h

/-- Lemma 2.1 for the spectrum of any finite-kinetic positive operator. The
occupations need only be nonnegative, and need not be bounded by one. -/
theorem hoffmann_ostenhof_occupied (chain : RankOneRootChain d) (convex : CountableFisherConvexity d)
    (D : Density d) (S : Gradient d) (hD : SqrtRegular D S)
    (v : ℕ → Point d → OrbitalValue) (w : ℕ → Point d → Fin d → OrbitalValue) (n : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ n k)
    (hw : ∀ k i j, WeakPartial i (fun x => v k x j) (fun x => w k x i j))
    (hl : ∀ k i j, MemLp (fun x => w k x i j) 2 volume)
    (hd : ∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (orbitalDensity (v k)).matrix x i j) (D.matrix x i j))
    (hk : Summable fun k => n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2) :
    sqrtKinetic S / 2 ≤ ∑' k, n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2 := by
  choose V hV hVi hcost using fun k => singleOrbital_bound chain (v k) (w k) (hw k) (hl k)
  have hb (k) : n k * sqrtKinetic (V k) ≤ 2 * (n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2) :=
    (mul_le_mul_of_nonneg_left (hcost k) (hn k)).trans_eq (by ring)
  have hm := hk.mul_left 2
  have hs := Summable.of_nonneg_of_le (fun k => mul_nonneg (hn k)
    (integral_nonneg (kineticDensity_nonneg (V k)))) hb hm
  have hf := convex D S hD (fun k => orbitalDensity (v k)) V n hn hV hVi hd hs
  have h := hs.tsum_le_tsum hb hm
  rw [tsum_mul_left] at h
  linarith

theorem hoffmann_ostenhof_oneBody (chain : RankOneRootChain d) (convex : CountableFisherConvexity d)
    (γ : OneBody d) (D : Density d) (S : Gradient d) (hD : SqrtRegular D S)
    (hd : γ.matrixDensity =ᵐ[volume] D.matrix) : sqrtKinetic S / 2 ≤ γ.kinetic := by
  apply hoffmann_ostenhof_occupied chain convex D S hD (fun k x j => γ.orbital k j x)
    (fun k x i j => γ.gradient k j i x) γ.occupation (fun k => (γ.occupation_mem k).1)
    (fun k i j => γ.weak k j i) (fun k i j => γ.gradient_L2 k j i) _ γ.finite_kinetic
  filter_upwards [γ.diagonal_summable, hd] with x hx hxe
  intro i j
  rw [← hxe]
  simpa only [orbitalDensity, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, mul_assoc,
    OneBody.matrixDensity, OneBody.kernel] using (hx i j).hasSum

end TSGA.ManyBody.Spatial
