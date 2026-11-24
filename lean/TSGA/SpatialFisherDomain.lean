import TSGA.SpatialHoffmannOstenhof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # The H¹ square root of a finite-trace spin density

Countable convexity of the lower semicontinuous matrix Fisher integral
applies to a sum before its square root is known to have a weak gradient.
Finite trace gives the L² norm of the root. The rank-one chain rule gives
the gradient and energy of each orbital in the approximating sum.
-/

noncomputable section
namespace TSGA.ManyBody.Spatial
open MeasureTheory Matrix Filter
open scoped ComplexConjugate ComplexOrder ENNReal Topology

variable {d : ℕ}

/-- The domain-closed version of countable convexity for the extended matrix
Fisher functional on positive fields. The conclusion includes a square-
integrable weak gradient of the limiting square root. -/
def ClosedFisherConvexity (d : ℕ) : Prop :=
  ∀ (D : Density d) (A : ℕ → Density d) (V : ℕ → Gradient d) (n : ℕ → ℝ),
    (∀ k, 0 ≤ n k) → (∀ k, Integrable (A k).charge) →
    Summable (fun k => n k * ∫ x, (A k).charge x) →
    (∀ k, IsMatrixGradient ((A k).power (1/2)) (V k)) →
    (∀ k, Integrable (kineticDensity (V k))) →
    (∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (A k).matrix x i j) (D.matrix x i j)) →
    Summable (fun k => n k * sqrtKinetic (V k)) →
    ∃ S : Gradient d, IsMatrixGradient (D.power (1/2)) S ∧
      MemLp (fun x => √(kineticDensity S x)) 2 ∧ sqrtKinetic S ≤ ∑' k, n k * sqrtKinetic (V k)

private theorem charge_series (D : Density d) (A : ℕ → Density d) (n : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ n k) (hi : ∀ k, Integrable (A k).charge)
    (hm : Summable (fun k => n k * ∫ x, (A k).charge x))
    (hd : ∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (A k).matrix x i j) (D.matrix x i j)) :
    Integrable D.charge ∧ (∫ x, D.charge x) = ∑' k, n k * ∫ x, (A k).charge x := by
  let f := fun k x => n k * (A k).charge x
  have hf (k) : Integrable (f k) := (hi k).const_mul (n k)
  have norm (k x) : ‖f k x‖ = f k x := Real.norm_of_nonneg (mul_nonneg (hn k) ((A k).charge_nonneg x))
  have mass : ∀ᵐ x, HasSum (fun k => f k x) (D.charge x) := by
    filter_upwards [hd] with x hx
    have h := Complex.hasSum_re ((hx 0 0).add (hx 1 1))
    simpa only [f, Density.charge, Matrix.trace_fin_two, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_add] using h
  have absSum : Summable fun k => ∫ x, ‖f k x‖ := by simpa only [norm,f,integral_const_mul] using hm
  have finite : ∑' k, ‖(hf k).toL1 _‖ₑ ≠ ⊤ := by
    simp only [Integrable.enorm_toL1, ← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    exact absSum.tsum_ofReal_ne_top
  have repr : ∀ᵐ x, ∀ k, (hf k).toL1 _ x = f k x := ae_all_iff.mpr fun k => (hf k).coeFn_toL1
  have eq : (fun x => (∑' k, (hf k).toL1 _) x) =ᵐ[volume] D.charge := by
    filter_upwards [Lp.hasSum_coeFn_tsum finite, repr, mass] with x h he hs
    exact (by simpa only [he] using h : HasSum (fun k => f k x) _).unique hs
  refine ⟨(L1.integrable_coeFn _).congr eq, ?_⟩
  rw [integral_congr_ae (mass.mono fun _ h => h.tsum_eq.symm), ← integral_tsum_of_summable_integral_norm hf absSum]
  simp only [f,integral_const_mul]

private theorem root_entries_L2 [NeZero d] (D : Density d) (S : Gradient d) (h : SqrtRegular D S)
    (i j : Fin 2) : MemLp (fun x => D.power (1/2) x i j) 2 volume := by
  have eq (x : Point d) : (∑ l, ∑ m, ‖D.power (1/2) x l m‖^2) = D.charge x :=
    TSGA.Localization.sqrt_hilbertSchmidt_sq (⟨fun _ => D.matrix x, fun _ => D.positive x⟩ : TSGA.Density) 0
  have hs := (h.weak 0 i j).1.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hs).2
  apply h.charge.mono' (hs.norm.pow 2)
  filter_upwards with x
  change ‖‖D.power (1/2) x i j‖^2‖ ≤ D.charge x
  rw [Real.norm_of_nonneg (sq_nonneg _), ← eq]
  calc
    _ ≤ ∑ m, ‖D.power (1/2) x i m‖^2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun l => ∑ m, ‖D.power (1/2) x l m‖^2)
      (fun l _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

private theorem orbital_charge (v : Point d → OrbitalValue) (x : Point d) :
    (orbitalDensity v).charge x = spinSq (v x) := by
  simp [orbitalDensity, Density.charge, spinSq, Fin.sum_univ_two,
    Complex.mul_conj, ← Complex.sq_norm, -Complex.ofReal_pow]

/-- Existence of the H¹ root and the sharp bound for a finite-trace positive
operator with arbitrary nonnegative occupations and finite kinetic energy. -/
theorem hoffmann_ostenhof_occupied_domain [NeZero d]
    (chain : RankOneRootChain d) (closed : ClosedFisherConvexity d) (D : Density d)
    (v : ℕ → Point d → OrbitalValue) (w : ℕ → Point d → Fin d → OrbitalValue) (n : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ n k) (traceFinite : Summable n)
    (orbitals : ∀ k j, MemLp (fun x => v k x j) 2 volume)
    (unit : ∀ k, (∫ x, spinSq (v k x)) = 1)
    (weak : ∀ k i j, WeakPartial i (fun x => v k x j) (fun x => w k x i j))
    (grad : ∀ k i j, MemLp (fun x => w k x i j) 2 volume)
    (hd : ∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (orbitalDensity (v k)).matrix x i j) (D.matrix x i j))
    (hk : Summable fun k => n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2) :
    (∫ x, D.charge x) = ∑' k, n k ∧ ∃ S : Gradient d, SqrtRegular D S ∧
      (∀ i j, MemLp (fun x => D.power (1/2) x i j) 2 volume) ∧
      sqrtKinetic S / 2 ≤ ∑' k, n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2 := by
  let A := fun k => orbitalDensity (v k)
  have hi (k) : Integrable (A k).charge := by
    change Integrable (fun x => (orbitalDensity (v k)).charge x)
    simp_rw [orbital_charge]
    exact integrable_finsetSum _ fun j _ => (orbitals k j).integrable_norm_pow (p := 2) (by decide)
  have mass (k) : (∫ x, (A k).charge x) = 1 := by simpa only [A,orbital_charge] using unit k
  have sumMass : Summable (fun k => n k * ∫ x, (A k).charge x) := by simpa only [mass,mul_one] using traceFinite
  obtain ⟨charge, id⟩ := charge_series D A n hn hi sumMass hd
  choose V hV hVi hE using fun k => singleOrbital_bound chain (v k) (w k) (weak k) (grad k)
  have hb (k) : n k * sqrtKinetic (V k) ≤ 2 * (n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2) :=
    (mul_le_mul_of_nonneg_left (hE k) (hn k)).trans_eq (by ring)
  have hm := hk.mul_left 2
  have hs := Summable.of_nonneg_of_le (fun k => mul_nonneg (hn k) (integral_nonneg (kineticDensity_nonneg (V k)))) hb hm
  obtain ⟨S, hS, l2, bound⟩ := closed D A V n hn hi sumMass hV hVi hd hs
  have reg : SqrtRegular D S := ⟨charge,hS,l2⟩
  refine ⟨by simpa only [mass,mul_one] using id, S, reg, root_entries_L2 D S reg, ?_⟩
  have le := hs.tsum_le_tsum hb hm
  rw [tsum_mul_left] at le
  linarith

/-- A finite-kinetic contraction supplies the spectrum, its trace, and the
almost-everywhere density series. Only weak calculus and closed convexity
of Fisher information remain as inputs. -/
theorem hoffmann_ostenhof_oneBody_domain [NeZero d] (chain : RankOneRootChain d)
    (closed : ClosedFisherConvexity d) (γ : OneBody d) (D : Density d)
    (hd : γ.matrixDensity =ᵐ[volume] D.matrix) :
    (∫ x, D.charge x) = ∑' k, γ.occupation k ∧ ∃ S : Gradient d, SqrtRegular D S ∧
      (∀ i j, MemLp (fun x => D.power (1/2) x i j) 2 volume) ∧ sqrtKinetic S / 2 ≤ γ.kinetic := by
  apply hoffmann_ostenhof_occupied_domain chain closed D (fun k x j => γ.orbital k j x)
    (fun k x i j => γ.gradient k j i x) γ.occupation (fun k => (γ.occupation_mem k).1)
    γ.finite_trace γ.orbital_L2 _ (fun k i j => γ.weak k j i) (fun k i j => γ.gradient_L2 k j i) _ γ.finite_kinetic
  · intro k
    have h := congrArg Complex.re (γ.orthonormal k k)
    have hi (j) := (γ.orbital_L2 k j).integrable_norm_pow (p := 2) (by decide)
    simp only [spinSq, Fin.sum_univ_two, integral_add (hi 0) (hi 1)]
    simpa [Complex.conj_mul', ← Complex.ofReal_pow, integral_complex_ofReal, Fin.sum_univ_two] using h
  · filter_upwards [γ.diagonal_summable, hd] with x hx he
    intro i j
    rw [← he]
    simpa only [orbitalDensity, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, mul_assoc,
      OneBody.matrixDensity, OneBody.kernel] using (hx i j).hasSum

/-- The trace-class series is almost everywhere a positive matrix. -/
theorem OneBody.matrixDensity_posSemidef (γ : OneBody d) : ∀ᵐ x, (γ.matrixDensity x).PosSemidef := by
  filter_upwards [γ.diagonal_summable] with x hx
  let A := fun k => orbitalDensity (fun y j => γ.orbital k j y)
  let B := fun k => γ.occupation k • (A k).matrix x
  have hlim : HasSum B (γ.matrixDensity x) := by
    refine Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => ?_
    simpa only [B,A,Matrix.smul_apply,Complex.real_smul,orbitalDensity,Matrix.vecMulVec_apply,
      Pi.star_apply,Complex.star_def,mul_assoc,OneBody.matrixDensity,OneBody.kernel] using (hx i j).hasSum
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hlim (Eventually.of_forall fun t =>
    Matrix.posSemidef_sum t (fun k _ => ((A k).positive x).smul (γ.occupation_mem k).1))

/-- Positive representative of the diagonal of the natural-orbital kernel. -/
def OneBody.density (γ : OneBody d) : Density d := by
  classical
  exact ⟨fun x => if (γ.matrixDensity x).PosSemidef then γ.matrixDensity x else 0,
    fun x => by split <;> first | assumption | exact Matrix.PosSemidef.zero⟩

/-- Lemma 2.1, including the H¹ conclusion for the operator's own density. -/
theorem OneBody.hoffmann_ostenhof [NeZero d] (γ : OneBody d)
    (chain : RankOneRootChain d) (closed : ClosedFisherConvexity d) :
    (∫ x, γ.density.charge x) = ∑' k, γ.occupation k ∧ ∃ S : Gradient d, SqrtRegular γ.density S ∧
      (∀ i j, MemLp (fun x => γ.density.power (1/2) x i j) 2 volume) ∧ sqrtKinetic S / 2 ≤ γ.kinetic := by
  classical
  apply hoffmann_ostenhof_oneBody_domain chain closed γ γ.density
  filter_upwards [γ.matrixDensity_posSemidef] with x hx
  simp [OneBody.density,hx]

end TSGA.ManyBody.Spatial
