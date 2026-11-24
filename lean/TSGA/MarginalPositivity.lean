import TSGA.LevyLieb
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Positivity of many-body spin marginals

Fubini gives square-integrable first-coordinate slices almost everywhere.
On that set the spin marginal is a finite positive sum of Gram matrices in
`L²`. Closing the positive cone under limits gives positivity for the
countable ensemble.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Filter
open scoped ComplexOrder ComplexConjugate Topology

/-- Separate the first position from the other particle coordinates under
product Lebesgue measure. -/
private theorem cons_preserves_volume (n : ℕ) :
    MeasurePreserving (fun p : Position × Space n => Fin.cons p.1 p.2)
      (volume.prod volume) (volume : Measure (Space (n + 1))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Position) 0
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Position) 0).symm e
  have he : (fun p : Position × Space n => Fin.cons p.1 p.2) = e.symm := by
    funext p
    exact (Fin.insertNth_zero' p.1 p.2).symm
  rw [he]
  exact h

/-- The good spatial set is common to all finitely many spin indices. -/
theorem Wave.square_integrable_slices {n : ℕ} (ψ : Wave (n + 1)) :
    ∀ᵐ x : Position, ∀ i : Fin 2, ∀ s : Spins n,
      MemLp (fun y : Space n => ψ.value (Fin.cons i s) (Fin.cons x y)) 2 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro s
  let f (p : Position × Space n) := ψ.value (Fin.cons i s) (Fin.cons p.1 p.2)
  have h : MemLp f 2 (volume.prod volume) :=
    (ψ.square_integrable (Fin.cons i s)).comp_measurePreserving (cons_preserves_volume n)
  have hs := (h.integrable_norm_pow (p := 2) (by decide)).prod_right_ae
  filter_upwards [hs, h.aestronglyMeasurable.prodMk_left] with x hsq hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hsq

/-- A spin block of the marginal is the transpose of the `L²` Gram matrix
in the convention `ψᵢ conj ψⱼ`. -/
private theorem gram_integral_posSemidef {n : ℕ} (v : Fin 2 → Space n → ℂ)
    (hv : ∀ i, MemLp (v i) 2) :
    (Matrix.of fun i j => ∫ y, v i y * conj (v j y)).PosSemidef := by
  let V (i : Fin 2) := (hv i).toLp (v i)
  have hmatrix : (Matrix.of fun i j => ∫ y, v i y * conj (v j y)) = (Matrix.gram ℂ V).transpose := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply, L2.inner_def, RCLike.inner_apply]
    apply integral_congr_ae
    filter_upwards [(hv i).coeFn_toLp, (hv j).coeFn_toLp] with y hi hj
    rw [show V i y = v i y from hi, show V j y = v j y from hj]
  rw [hmatrix]
  exact (Matrix.posSemidef_gram ℂ V).transpose

theorem Wave.matrixDensity_posSemidef {n : ℕ} (ψ : Wave (n + 1)) :
    ∀ᵐ x : Position, (ψ.matrixDensity x).PosSemidef := by
  filter_upwards [ψ.square_integrable_slices] with x hx
  let block (s : Spins n) : SpinMatrix := Matrix.of fun i j => ∫ y : Space n,
    ψ.value (Fin.cons i s) (Fin.cons x y) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))
  have hblock (s : Spins n) : (block s).PosSemidef :=
    gram_integral_posSemidef _ (fun i => hx i s)
  have hmatrix : ψ.matrixDensity x = ((n + 1 : ℕ) : ℝ) • ∑ s, block s := by
    ext i j
    simp [Wave.matrixDensity, block, Matrix.sum_apply, Complex.real_smul]
  rw [hmatrix]
  exact (Matrix.posSemidef_sum _ (fun s _ => hblock s)).smul (by positivity)

theorem PureState.matrixDensity_posSemidef (s : PureState) :
    ∀ᵐ x : Position, (s.matrixDensity x).PosSemidef := by
  cases s with
  | vacuum => exact ae_of_all _ (fun _ => Matrix.PosSemidef.zero)
  | occupied ψ => exact ψ.matrixDensity_posSemidef

theorem MixedState.matrixDensity_posSemidef (Γ : MixedState) :
    ∀ᵐ x : Position, (Γ.matrixDensity x).PosSemidef := by
  have hpos : ∀ᵐ x : Position, ∀ k, ((Γ.component k).matrixDensity x).PosSemidef :=
    ae_all_iff.mpr fun k => (Γ.component k).matrixDensity_posSemidef
  filter_upwards [hpos, Γ.density_summable] with x hx hsum
  let B (k : ℕ) : SpinMatrix := Γ.weight k • (Γ.component k).matrixDensity x
  have hB (k : ℕ) : (B k).PosSemidef := (hx k).smul (Γ.weight_nonneg k)
  have hlim : HasSum B (Γ.matrixDensity x) := by
    apply Pi.hasSum.mpr
    intro i
    apply Pi.hasSum.mpr
    intro j
    exact (hsum i j).hasSum
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hlim
    (Eventually.of_forall fun s => Matrix.posSemidef_sum s (fun k _ => hB k))

/-- A pointwise positive representative of the actual countable marginal. -/
def MixedState.density (Γ : MixedState) : Density := by
  classical
  exact ⟨fun x => if (Γ.matrixDensity x).PosSemidef then Γ.matrixDensity x else 0,
    fun x => by split <;> first | assumption | exact Matrix.PosSemidef.zero⟩

theorem MixedState.feasible_density (Γ : MixedState) : feasible Γ.density.matrix Γ := by
  classical
  filter_upwards [Γ.matrixDensity_posSemidef] with x hx
  simp [MixedState.density, hx]

end TSGA.ManyBody
