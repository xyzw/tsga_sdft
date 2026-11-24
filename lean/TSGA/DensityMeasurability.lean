import TSGA.Sobolev
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # Measurability of the original matrix field from its weak square root -/

namespace TSGA

open MeasureTheory
open scoped ComplexOrder

theorem Density.sqrt_mul_self (D : Density) (x : Position) :
    D.power (1/2) x * D.power (1/2) x = D.matrix x := by
  let h := (D.positive x).isHermitian
  change h.cfc _ * h.cfc _ = _
  rw [Matrix.IsHermitian.cfc, ← map_mul, Matrix.diagonal_mul_diagonal]
  conv_rhs => rw [h.spectral_theorem]
  apply congrArg _
  congr 1
  funext i
  simp only [Function.comp_apply, ← Real.sqrt_eq_rpow]
  exact_mod_cast Real.mul_self_sqrt ((D.positive x).eigenvalues_nonneg i)

theorem DensityRegular.aemeasurable_matrix {D : Density} {p θ : ℝ} {S T : MatrixGradient}
    (h : DensityRegular D p θ S T) : AEMeasurable D.matrix volume := by
  have hs (i j : Fin 2) : AEMeasurable (fun x => D.power (1/2) x i j) volume :=
    (locallyIntegrableOn_univ.mp (h.sqrt_gradient 0 i j).1).aestronglyMeasurable.aemeasurable
  have hm (i j : Fin 2) : AEMeasurable (fun x => D.matrix x i j) volume := by
    have he (x : Position) : D.matrix x i j = ∑ k, D.power (1/2) x i k * D.power (1/2) x k j :=
      congrArg (fun M : SpinMatrix => M i j) (D.sqrt_mul_self x).symm
    simp_rw [he]
    exact Finset.aemeasurable_fun_sum _ fun k _ => (hs i k).mul (hs k j)
  exact aemeasurable_pi_lambda _ fun i => aemeasurable_pi_lambda _ (hm i)

end TSGA
