import TSGA.AxialKinetic
import TSGA.ActualTileEnergy

/-! # Localization domain from the representability assumptions

In three dimensions an `H¹` matrix field is in `L⁴`. For the positive
square root the fourth power of its Hilbert–Schmidt norm is the charge squared.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization

/-- The standard `H¹(ℝ³) ⊂ L⁴(ℝ³)` embedding for finite-dimensional
Hilbert–Schmidt matrix fields, written using squared norms. -/
def MatrixSobolevEmbeddingFour : Prop := ∀ (M : Position → SpinMatrix) (S : MatrixGradient),
  IsMatrixGradientOn Set.univ M S → Integrable (fun x => ∑ j, ∑ k, ‖M x j k‖^2) →
  MemLp (matrixGradNorm S) 2 → Integrable (fun x => (∑ j, ∑ k, ‖M x j k‖^2)^2)

theorem tileDensityDomain_of_representable (embed : MatrixSobolevEmbeddingFour)
    {D : Density} {S : MatrixGradient} (h : SqrtRegular D S) : TileDensityDomain D S := by
  have hs (i j : Fin 2) : AEMeasurable (fun x => D.power (1/2) x i j) volume :=
    (locallyIntegrableOn_univ.mp (h.weak 0 i j).1).aestronglyMeasurable.aemeasurable
  have hm (i j : Fin 2) : AEMeasurable (fun x => D.matrix x i j) volume := by
    have eq (x : Position) : D.matrix x i j = ∑ k, D.power (1/2) x i k * D.power (1/2) x k j :=
      congrArg (fun a : SpinMatrix => a i j) (D.sqrt_mul_self x).symm
    simp_rw [eq]
    exact Finset.aemeasurable_fun_sum _ fun k _ => (hs i k).mul (hs k j)
  refine tileDensityDomain_of_regular h (AEMeasurable.of_eval fun i => AEMeasurable.of_eval (hm i)) ?_
  simpa only [sqrt_hilbertSchmidt_sq] using embed (D.power (1/2)) S h.weak
    (by simpa only [sqrt_hilbertSchmidt_sq] using h.charge) h.grad

end TSGA.ManyBody
