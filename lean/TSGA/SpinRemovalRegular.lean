import TSGA.FockPartialTrace
import TSGA.CutoffRepresentability

/-! # Spin removal for Sobolev-admissible densities and scalar profiles -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped ComplexOrder MatrixOrder

/-- The first inequality in Lemma E.1 under the square-root density hypothesis. -/
theorem FockPartialTraceSpectralTheorem.levyLieb_spin_removal_of_sqrtRegular
    {F : SectorFourierTransform} (pt : FockPartialTraceSpectralTheorem F) (pl : SectorPlancherelMoments F)
    (H : FiniteEnergyInputs) {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S)
    (B : SpinMatrix) (hB : star B * B ≤ 1) :
    levyLieb (fun x => B * D.matrix x * star B) ≤ levyLieb D.matrix :=
  pt.levyLieb_spin_removal pl (H.representable reg) B hB

/-- The ordered-matrix corollary for every nonnegative scalar profile with square root in H¹. -/
theorem FockPartialTraceSpectralTheorem.energy_ordered_cutoff_of_sqrtH1
    {F : SectorFourierTransform} (pt : FockPartialTraceSpectralTheorem F) (pl : SectorPlancherelMoments F)
    (H : FiniteEnergyInputs) {A B : SpinMatrix} (hA : A.PosSemidef) (hAB : A ≤ B)
    {f : Position → ℝ} (hf : ∀ x, 0 ≤ f x) (root : MemLp (fun x => √(f x)) 2)
    (g : Position → Position) (weak : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (grad : MemLp g 2) :
    energy (fun x => f x • A) ≤ energy (fun x => f x • B) + (B.trace.re^2-A.trace.re^2)*hartree f := by
  have int : Integrable f := by simpa only [Real.sq_sqrt (hf _)] using root.integrable_sq
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans hAB)
  exact pt.energy_ordered_cutoff pl hA hAB f (H.representable_cutoff hf int g weak grad hB)

end TSGA.ManyBody
