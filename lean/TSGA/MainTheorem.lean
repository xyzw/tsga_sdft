import TSGA.Exponents
import TSGA.LocalEstimate

/-! # The main estimate and its LSDA corollary

`MainTSGAEstimate` contains the two finite-error bounds of `thm:LSSWA` and a
strengthening under a positive minority-density bound. The proof from the finite
tile comparisons is `TSGA.tsga_theorem` in `TSGA/TSGATheorem.lean`.
The corollary `mainLSDA_of_mainTSGA` specializes the general and positive-minority bounds to zero phase.
-/

namespace TSGA

open MeasureTheory

/-- Alternative estimate `eq:LSSWA_sharp_bulk`. The same field `G` represents
the weak gradient of the matrix root on all of space and on the active set.
The bulk exponent in `tsgaError` is now `2p − 1`. The extra term is the
unweighted integral of the global root gradient with that same coefficient. -/
def SharpTSGAEstimate (F : GasEnergies) (p θ C : ℝ) : Prop :=
  ∀ (D : Density) (S T G : MatrixGradient), DensityRegular D p θ S T →
    IsMatrixGradientOn Set.univ (D.power (1 / p)) G →
    MemLp (matrixGradNorm G) (ENNReal.ofReal p) →
    ∀ (φ : Phase), PhaseAdmissible D p φ G → ∀ ε : ℝ, 0 < ε →
      Integrable (fun x => F.ssw (D.matrix x) (φ.grad x)) ∧
      |F.energy (fun x => rotate (φ.value x) (D.matrix x)) -
        ∫ x, F.ssw (D.matrix x) (φ.grad x)| ≤
        tsgaError D φ S T G p (2 * p - 1) C ε +
        C / ε ^ (2 * p - 1) * (∫ x, matrixGradNorm G x ^ p)

/-- The parameter-quantified TSGA theorem. All three constants are uniform in
the density, the phase and `ε`. The sharp estimate also has the same constant
for every admissible `θ` at a fixed `p`. -/
structure MainTSGAEstimate (F : GasEnergies) : Prop where
  general : ∀ p θ : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p * θ →
    ∃ C > 0, TSGAEstimate F (fun _ => True) p θ (bulkExponent p θ) C
  minority : ∀ p θ ν : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p * θ →
    0 < ν → ν ≤ 1 / 2 → ∃ C > 0,
      TSGAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C
  sharp : ∀ p : ℝ, 3 < p → ∃ C > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ →
    SharpTSGAEstimate F p θ C

/-- The noncollinear LSDA corollary and its positive-minority strengthening. Each constant is the one from the corresponding
TSGA estimate. -/
theorem mainLSDA_of_mainTSGA {F : GasEnergies} (h : MainTSGAEstimate F)
    {p θ : ℝ} (hp : 3 < p) (hθlower : 2 / p ≤ θ) (hθupper : θ < 1) :
    (∃ C > 0, LSDAEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∀ ν : ℝ, 0 < ν → ν ≤ 1 / 2 → ∃ C > 0,
      LSDAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) := by
  have hp₀ : 0 < p := by linarith
  have hθ₀ : 0 < θ := (div_pos (by norm_num : 0 < (2 : ℝ)) hp₀).trans_le hθlower
  have hpθ : 2 ≤ p * θ := by
    simpa only [mul_comm θ p] using (div_le_iff₀ hp₀).1 hθlower
  constructor
  · obtain ⟨C, hC, hestimate⟩ := h.general p θ hp hθ₀ hθupper hpθ
    exact ⟨C, hC, lsda_of_tsga hp₀ hestimate⟩
  · intro ν hν hνupper
    obtain ⟨C, hC, hestimate⟩ := h.minority p θ ν hp hθ₀ hθupper hpθ hν hνupper
    exact ⟨C, hC, lsda_of_tsga hp₀ hestimate⟩

end TSGA
