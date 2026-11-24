import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Thermodynamic limit for direction-averaged spiral tetrahedra

For one fixed spin matrix and wavevector, `tile ℓ δ` denotes the averaged
energy per unit volume of a tetrahedron of side length `ℓ` smoothed at
length `δ`. The comparison is applied first at a fixed inner scale, then
with the inner scale tending to infinity, as in Step 1 of `thm:spiral_limit`.
-/

namespace TSGA.SSW

open Filter
open scoped Topology

/-- The Lieb–Oxford lower bound and kinetic upper bound of
`eq:bounds_tetrahedron_spiral`, at fixed density and wavevector. -/
def TileBounds (tile : ℝ → ℝ → ℝ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ℓ δ : ℝ, 0 < ℓ → 0 < δ →
    -A ≤ tile ℓ δ ∧ tile ℓ δ ≤ B + B / (ℓ * δ)

private theorem TileBounds.bound_of_smoothing_ge {tile : ℝ → ℝ → ℝ}
    (h : TileBounds tile) {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ δ : ℝ, d ≤ δ → |tile ℓ δ| ≤ K := by
  obtain ⟨A, B, _, hB, htile⟩ := h
  refine ⟨max A (B + B / d), ?_⟩
  intro ℓ hℓ δ hδ
  have hδpos : 0 < δ := hd.trans_le hδ
  obtain ⟨hlo, hhi⟩ := htile ℓ δ (zero_lt_one.trans_le hℓ) hδpos
  have hden : d ≤ ℓ * δ := hδ.trans (le_mul_of_one_le_left hδpos.le hℓ)
  exact abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans hlo,
    (hhi.trans (add_le_add le_rfl (div_le_div_of_nonneg_left hB hd hden))).trans
      (le_max_right _ _)⟩

/-- The bounds are uniform in all sufficiently large tiles at fixed smoothing. -/
theorem TileBounds.eventually_bounded {tile : ℝ → ℝ → ℝ} (h : TileBounds tile)
    (δ : ℝ) (hδ : 0 < δ) : ∃ B : ℝ, ∀ᶠ ℓ in atTop, |tile ℓ δ| ≤ B := by
  obtain ⟨K, hK⟩ := h.bound_of_smoothing_ge hδ
  exact ⟨K, (eventually_ge_atTop (1 : ℝ)).mono fun ℓ hℓ => hK ℓ hℓ δ le_rfl⟩

/-- One constant dominates the scale average in Step 3 for all large tiles. -/
theorem TileBounds.uniform_bound {tile : ℝ → ℝ → ℝ} (h : TileBounds tile) :
    ∃ B : ℝ, ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ t ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), |tile ℓ t| ≤ B := by
  obtain ⟨K, hK⟩ := h.bound_of_smoothing_ge (half_pos (zero_lt_one : (0 : ℝ) < 1))
  exact ⟨K, fun ℓ hℓ t ht => hK ℓ hℓ t ht.1⟩

/-- The two finite-scale estimates used for tetrahedra. In the second field
the constant can depend on both fixed smoothing lengths. The error displayed
here follows by bounding the inner energy in `eq:two_scales_spiral`. -/
structure TileComparison (tile : ℝ → ℝ → ℝ) : Prop where
  bounded : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ᶠ ℓ in atTop, |tile ℓ δ| ≤ B
  twoScale : ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ ℓ in atTop, ∀ᶠ L in atTop,
      tile ℓ δ - (C / ℓ + C * (ℓ + δ + δ') / L) ≤ tile L δ'

/-- The candidate energy density uses a reference smoothing of one. -/
noncomputable def tileLimit (tile : ℝ → ℝ → ℝ) : ℝ :=
  limsup (fun ℓ => tile ℓ 1) atTop

variable {tile : ℝ → ℝ → ℝ}

/-- The manuscript's two-scale estimate, before absorbing the inner energy
into a constant. Here `c` is the geometric constant, `k` the offset in the
Lieb–Oxford bound, `d` the boundary coefficient and `m / ℓ` the remaining
localization error at fixed smoothing lengths. -/
theorem TileComparison.of_two_scales
    (hb : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ᶠ ℓ in atTop, |tile ℓ δ| ≤ B)
    (hraw : ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → ∃ c k d m : ℝ, 0 ≤ c ∧
      ∀ᶠ ℓ in atTop, ∀ᶠ L in atTop,
        tile ℓ δ - c * (δ / ℓ + (ℓ + δ + δ') / L) * (tile ℓ δ + k) -
          d * ((ℓ + δ + δ') / L) - m / ℓ ≤ tile L δ') :
    TileComparison tile := by
  refine ⟨hb, ?_⟩
  intro δ δ' hδ hδ'
  obtain ⟨B, hB⟩ := hb δ hδ
  obtain ⟨c, k, d, m, hc, hcomparison⟩ := hraw δ δ' hδ hδ'
  let A := c * δ * (B + k) + m
  let D := c * (B + k) + d
  let C := max 0 (max A D)
  have hA : A ≤ C := (le_max_left A D).trans (le_max_right 0 _)
  have hD : D ≤ C := (le_max_right A D).trans (le_max_right 0 _)
  refine ⟨C, le_max_left 0 _, ?_⟩
  filter_upwards [hB, hcomparison, eventually_gt_atTop (0 : ℝ)] with ℓ hℓ hcomp hℓpos
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with L hL hLpos
  let t := (ℓ + δ + δ') / L
  have ht : 0 ≤ t := div_nonneg (by linarith) hLpos.le
  have hfactor : 0 ≤ c * (δ / ℓ + t) := mul_nonneg hc (add_nonneg (div_nonneg hδ.le hℓpos.le) ht)
  have hinner := mul_le_mul_of_nonneg_left (add_le_add (abs_le.mp hℓ).2 (le_refl k)) hfactor
  have herr : c * (δ / ℓ + t) * (tile ℓ δ + k) + d * t + m / ℓ ≤
      C / ℓ + C * t := by
    calc
      _ ≤ c * (δ / ℓ + t) * (B + k) + d * t + m / ℓ := by linarith
      _ = A / ℓ + D * t := by unfold A D; ring
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hA hℓpos.le) (mul_le_mul_of_nonneg_right hD ht)
  change tile ℓ δ - c * (δ / ℓ + t) * (tile ℓ δ + k) - d * t - m / ℓ ≤ tile L δ' at hL
  rw [mul_div_assoc C]
  change tile ℓ δ - (C / ℓ + C * t) ≤ tile L δ'
  linarith

private theorem TileComparison.bounded_above_below (h : TileComparison tile)
    {δ : ℝ} (hδ : 0 < δ) :
    (atTop.IsBoundedUnder (· ≤ ·) (fun ℓ => tile ℓ δ)) ∧
    (atTop.IsBoundedUnder (· ≥ ·) (fun ℓ => tile ℓ δ)) := by
  obtain ⟨B, hB⟩ := h.bounded δ hδ
  exact ⟨⟨B, hB.mono fun _ hℓ => (abs_le.mp hℓ).2⟩,
    ⟨-B, hB.mono fun _ hℓ => (abs_le.mp hℓ).1⟩⟩

/-- Taking the outer and inner length to infinity in order compares different
smoothing lengths. No convergence of the tile energies is needed here. -/
theorem TileComparison.limsup_le_liminf (h : TileComparison tile) {δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') :
    limsup (fun ℓ => tile ℓ δ) atTop ≤ liminf (fun L => tile L δ') atTop := by
  obtain ⟨C, _, hcomp⟩ := h.twoScale δ δ' hδ hδ'
  have hi := (h.bounded_above_below hδ).2.isCoboundedUnder_le
  have ho := (h.bounded_above_below hδ').1.isCoboundedUnder_ge
  apply le_of_forall_pos_le_add
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have small (b : ℝ) : ∀ᶠ x : ℝ in atTop, b / x < ε / 2 :=
    (tendsto_id.const_div_atTop b).eventually_lt_const hhalf
  apply limsup_le_of_le hi
  filter_upwards [hcomp, small C] with ℓ hℓ hsmall
  have hlower : tile ℓ δ - ε ≤ liminf (fun L => tile L δ') atTop := by
    apply le_liminf_of_le ho
    filter_upwards [hℓ, small (C * (ℓ + δ + δ'))] with L hL hboundary
    linarith
  linarith

/-- The averaged tetrahedron energy has the same limit for every fixed
positive smoothing length, as its real side length tends to infinity. -/
theorem TileComparison.tendsto (h : TileComparison tile) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ℓ => tile ℓ δ) atTop (𝓝 (tileLimit tile)) := by
  obtain ⟨hupper, hlower⟩ := h.bounded_above_below hδ
  obtain ⟨hupper₁, hlower₁⟩ := h.bounded_above_below zero_lt_one
  exact tendsto_of_le_liminf_of_limsup_le
    (h.limsup_le_liminf zero_lt_one hδ)
    ((h.limsup_le_liminf hδ zero_lt_one).trans (liminf_le_limsup hupper₁ hlower₁))
    hupper hlower

/-- Symmetries of the averaged tile at reference smoothing pass to its limit.
Eventual equality is sufficient. -/
theorem tileLimit_congr {s t : ℝ → ℝ → ℝ}
    (heq : ∀ᶠ ℓ in atTop, s ℓ 1 = t ℓ 1) : tileLimit s = tileLimit t :=
  limsup_congr heq

end TSGA.SSW
