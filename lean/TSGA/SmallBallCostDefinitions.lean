import TSGA.IslandInteriorTrial

/-! # Scalar costs of the two island additions and the local rotations -/

noncomputable section
namespace TSGA.ManyBody
/-- The upper bounds for the spatial integrals in the cost of differentiating
the tapered, rotated square root. V is the cell volume scale and J bounds the
Fisher integral of its taper. -/
def smallAffineCost (V J k Q α cap : ℝ) : ℝ := 8*(α*k+cap*J)+2*Q^2*cap*V

def smallAdditionCost (C ε V J k Q r dist : ℝ) : ℝ :=
  let bg := smallAffineCost V J k Q 1 (2*r)
  let mixed := smallAffineCost V J k Q ε⁻¹ (2*dist+ε*(2*r))
  (12*C+2*C^2)*(3*ε*((2*r+(2*r)^2)*V+bg) + mixed +
    3*(ε+√(2*dist/ε)+2*dist/ε)*(2*dist*V))

/-- The unnormalized island and gauge errors on one oriented window. -/
def smallReplacementCost (H : FiniteEnergyInputs) (C ε V J k Q r dist d p v : ℝ) : ℝ :=
  let bg := smallAffineCost V J k Q 1 (2*r)
  let base := (H.interiorConstant+H.loCoeff)*((r+r^2)*V) + H.interiorConstant*bg
  let axes := 2*192^2*k + (2*r*Q^2*((96/(1/p))*d)^2)*V
  let phase := v^2/4*(r*V)
  smallAdditionCost C ε V J k Q r dist + 6*ε*base+(8/ε)*(axes+phase)

end TSGA.ManyBody
