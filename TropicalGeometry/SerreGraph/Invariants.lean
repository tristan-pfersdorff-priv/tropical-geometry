import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.Connectedness

namespace SerreGraph

variable {G : SerreGraph}

noncomputable def genusInZ (G : SerreGraph) : ℤ :=
  (nedges G : ℤ) - (nvertices G : ℤ) + nComponents G

noncomputable def genus (G : SerreGraph) : ℕ :=
  Int.toNat (genusInZ G)

-- TODO: prove that genus = genusInZ, also it may be nice to show that genus adds over components
theorem genus_nonneg (G : SerreGraph) : genus G = genusInZ G := by
  sorry

end SerreGraph
