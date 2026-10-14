import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.Hom
/-! ... -/

namespace SerreGraph

variable {G : SerreGraph}

structure SubharmonicMorphism (G H : SerreGraph) where
  toHom : Hom G H
  non_contracting : IsNonContracting toHom
  local_deg : G.Ledge → ℕ+

instance : Coe (SubharmonicMorphism G H) (Hom G H) where
  coe ϕ := ϕ.toHom

noncomputable def MultiplicitiesNearVertex (ϕ : SubharmonicMorphism G H) (v : G.Vertex) :
  H.OutgoingLedges ((ϕ : Hom G H).toVertex v) → ℕ :=
    letI := G.finite
    fun b =>
      let ledgesOverb := {a' : G.OutgoingLedges v // ϕ.toHom (Ledge.val a'.val) = Ledge.val b.val}
      letI : Fintype ledgesOverb := Fintype.ofFinite _
      ∑ a : ledgesOverb,
        (ϕ.local_deg a.val : ℕ)

end SerreGraph
