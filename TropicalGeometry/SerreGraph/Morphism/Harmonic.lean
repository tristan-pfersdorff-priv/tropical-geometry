import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.Hom
import TropicalGeometry.SerreGraph.Morphism.Subharmonic

namespace SerreGraph

variable {G : SerreGraph}

def IsHarmonicOfDeg (ϕ : SubharmonicMorphism G H) (d : ℕ+) : Prop :=
  ∀ v : G.Vertex,
    MultiplicitiesNearVertex ϕ v = (fun _ => d : H.OutgoingLedges ((ϕ : Hom G H).toVertex v) → ℕ)

structure HarmonicMorphism (G H : SerreGraph) where
  toSubharmonic : SubharmonicMorphism G H
  global_deg : ℕ+
  isHarmonic : IsHarmonicOfDeg toSubharmonic global_deg

instance : Coe (HarmonicMorphism G H) (SubharmonicMorphism G H) where
  coe ϕ := ϕ.toSubharmonic

end SerreGraph
