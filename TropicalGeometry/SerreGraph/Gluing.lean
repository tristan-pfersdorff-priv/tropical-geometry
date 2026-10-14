import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.DisjointUnion
/-! ... -/

namespace SerreGraph

structure PointedSerreGraph where
  graph : SerreGraph
  point : graph.Vertex

variable {G H : PointedSerreGraph}

abbrev DisjointUnionX (G H : PointedSerreGraph) :=
  Sum G.graph.X H.graph.X

def WedgeSumGen (G H : PointedSerreGraph) :
    DisjointUnionX G H → DisjointUnionX G H → Prop :=
  fun x y =>
    x = Sum.inl G.point.val ∧
    y = Sum.inr H.point.val

def WedgeSumSetoid (G H : PointedSerreGraph) : Setoid (DisjointUnionX G H) :=
  Relation.EqvGen.setoid (WedgeSumGen G H)

def WedgeSumX (G H : PointedSerreGraph) :=
  Quotient (WedgeSumSetoid G H)

def WedgeSumRoot (G H : PointedSerreGraph) : (WedgeSumX G H) → (WedgeSumX G H) :=
  Quotient.lift
    (Quotient.mk (WedgeSumSetoid G H) ∘ (disjointUnion G.graph H.graph).root)
    (by sorry)

def WedgeSumFlip (G H : PointedSerreGraph) : (WedgeSumX G H) → (WedgeSumX G H) :=
  Quotient.lift
    (Quotient.mk (WedgeSumSetoid G H) ∘ (disjointUnion G.graph H.graph).flip)
    (by sorry)

def wedgeSum (G H : PointedSerreGraph) : SerreGraph where
  X := WedgeSumX G H
  finite := by
    let := G.graph.finite
    let := H.graph.finite
    let : Finite (DisjointUnionX G H) := by
      unfold DisjointUnionX
      infer_instance
    unfold WedgeSumX
    infer_instance
  root := WedgeSumRoot G H
  flip := WedgeSumFlip G H
  root_idem := by sorry
  flip_invo := by sorry
  flip_root := by sorry


end SerreGraph
