import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.DisjointUnion
import TropicalGeometry.Util.Relation
/-! ... -/

namespace SerreGraph

/- def DisjointUnionGraph (G H : SerreGraph) : SerreGraph where
  X := Sum G.X H.X
  finite := by
    let := G.finite
    let := H.finite
    infer_instance
  root :=  -/

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

lemma respects_gluing
    {G H : PointedSerreGraph}
    {f : DisjointUnionX G H → DisjointUnionX G H}
    (hf : ∀ x y, WedgeSumGen G H x y →
      WedgeSumGen G H (f x) (f y)) :
    ∀ x y, WedgeSumSetoid G H x y →
      WedgeSumSetoid G H (f x) (f y) := by
  apply Relation.respects_eqvGen_setoid
    (WedgeSumGen G H) (WedgeSumSetoid G H) ?_ hf
  rfl

/- lemma root_respects_gluing (G H : PointedSerreGraph) :
    ∀ x y, WedgeSumSetoid G H x y →
      WedgeSumSetoid G H ((DisjointUnion G H).root x) (G.root y) := by
  apply respects_gluing G H
  intro x y h -/

def WedgeSumRoot (G H : PointedSerreGraph) : (WedgeSumX G H) → (WedgeSumX G H) :=
  Quotient.lift
    (Quotient.mk (WedgeSumSetoid G H) ∘ (disjointUnion G.graph H.graph).root)
    (by sorry
    )

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
