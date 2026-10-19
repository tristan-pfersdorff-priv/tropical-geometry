import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.DisjointUnion
import TropicalGeometry.SerreGraph.Hom
import TropicalGeometry.Util.Relation
/-! ... -/

namespace SerreGraph

structure PointedSerreGraph where
  graph : SerreGraph
  point : graph.Vertex

variable {G H : PointedSerreGraph}

abbrev DisjointUnionX (G H : PointedSerreGraph) :=
  (disjointUnion G.graph H.graph).X

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

lemma root_respects_gluing (G H : PointedSerreGraph) :
    ∀ x y, WedgeSumSetoid G H x y →
      WedgeSumSetoid G H
        ((disjointUnion G.graph H.graph).root x)
        ((disjointUnion G.graph H.graph).root y) := by
  apply respects_gluing
  intro x y h
  rcases h with ⟨hx, hy⟩
  constructor
  · rw [hx]
    have hvertex : (disjointUnion G.graph H.graph).IsVertex
        (Sum.inl G.point.val) := by
      exact disjointUnion_inl_isVertex
        G.graph H.graph G.point.val G.point.property
    exact (disjointUnion G.graph H.graph).IsVertex_iff
      (Sum.inl G.point.val) |>.mp hvertex
  · rw [hy]
    have hvertex : (disjointUnion G.graph H.graph).IsVertex
        (Sum.inr H.point.val) := by
      exact disjointUnion_inr_isVertex
        G.graph H.graph H.point.val H.point.property
    exact (disjointUnion G.graph H.graph).IsVertex_iff
      (Sum.inr H.point.val) |>.mp hvertex

lemma flip_respects_gluing (G H : PointedSerreGraph) :
    ∀ x y, WedgeSumSetoid G H x y →
      WedgeSumSetoid G H
        ((disjointUnion G.graph H.graph).flip x)
        ((disjointUnion G.graph H.graph).flip y) := by
  apply respects_gluing
  intro x y h
  rcases h with ⟨hx, hy⟩
  constructor
  · rw [hx]
    have hvertex : (disjointUnion G.graph H.graph).IsVertex
        (Sum.inl G.point.val) := by
      exact disjointUnion_inl_isVertex
        G.graph H.graph G.point.val G.point.property
    exact (disjointUnion G.graph H.graph).flip_eq_self_of_isVertex ⟨Sum.inl G.point, hvertex⟩
  · rw [hy]
    have hvertex : (disjointUnion G.graph H.graph).IsVertex
        (Sum.inr H.point.val) := by
      exact disjointUnion_inr_isVertex
        G.graph H.graph H.point.val H.point.property
    exact (disjointUnion G.graph H.graph).flip_eq_self_of_isVertex ⟨Sum.inr H.point, hvertex⟩

-- flip_eq_self_of_isVertex

def WedgeSumRoot (G H : PointedSerreGraph) : (WedgeSumX G H) → (WedgeSumX G H) :=
  Relation.liftQuotient
    (WedgeSumSetoid G H)
    (disjointUnion G.graph H.graph).root
    (root_respects_gluing G H)

def WedgeSumFlip (G H : PointedSerreGraph) : (WedgeSumX G H) → (WedgeSumX G H) :=
  Relation.liftQuotient
    (WedgeSumSetoid G H)
    (disjointUnion G.graph H.graph).flip
    (flip_respects_gluing G H)

@[simp]
lemma WedgeSumRoot_mk (G H : PointedSerreGraph) (x : (disjointUnion G.graph H.graph).X) :
    WedgeSumRoot G H (Quotient.mk (WedgeSumSetoid G H) x) =
      Quotient.mk (WedgeSumSetoid G H) ((disjointUnion G.graph H.graph).root x) := by
  rfl

@[simp]
lemma WedgeSumFlip_mk (G H : PointedSerreGraph) (x : (disjointUnion G.graph H.graph).X) :
    WedgeSumFlip G H (Quotient.mk (WedgeSumSetoid G H) x) =
      Quotient.mk (WedgeSumSetoid G H) ((disjointUnion G.graph H.graph).flip x) := by
  rfl

lemma WedgeSumRoot_idem (G H : PointedSerreGraph) :
    WedgeSumRoot G H ∘ WedgeSumRoot G H = WedgeSumRoot G H := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [WedgeSumRoot_mk]
  apply congrArg (Quotient.mk (WedgeSumSetoid G H))
  exact congrFun (disjointUnion G.graph H.graph).root_idem x

lemma WedgeSumFlip_invo (G H : PointedSerreGraph) :
    WedgeSumFlip G H ∘ WedgeSumFlip G H = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change WedgeSumFlip G H (WedgeSumFlip G H (Quotient.mk (WedgeSumSetoid G H) x))
      = Quotient.mk (WedgeSumSetoid G H) x
  rw [WedgeSumFlip_mk]
  apply congrArg (Quotient.mk (WedgeSumSetoid G H))
  simpa using congrFun (disjointUnion G.graph H.graph).flip_invo x

lemma WedgeSumFlip_root (G H : PointedSerreGraph) :
    WedgeSumFlip G H ∘ WedgeSumRoot G H = WedgeSumRoot G H := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [WedgeSumRoot_mk]
  apply congrArg (Quotient.mk (WedgeSumSetoid G H))
  exact congrFun (disjointUnion G.graph H.graph).flip_root x

def wedgeSum (G H : PointedSerreGraph) : SerreGraph where
  X := WedgeSumX G H
  finite := by
    let := (disjointUnion G.graph H.graph).finite
    unfold WedgeSumX
    infer_instance
  root := WedgeSumRoot G H
  flip := WedgeSumFlip G H
  root_idem := WedgeSumRoot_idem G H
  flip_invo := WedgeSumFlip_invo G H
  flip_root := WedgeSumFlip_root G H

def glueImageGraph (G : PointedSerreGraph) (H : SerreGraph) (ϕ : Hom G.graph H) : PointedSerreGraph :=
  wedgeSum G
  (PointedSerreGraph where
    graph := H
    point := ϕ.toVertex G.point)

end SerreGraph
