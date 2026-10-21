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

abbrev WedgeSumX (G H : PointedSerreGraph) :=
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
lemma WedgeSumRoot_mk (G H : PointedSerreGraph) (x : DisjointUnionX G H) :
    WedgeSumRoot G H (Quotient.mk (WedgeSumSetoid G H) x) =
      Quotient.mk (WedgeSumSetoid G H) ((disjointUnion G.graph H.graph).root x) := by
  rfl

@[simp]
lemma WedgeSumFlip_mk (G H : PointedSerreGraph) (x : DisjointUnionX G H) :
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

def wedgeSumGraph (G H : PointedSerreGraph) : SerreGraph where
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

def wedgeSum (G H : PointedSerreGraph) : PointedSerreGraph where
  graph := wedgeSumGraph G H
  point := by
    let pval :=
      Quotient.mk (WedgeSumSetoid G H) (Sum.inl G.point.val)
    refine ⟨pval, ?_⟩
    have hvertex :=
      disjointUnion_inl_isVertex
        G.graph H.graph G.point.val G.point.property
    have root_fix_in_sum :=
      (disjointUnion G.graph H.graph).IsVertex_iff
        (Sum.inl G.point.val) |>.mp hvertex
    have root_fix_in_wedge_sum :
      (wedgeSumGraph G H).root pval = pval := by
      unfold pval
      change (WedgeSumRoot G H) ⟦Sum.inl ↑G.point⟧ = ⟦Sum.inl ↑G.point⟧
      rw [WedgeSumRoot_mk G H (Sum.inl G.point.val), root_fix_in_sum]
      rfl
    exact (wedgeSumGraph G H).IsVertex_iff
      pval |>.mpr root_fix_in_wedge_sum

def wedgeSumMap
    (ϕ : G.graph.Hom K)
    (ψ : H.graph.Hom K)
    (hpoint : ϕ G.point.val = ψ H.point.val) :
    WedgeSumX G H → K.X :=
  Quotient.lift (disjointUnionMap ϕ ψ) (by
    apply Relation.eqvGen_map_to_set
    intro x y h
    simp only [h.left, h.right]
    exact hpoint
  )

def wedgeSumHom
    (ϕ : G.graph.Hom K)
    (ψ : H.graph.Hom K)
    (hpoint : ϕ G.point.val = ψ H.point.val) :
    (wedgeSum G H).graph.Hom K where
  toFun := wedgeSumMap ϕ ψ hpoint
  root_comm := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    change (wedgeSumMap ϕ ψ hpoint) (WedgeSumRoot G H ⟦x⟧) = K.root (wedgeSumMap ϕ ψ hpoint ⟦x⟧)
    rw [WedgeSumRoot_mk]
    unfold wedgeSumMap
    change disjointUnionMap ϕ ψ ((disjointUnionRoot G.graph H.graph) x) =
      K.root ((disjointUnionMap ϕ ψ) x)
    unfold disjointUnionMap disjointUnionRoot
    cases x with
      | inl xl =>
        change (ϕ.toFun ∘ G.graph.root) xl = (K.root ∘ ϕ) xl
        rw [ϕ.root_comm]
        rfl
      | inr xr =>
        change (ψ.toFun ∘ H.graph.root) xr = (K.root ∘ ψ) xr
        rw [ψ.root_comm]
        rfl
  flip_comm := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    change (wedgeSumMap ϕ ψ hpoint) (WedgeSumFlip G H ⟦x⟧) = K.flip (wedgeSumMap ϕ ψ hpoint ⟦x⟧)
    rw [WedgeSumFlip_mk]
    unfold wedgeSumMap
    change disjointUnionMap ϕ ψ ((disjointUnionFlip G.graph H.graph) x) =
      K.flip ((disjointUnionMap ϕ ψ) x)
    unfold disjointUnionMap disjointUnionFlip
    cases x with
      | inl xl =>
        change (ϕ.toFun ∘ G.graph.flip) xl = (K.flip ∘ ϕ) xl
        rw [ϕ.flip_comm]
        rfl
      | inr xr =>
        change (ψ.toFun ∘ H.graph.flip) xr = (K.flip ∘ ψ) xr
        rw [ψ.flip_comm]
        rfl

def glueImage (G : PointedSerreGraph) (H : SerreGraph) (ϕ : Hom G.graph H) :
    PointedSerreGraph :=
  let Hpointed : PointedSerreGraph := {
    graph := H
    point := ϕ.toVertex G.point
 }
  wedgeSum G Hpointed

def glueImageHom (G : PointedSerreGraph) (H : SerreGraph) (ϕ : Hom G.graph H) :
    Hom (glueImage G H ϕ).graph H :=
    wedgeSumHom ϕ (Hom.id H) (by rfl)

end SerreGraph
