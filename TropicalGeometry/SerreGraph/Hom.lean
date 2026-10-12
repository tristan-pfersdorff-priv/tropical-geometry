import TropicalGeometry.SerreGraph.Basic

namespace SerreGraph

variable {G H : SerreGraph}

structure Hom (G H : SerreGraph) where
  toFun : G.X → H.X
  root_comm : toFun ∘ G.root = H.root ∘ toFun
  flip_comm : toFun ∘ G.flip = H.flip ∘ toFun

instance {G H : SerreGraph} : FunLike (Hom G H) G.X H.X where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simp_all

def Hom.id (G : SerreGraph) : Hom G G where
  toFun := fun x : G.X => x
  root_comm := by rfl
  flip_comm := by rfl

def Hom.comp {G H K : SerreGraph} (f : Hom G H) (g : Hom H K) : Hom G K where
  toFun := g.toFun ∘ f.toFun
  root_comm := by
    rw [Function.comp_assoc]
    rw [f.root_comm]
    rw [← Function.comp_assoc]
    rw [g.root_comm]
    rw [Function.comp_assoc]
  flip_comm := by
    rw [Function.comp_assoc]
    rw [f.flip_comm]
    rw [← Function.comp_assoc]
    rw [g.flip_comm]
    rw [Function.comp_assoc]

def IsIso {G H : SerreGraph} (f : Hom G H) : Prop :=
  ∃ g : Hom H G,
    g.toFun ∘ f.toFun = id ∧
    f.toFun ∘ g.toFun = id

structure Iso (G H : SerreGraph) where
  hom : Hom G H
  isIso : IsIso hom

@[ext]
lemma Iso.ext {f g : Iso G H}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp_all

noncomputable def Iso.inv (f : Iso G H) : Hom H G :=
  Classical.choose f.isIso

lemma Iso.left_inv (f : Iso G H) :
    f.inv.toFun ∘ f.hom.toFun = id :=
  (Classical.choose_spec f.isIso).1

lemma Iso.right_inv (f : Iso G H) :
    f.hom.toFun ∘ f.inv.toFun = id :=
  (Classical.choose_spec f.isIso).2

def Hom.toVertex (f : Hom G H) : Vertex G → Vertex H :=
  fun v => ⟨f v.val, by
  rcases v.property with ⟨x, hx⟩
  refine ⟨f x, ?_⟩
  change (H.root ∘ f.toFun) x = f v.val
  rw [← f.root_comm]
  change f.toFun (G.root x) = f v.val
  rw [hx]
  rfl⟩

def fiber (f : Hom G H) (v : H.Vertex) : SerreGraph where
  X := {a : G.X // f a = v}
  finite := by
    let := G.finite
    infer_instance
  root := fun x => ⟨G.root x, by
    change (f.toFun ∘ G.root) x = v
    rw [f.root_comm]
    change H.root (f.toFun x) = v
    change H.root (f x) = v
    rw [x.property]
    rw [←IsVertex_iff v.val]
    exact v.property
  ⟩
  flip := fun x => ⟨G.flip x, by
    change (f.toFun ∘ G.flip) x = v
    rw [f.flip_comm]
    change H.flip (f.toFun x) = v
    change H.flip (f x) = v
    rw [x.property]
    exact flip_eq_self_of_isVertex v
  ⟩
  root_idem := by
    funext x
    apply Subtype.ext
    exact congrFun G.root_idem x.val
  flip_invo := by
    funext x
    apply Subtype.ext
    change G.flip (G.flip x.val) = x.val
    exact congrFun G.flip_invo x.val
  flip_root := by
    funext x
    apply Subtype.ext
    change G.flip (G.root x.val) = G.root x.val
    exact congrFun G.flip_root x.val

def IsNonContracting (f : Hom G H) : Prop :=
  --∀ e : G.X, IsEdge e → IsEdge (f e) -- also a decent version
  ∀ e : G.Edge, IsEdge (f e)

end SerreGraph
