import TropicalGeometry.SerreGraph.Basic
import TropicalGeometry.SerreGraph.Hom
/-! ... -/

namespace SerreGraph

variable {G : SerreGraph}

def ContractGen (e : G.Edge) : G.X → G.X → Prop :=
  fun x y => x = G.root e.val ∧ y = G.root (G.flip e.val)

def ContractSetoid (e : G.Edge) : Setoid G.X :=
  Relation.EqvGen.setoid (ContractGen e)

def ContractX (e : G.Edge) :=
  Quotient (ContractSetoid e)

lemma respects_contract
    (e : G.Edge)
    {f : G.X → G.X}
    (hf : ∀ x y, ContractGen e x y →
      ContractGen e (f x) (f y)) :
    ∀ x y, ContractSetoid e x y →
      ContractSetoid e (f x) (f y) := by
  intro x y h
  change Relation.EqvGen (ContractGen e) x y at h
  change Relation.EqvGen (ContractGen e) (f x) (f y)
  induction h with
  | rel x y hxy =>
      exact Relation.EqvGen.rel (f x) (f y) (hf x y hxy)
  | refl x =>
      exact Relation.EqvGen.refl (f x)
  | symm x y hxy ih =>
      exact Relation.EqvGen.symm (f x) (f y) ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans (f x) (f y) (f z) ihxy ihyz

lemma root_respects_contract (e : G.Edge) :
    ∀ x y, ContractSetoid e x y →
      ContractSetoid e (G.root x) (G.root y) := by
  apply respects_contract e
  intro x y h
  rcases h with ⟨hx, hy⟩
  constructor
  · rw [hx]
    exact congrFun G.root_idem e.val
  · rw [hy]
    exact congrFun G.root_idem (G.flip e.val)

lemma flip_respects_contract (e : G.Edge) :
    ∀ x y, ContractSetoid e x y →
      ContractSetoid e (G.flip x) (G.flip y) := by
  apply respects_contract e
  intro x y h
  rcases h with ⟨hx, hy⟩
  constructor
  · rw [hx]
    exact congrFun G.flip_root e.val
  · rw [hy]
    exact congrFun G.flip_root (G.flip e.val)

def ContractRoot (e : G.Edge) : ContractX e → ContractX e :=
  Quotient.lift
    (Quotient.mk (ContractSetoid e) ∘ G.root)
    (by
      intro x y h
      exact Quotient.sound (root_respects_contract e x y h))

def ContractFlip (e : G.Edge) : ContractX e → ContractX e :=
  Quotient.lift
    (Quotient.mk (ContractSetoid e) ∘ G.flip)
    (by
      intro x y h
      exact Quotient.sound (flip_respects_contract e x y h))

@[simp]
lemma ContractRoot_mk (e : G.Edge) (x : G.X) :
    ContractRoot e (Quotient.mk (ContractSetoid e) x) =
      Quotient.mk (ContractSetoid e) (G.root x) := by
  rfl

@[simp]
lemma ContractFlip_mk (e : G.Edge) (x : G.X) :
    ContractFlip e (Quotient.mk (ContractSetoid e) x) =
      Quotient.mk (ContractSetoid e) (G.flip x) := by
  rfl

lemma ContractRoot_idem (e : G.Edge) :
    ContractRoot e ∘ ContractRoot e = ContractRoot e := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [ContractRoot_mk]
  apply congrArg (Quotient.mk (ContractSetoid e))
  exact congrFun G.root_idem x

lemma ContractFlip_invo (e : G.Edge) :
    ContractFlip e ∘ ContractFlip e = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change ContractFlip e (ContractFlip e (Quotient.mk (ContractSetoid e) x))
      = Quotient.mk (ContractSetoid e) x
  rw [ContractFlip_mk, ContractFlip_mk]
  apply congrArg (Quotient.mk (ContractSetoid e))
  simpa using congrFun G.flip_invo x

lemma ContractFlip_root (e : G.Edge) :
    ContractFlip e ∘ ContractRoot e = ContractRoot e := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [ContractRoot_mk]
  apply congrArg (Quotient.mk (ContractSetoid e))
  exact congrFun G.flip_root x

def contractGraph (e : G.Edge) : SerreGraph where
  X := ContractX e
  finite := by
    let := G.finite
    apply Finite.of_surjective (Quotient.mk (ContractSetoid e))
    exact Quotient.mk_surjective
  root := ContractRoot e
  flip := ContractFlip e
  root_idem := ContractRoot_idem e
  flip_invo := ContractFlip_invo e
  flip_root := ContractFlip_root e

-- maybe abbrev is better than def here, but we will see
def edgeContraction (e : G.Edge) := Quotient.mk (ContractSetoid e)

def edgeContractionHom (e : G.Edge) : Hom G (G.contractGraph e) where
  toFun := edgeContraction e
  root_comm := by
    funext x
    change ContractRoot e (Quotient.mk (ContractSetoid e) x) =
      Quotient.mk (ContractSetoid e) (G.root x)
    rw [ContractRoot_mk]
  flip_comm := by
    funext x
    change ContractFlip e (Quotient.mk (ContractSetoid e) x) =
      Quotient.mk (ContractSetoid e) (G.flip x)
    rw [ContractFlip_mk]

inductive IsContraction : {G H : SerreGraph} → Hom G H → Prop where
  | iso {G H : SerreGraph} (f : Hom G H) :
      IsIso f →
      IsContraction f
  | contract {G H : SerreGraph}
      (e : G.Edge)
      (g : Hom (contractGraph e) H) :
      IsContraction g →
      IsContraction ((edgeContractionHom e).comp g)

end SerreGraph
