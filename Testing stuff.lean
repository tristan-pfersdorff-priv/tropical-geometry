import Mathlib

structure SerreGraph where

  -- The ambient set in question, but doing things as a type is likely easier
  X : Type*
  -- I like to assume my graphs are finite since infinite ones are pointless for tropical stuff
  finite : Finite X
  -- I also like to disallow the empty graph
  nonempty: Inhabited X

  -- The usual Serre stuff
  root : X → X
  flip : X → X
  root_idem : root ∘ root = root
  flip_invo : flip ∘ flip = id
  flip_root : flip ∘ root = root
  -- no_loops : ∀ x, root (flip x) = root x → flip x = x

/- This somehow helps lean understand that sybtypes of G.X are finite,
  i.e. that Finite Y checks out for any sybtype Y of G.X .
  However, lean is much more strict on labeling things as Fintype;
  Difference being that lean demands proofs of finiteness for that
  and does not like to provide them automatically as a design choice,
  which is why a lot of stuff will be marked noncomputable as soon as
  we try to do stuff that needs to know the underlying finite sets,
  like taking valencies.
-/
instance (G : SerreGraph) : Inhabited G.X := G.nonempty

namespace SerreGraph

variable {G : SerreGraph}

def Loopless (G : SerreGraph) : Prop :=
  ∀ x, G.root (G.flip x) = G.root x → G.flip x = x

-- TODO
-- prove lemma that loopless is equivalent to the condition that the root of a flip is
-- not equal to the root of the original element unless they are equal, since this may be useful

def IsVertex (v : G.X) : Prop :=
  ∃ a : G.X, G.root a = v
  --G.root v = v
def IsEdge (e : G.X) : Prop :=
  G.flip e ≠ e
def IsLeg (l : G.X) : Prop :=
  G.root l ≠ l ∧ G.flip l = l

abbrev V (G : SerreGraph) : Type* :=
  {v : G.X  // IsVertex v}
abbrev E (G : SerreGraph) : Type* :=
  {e : G.X // IsEdge e}
abbrev L (G : SerreGraph) : Type* :=
  {l : G.X // IsLeg l}
abbrev LE (G : SerreGraph) : Type* :=
  {a : G.X // IsEdge a ∨ IsLeg a}

-- lean does not readily understand that vertices are indeed vertices
def rootVertex (e : G.E) : G.V :=
  ⟨G.root e.val, ⟨e.val, rfl⟩⟩

lemma flip_ne_flip (x : G.X) (hx : G.flip x ≠ x) :
    G.flip (G.flip x) ≠ G.flip x := by
  change (G.flip ∘ G.flip) x ≠ G.flip x
  rw [G.flip_invo]
  simpa using hx.symm

-- and might as well make lean understand that flipping an edge gives an edge
def flipEdge (e : G.E) : G.E :=
  ⟨G.flip e.val, flip_ne_flip e.val e.property⟩

lemma flipEdge_invo (e : G.E) :
    G.flipEdge (G.flipEdge e) = e := by
  apply Subtype.ext
  change G.flip (G.flip e.val) = e.val
  change (G.flip ∘ G.flip) e.val = e.val
  rw [G.flip_invo, id_eq]

abbrev OutgoingLedges (v : V G) :=
  {a : LE G // G.root a.val = v.val}

noncomputable def valency (v : V G) : ℕ :=
  Nat.card (OutgoingLedges v)

noncomputable def nvertices (G : SerreGraph) : ℕ :=
  Nat.card (V G)

noncomputable def nedges (G : SerreGraph) : ℕ :=
  Nat.card (E G) / 2

noncomputable def nlegs (G : SerreGraph) : ℕ :=
  Nat.card (L G)

noncomputable def nledges (G : SerreGraph) : ℕ :=
  nedges G + nlegs G

noncomputable def genus (G : SerreGraph) : ℤ :=
  (nedges G : ℤ) - (nvertices G : ℤ) + 1


def Adjacent {G : SerreGraph} (u v : V G) : Prop :=
  ∃ e : E G,
    u = G.rootVertex e ∧
    v = G.rootVertex (G.flipEdge e)

instance adjacent_stdSymm : Std.Symm (@Adjacent G) where
  symm := by
    intro u v h
    rcases h with ⟨e, rfl, rfl⟩
    refine ⟨G.flipEdge e, rfl, ?_⟩
    rw [flipEdge_invo]

def AreConnected {G : SerreGraph} (u v : V G) : Prop :=
  Relation.ReflTransGen (@Adjacent G) u v

lemma neighbors_adjacent (e : E G) :
    Adjacent (G.rootVertex e) (G.rootVertex (G.flipEdge e)) := by
  exact ⟨e, rfl, rfl⟩

lemma connected_refl (v : G.V) :
    AreConnected v v := by
  exact Relation.ReflTransGen.refl

lemma connected_symm {u v : G.V} :
    AreConnected u v → AreConnected v u := by
  intro h
  exact Relation.ReflTransGen.stdSymm.symm u v h

lemma connected_trans {u v w : G.V} :
    AreConnected u v →
    AreConnected v w →
    AreConnected u w :=
  Relation.ReflTransGen.trans

theorem connectedEquivalence (G : SerreGraph) :
    Equivalence (@AreConnected G) where
  refl := connected_refl
  symm := connected_symm
  trans := connected_trans

def Connected (G : SerreGraph) : Prop :=
  ∀ u v : G.V, AreConnected u v

-- TODO
-- update genus definition for disconnected graphs maybe, though idk if we need this


-- time to define morphisms of Serre graphs, which are just map that commute with root and flip

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

-- Now for defining contractions

def ContractGen (e : G.E) : G.X → G.X → Prop :=
  fun x y => x = G.root e.val ∧ y = G.root (G.flip e.val)

def ContractSetoid (e : G.E) : Setoid G.X :=
  Relation.EqvGen.setoid (ContractGen e)

def ContractX (e : G.E) :=
  Quotient (ContractSetoid e)

lemma respects_contract
    (e : G.E)
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

lemma root_respects_contract (e : G.E) :
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

lemma flip_respects_contract (e : G.E) :
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

def ContractRoot (e : G.E) : ContractX e → ContractX e :=
  Quotient.lift
    (Quotient.mk (ContractSetoid e) ∘ G.root)
    (by
      intro x y h
      exact Quotient.sound (root_respects_contract e x y h))

def ContractFlip (e : G.E) : ContractX e → ContractX e :=
  Quotient.lift
    (Quotient.mk (ContractSetoid e) ∘ G.flip)
    (by
      intro x y h
      exact Quotient.sound (flip_respects_contract e x y h))

@[simp]
lemma ContractRoot_mk (e : G.E) (x : G.X) :
    ContractRoot e (Quotient.mk (ContractSetoid e) x) =
      Quotient.mk (ContractSetoid e) (G.root x) := by
  rfl

@[simp]
lemma ContractFlip_mk (e : G.E) (x : G.X) :
    ContractFlip e (Quotient.mk (ContractSetoid e) x) =
      Quotient.mk (ContractSetoid e) (G.flip x) := by
  rfl

lemma ContractRoot_idem (e : G.E) :
    ContractRoot e ∘ ContractRoot e = ContractRoot e := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [ContractRoot_mk]
  apply congrArg (Quotient.mk (ContractSetoid e))
  exact congrFun G.root_idem x

lemma ContractFlip_invo (e : G.E) :
    ContractFlip e ∘ ContractFlip e = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change ContractFlip e (ContractFlip e (Quotient.mk (ContractSetoid e) x))
      = Quotient.mk (ContractSetoid e) x
  rw [ContractFlip_mk, ContractFlip_mk]
  apply congrArg (Quotient.mk (ContractSetoid e))
  simpa using congrFun G.flip_invo x

lemma ContractFlip_root (e : G.E) :
    ContractFlip e ∘ ContractRoot e = ContractRoot e := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [ContractRoot_mk]
  apply congrArg (Quotient.mk (ContractSetoid e))
  exact congrFun G.flip_root x

def contractGraph (e : G.E) : SerreGraph where
  X := ContractX e
  finite := by
    let := G.finite
    apply Finite.of_surjective (Quotient.mk (ContractSetoid e))
    exact Quotient.mk_surjective
  nonempty := ⟨Quotient.mk (ContractSetoid e) default⟩
  root := ContractRoot e
  flip := ContractFlip e
  root_idem := ContractRoot_idem e
  flip_invo := ContractFlip_invo e
  flip_root := ContractFlip_root e

abbrev edgeContraction (e : G.E) := Quotient.mk (ContractSetoid e)

end SerreGraph
