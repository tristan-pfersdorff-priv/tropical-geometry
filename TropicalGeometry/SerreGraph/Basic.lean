import Mathlib

structure SerreGraph where

  -- The ambient set in question, but doing things as a type is likely easier
  X : Type*
  -- I like to assume my graphs are finite since infinite ones are pointless for tropical stuff
  finite : Finite X
  -- I also like to disallow the empty graph, but fibers may be empty, so we will allow this
  -- nonempty: Inhabited X

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
--instance (G : SerreGraph) : Inhabited G.X := G.nonempty

namespace SerreGraph

variable {G H : SerreGraph}

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

lemma IsVertex_iff (v : G.X) :
    IsVertex v ↔ G.root v = v := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    rw [← ha]
    exact congrFun G.root_idem a
  · intro h
    use v

abbrev Vertex (G : SerreGraph) : Type* :=
  {v : G.X  // IsVertex v}
abbrev Edge (G : SerreGraph) : Type* :=
  {e : G.X // IsEdge e}
abbrev Leg (G : SerreGraph) : Type* :=
  {l : G.X // IsLeg l}
abbrev Ledge (G : SerreGraph) : Type* :=
  G.Leg ⊕ G.Edge

def Ledge.val (a : G.Ledge) : G.X :=
  match a with
  | Sum.inl l => l.val
  | Sum.inr e => e.val

-- lean does not readily understand that vertices are indeed vertices
def rootVertex (e : G.Edge) : G.Vertex :=
  ⟨G.root e.val, ⟨e.val, rfl⟩⟩

lemma flip_ne_flip (x : G.X) (hx : G.flip x ≠ x) :
    G.flip (G.flip x) ≠ G.flip x := by
  change (G.flip ∘ G.flip) x ≠ G.flip x
  rw [G.flip_invo]
  simpa using hx.symm

-- and might as well make lean understand that flipping an edge gives an edge
def flipEdge (e : G.Edge) : G.Edge :=
  ⟨G.flip e.val, flip_ne_flip e.val e.property⟩

lemma flipEdge_invo (e : G.Edge) :
    G.flipEdge (G.flipEdge e) = e := by
  apply Subtype.ext
  change G.flip (G.flip e.val) = e.val
  change (G.flip ∘ G.flip) e.val = e.val
  rw [G.flip_invo, id_eq]

-- we prove this by inserting root into flip v and using flip_root
lemma flip_eq_self_of_isVertex (v : G.Vertex) :
    G.flip v.val = v.val := by
  have hv : G.root v.val = v.val := by
    rw [← IsVertex_iff]
    exact v.property
  calc
    G.flip v.val = G.flip (G.root v.val) := by rw [hv]
    _ = G.root v.val := by
      change (G.flip ∘ G.root) v.val = G.root v.val
      rw [G.flip_root]
    _ = v.val := hv

abbrev OutgoingLedges (v : G.Vertex) :=
  {a : G.Ledge // G.root a.val = v.val}

noncomputable def valency (v : G.Vertex) : ℕ :=
  Nat.card (OutgoingLedges v)

noncomputable def nvertices (G : SerreGraph) : ℕ :=
  Nat.card (G.Vertex)

noncomputable def nedges (G : SerreGraph) : ℕ :=
  Nat.card (G.Edge) / 2

noncomputable def nlegs (G : SerreGraph) : ℕ :=
  Nat.card (G.Leg)

noncomputable def nledges (G : SerreGraph) : ℕ :=
  nedges G + nlegs G

def Adjacent {G : SerreGraph} (u v : Vertex G) : Prop :=
  ∃ e : Edge G,
    u = G.rootVertex e ∧
    v = G.rootVertex (G.flipEdge e)

instance adjacent_stdSymm : Std.Symm (@Adjacent G) where
  symm := by
    intro u v h
    rcases h with ⟨e, rfl, rfl⟩
    refine ⟨G.flipEdge e, rfl, ?_⟩
    rw [flipEdge_invo]

def AreConnected {G : SerreGraph} (u v : Vertex G) : Prop :=
  Relation.ReflTransGen (@Adjacent G) u v

lemma neighbors_adjacent (e : Edge G) :
    Adjacent (G.rootVertex e) (G.rootVertex (G.flipEdge e)) := by
  exact ⟨e, rfl, rfl⟩

lemma connected_refl (v : G.Vertex) :
    AreConnected v v := by
  exact Relation.ReflTransGen.refl

lemma connected_symm {u v : G.Vertex} :
    AreConnected u v → AreConnected v u := by
  intro h
  exact Relation.ReflTransGen.stdSymm.symm u v h

lemma connected_trans {u v w : G.Vertex} :
    AreConnected u v →
    AreConnected v w →
    AreConnected u w :=
  Relation.ReflTransGen.trans

theorem connected_equivalence (G : SerreGraph) :
    Equivalence (@AreConnected G) where
  refl := connected_refl
  symm := connected_symm
  trans := connected_trans

def Connected (G : SerreGraph) : Prop :=
  ∀ u v : G.Vertex, AreConnected u v

noncomputable def nComponents (G : SerreGraph) : ℕ := by
  letI : Setoid G.Vertex :=
    ⟨G.AreConnected, G.connected_equivalence⟩
  letI := G.finite
  exact Nat.card (Quotient (inferInstance : Setoid G.Vertex))

noncomputable def genusInZ (G : SerreGraph) : ℤ :=
  (nedges G : ℤ) - (nvertices G : ℤ) + nComponents G

noncomputable def genus (G : SerreGraph) : ℕ :=
  Int.toNat (genusInZ G)

-- TODO: prove that genus = genusInZ, also it may be nice to show that genus is adds over components
theorem genus_nonneg (G : SerreGraph) : genus G = genusInZ G := by
  sorry

-- time to define morphisms of Serre graphs, which are just maps that commute with root and flip

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

-- Now for defining contractions

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

-- we also need to work with plenty of morphisms which do not contract anything
def IsNonContracting (f : Hom G H) : Prop :=
  --∀ e : G.X, IsEdge e → IsEdge (f e) -- also a decent version
  ∀ e : G.Edge, IsEdge (f e)

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

def IsHarmonicOfDeg (ϕ : SubharmonicMorphism G H) (d : ℕ+) : Prop :=
  ∀ v : G.Vertex,
    MultiplicitiesNearVertex ϕ v = (fun _ => d : H.OutgoingLedges ((ϕ : Hom G H).toVertex v) → ℕ)

structure HarmonicMorphism (G H : SerreGraph) where
  toSubharmonic : SubharmonicMorphism G H
  global_deg : ℕ+
  isHarmonic : IsHarmonicOfDeg toSubharmonic global_deg

instance : Coe (HarmonicMorphism G H) (SubharmonicMorphism G H) where
  coe ϕ := ϕ.toSubharmonic

structure RationalFunction (G : SerreGraph) where
  vertex_values : Vertex G → ℤ
  leg_slopes : Leg G → ℤ

def EdgeSlopes (ϕ : RationalFunction G) : Edge G → ℤ :=
  fun e => ϕ.vertex_values (G.rootVertex (G.flipEdge e)) - ϕ.vertex_values (G.rootVertex e)

def LedgeSlopes (ϕ : RationalFunction G) : Ledge G → ℤ
  | Sum.inl l => ϕ.leg_slopes l
  | Sum.inr e => EdgeSlopes ϕ e

/- def splitGraph (e : G.Edge) : SerreGraph where
  X := -- remove e and flip e and add one new vertex and four new edges
  finite := -- added finite types
  root := sorry
  flip := sorry
  root_idem := sorry
  flip_invo := sorry
  flip_root := sorry -/

end SerreGraph
