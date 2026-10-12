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





-- time to define morphisms of Serre graphs, which are just maps that commute with root and flip

-- Now for defining contractions







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
