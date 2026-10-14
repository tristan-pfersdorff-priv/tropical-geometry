import Mathlib
/-! ... -/

structure SerreGraph where
  X : Type*
  finite : Finite X
  root : X → X
  flip : X → X
  root_idem : root ∘ root = root
  flip_invo : flip ∘ flip = id
  flip_root : flip ∘ root = root

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

/- def splitGraph (e : G.Edge) : SerreGraph where
  X := -- remove e and flip e and add one new vertex and four new edges
  finite := -- added finite types
  root := sorry
  flip := sorry
  root_idem := sorry
  flip_invo := sorry
  flip_root := sorry -/

end SerreGraph
