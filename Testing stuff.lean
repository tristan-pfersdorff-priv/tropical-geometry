import Mathlib

structure SerreGraph where

  -- The ambient set in question, but doing things as a type is likely easier
  X : Type*
  -- I like to assume my graphs are finite since infinite ones are pointless for tropical stuff
  finite : Fintype X
  -- I also like to disallow the empty graph
  nonempty: Inhabited X
  -- This might be useful in the future, but we shall see
  dec_eq : DecidableEq X

  -- The usual Serre stuff
  root : X → X
  flip : X → X
  root_idem : root ∘ root = root
  flip_invo : flip ∘ flip = id
  flip_root : flip ∘ root = root


/- This somehow helps lean understand that sybtypes of G.X are finite,
  i.e. that Finite Y checks out for any sybtype Y of G.X .
  However, lean is much more strict on labeling things as Fintype;
  Difference being that lean demands proofs of finiteness for that
  and does not like to provide them automatically as a design choice,
  which is why a lot of stuff will be marked noncomputable as soon as
  we try to do stuff that needs to know the underlying finite sets,
  like taking valencies.
-/
instance (G : SerreGraph) : Fintype G.X := G.finite
instance (G : SerreGraph) : Inhabited G.X := G.nonempty
instance (G : SerreGraph) : DecidableEq G.X := G.dec_eq

namespace SerreGraphDefs

variable {G : SerreGraph}

def IsVertex (v : G.X) : Prop :=
  G.root v = v
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

abbrev OutgoingLedges (v : V G) :=
  {a : LE G // G.root a.val = v.val}

noncomputable def valency (v : V G) : ℕ :=
  Nat.card (OutgoingLedges v)

end SerreGraphDefs

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
