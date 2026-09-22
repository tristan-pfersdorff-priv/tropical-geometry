import Mathlib

--open Finset

structure SerreGraph where
  X : Type*
  root : X → X
  flip : X → X
  root_idem : root ∘ root = root
  flip_invo : flip ∘ flip = id
  flip_root : flip ∘ root = root
  [finite : Fintype X]
  [nonempty: Inhabited X]

namespace SerreGraph

variable {G H : SerreGraph}

def IsVertex (v : G.X) : Prop :=
  v ∈ Set.range G.root

def IsEdge (e : G.X) : Prop :=
  G.flip e ≠ e

def IsLeg (l : G.X) : Prop :=
  ¬IsVertex l ∧ ¬IsEdge l

end SerreGraph
