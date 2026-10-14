import TropicalGeometry.SerreGraph.Basic
/-! ... -/

namespace SerreGraph

variable {G : SerreGraph}

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

end SerreGraph
