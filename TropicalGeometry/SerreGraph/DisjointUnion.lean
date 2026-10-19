import TropicalGeometry.SerreGraph.Basic
/-! ... -/

def disjointUnionRoot (G H : SerreGraph) :
    Sum G.X H.X → Sum G.X H.X
  | Sum.inl x => Sum.inl (G.root x)
  | Sum.inr y => Sum.inr (H.root y)

def disjointUnionFlip (G H : SerreGraph) :
    Sum G.X H.X → Sum G.X H.X
  | Sum.inl x => Sum.inl (G.flip x)
  | Sum.inr y => Sum.inr (H.flip y)

def disjointUnion (G H : SerreGraph) : SerreGraph where
  X := Sum G.X H.X
  finite := by
    let := G.finite
    let := H.finite
    infer_instance
  root := disjointUnionRoot G H
  flip := disjointUnionFlip G H
  root_idem := by
    funext x
    cases x <;>
    dsimp [disjointUnionRoot]
    · rw [Sum.inl.inj_iff]
      change (G.root ∘ G.root) _ = G.root _
      rw [G.root_idem]
    · rw [Sum.inr.inj_iff]
      change (H.root ∘ H.root) _ = H.root _
      rw [H.root_idem]
  flip_invo := by
    funext x
    cases x <;>
    dsimp [disjointUnionFlip]
    · rw [Sum.inl.inj_iff]
      change (G.flip ∘ G.flip) _ = id _
      rw [G.flip_invo]
    · rw [Sum.inr.inj_iff]
      change (H.flip ∘ H.flip) _ = id _
      rw [H.flip_invo]
  flip_root := by
    funext x
    cases x <;> dsimp [disjointUnionRoot, disjointUnionFlip]
    · rw [Sum.inl.inj_iff]
      change (G.flip ∘ G.root) _ = G.root _
      rw [G.flip_root]
    · rw [Sum.inr.inj_iff]
      change (H.flip ∘ H.root) _ = H.root _
      rw [H.flip_root]

lemma disjointUnion_inl_isVertex
    (G H : SerreGraph) (v : G.X)
    (hv : G.IsVertex v) :
    (disjointUnion G H).IsVertex (Sum.inl v) := by
  change ∃ a, (disjointUnion G H).root a = Sum.inl v
  obtain ⟨a, ha⟩ := hv
  refine ⟨Sum.inl a, ?_⟩
  change Sum.inl (G.root a) = Sum.inl v
  rw [ha]

lemma disjointUnion_inr_isVertex
    (G H : SerreGraph) (v : H.X)
    (hv : H.IsVertex v) :
    (disjointUnion G H).IsVertex (Sum.inr v) := by
  change ∃ a, (disjointUnion G H).root a = Sum.inr v
  obtain ⟨a, ha⟩ := hv
  refine ⟨Sum.inr a, ?_⟩
  change Sum.inr (H.root a) = Sum.inr v
  rw [ha]
