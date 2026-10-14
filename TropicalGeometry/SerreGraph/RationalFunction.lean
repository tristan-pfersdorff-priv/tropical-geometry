import TropicalGeometry.SerreGraph.Basic
/-! ... -/

namespace SerreGraph

structure RationalFunction (G : SerreGraph) where
  vertex_values : Vertex G → ℤ
  leg_slopes : Leg G → ℤ

def EdgeSlopes (ϕ : RationalFunction G) : Edge G → ℤ :=
  fun e => ϕ.vertex_values (G.rootVertex (G.flipEdge e)) - ϕ.vertex_values (G.rootVertex e)

def LedgeSlopes (ϕ : RationalFunction G) : Ledge G → ℤ
  | Sum.inl l => ϕ.leg_slopes l
  | Sum.inr e => EdgeSlopes ϕ e

end SerreGraph
