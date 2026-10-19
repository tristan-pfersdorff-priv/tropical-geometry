import Mathlib
/-! ... -/

namespace Relation

lemma eqvGen_map
    {α β : Type*}
    (r : α → α → Prop)
    (s : β → β → Prop)
    (f : α → β)
    (hf : ∀ x y, r x y → s (f x) (f y)) :
    ∀ x y, Relation.EqvGen r x y →
      Relation.EqvGen s (f x) (f y) := by
  intro x y h
  induction h with
  | rel x y hxy =>
      exact Relation.EqvGen.rel (f x) (f y) (hf x y hxy)
  | refl x =>
      exact Relation.EqvGen.refl (f x)
  | symm x y hxy ih =>
      exact Relation.EqvGen.symm (f x) (f y) ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans (f x) (f y) (f z) ihxy ihyz

lemma respects_eqvGen
    {α : Type*}
    (r : α → α → Prop)
    (f : α → α)
    (hf : ∀ x y, r x y → r (f x) (f y)) :
    ∀ x y, Relation.EqvGen r x y →
      Relation.EqvGen r (f x) (f y) := by
  exact Relation.eqvGen_map r r f hf

lemma respects_eqvGen_setoid
    {α : Type*}
    (r : α → α → Prop)
    (s : Setoid α)
    (hs : s.r = Relation.EqvGen r)
    {f : α → α}
    (hf : ∀ x y, r x y → r (f x) (f y)) :
    ∀ x y, s.r x y → s.r (f x) (f y) := by
  intro x y h
  rw [hs] at h ⊢
  exact Relation.respects_eqvGen r f hf x y h

def liftQuotient
    {α : Type*}
    (s : Setoid α)
    (f : α → α)
    (hf : ∀ x y, s.r x y → s.r (f x) (f y)) :
    Quotient s → Quotient s :=
  Quotient.lift
    (Quotient.mk s ∘ f)
    (fun x y h => Quotient.sound (hf x y h))

lemma liftQuotient_eq
    {α : Type*}
    (s : Setoid α)
    {f g : α → α}
    (hf : ∀ x y, s.r x y → s.r (f x) (f y))
    (hg : ∀ x y, s.r x y → s.r (g x) (g y))
    (hfg : f = g) :
    liftQuotient s f hf = liftQuotient s g hg := by
  subst g
  rfl

end Relation
