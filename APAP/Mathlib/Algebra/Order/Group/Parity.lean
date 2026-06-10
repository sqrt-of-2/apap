module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Lattice

public section

section
variable {M : Type*} [LinearOrder M] [Monoid M] {a b : M}

@[to_additive]
protected lemma IsSquare.max (ha : IsSquare a) (hb : IsSquare b) : IsSquare (max a b) := by grind

@[to_additive]
protected lemma IsSquare.min (ha : IsSquare a) (hb : IsSquare b) : IsSquare (min a b) := by grind

end
