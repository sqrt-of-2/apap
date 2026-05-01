module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise Indicator

public section

variable {G M₀ : Type*}

section OneZero
variable [One M₀] [Zero M₀] [Group G]

@[to_additive (dont_translate := M₀) (attr := simp) indicator_one_neg]
lemma indicator_one_inv (s : Set G) (a : G) : 𝟭_[s⁻¹, M₀] a = 𝟭_[s] a⁻¹ := by
  classical simp [Set.indicator_apply]

end OneZero
