module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

open scoped Pointwise Indicator

public section

variable {α G M₀ : Type*}

section OneZero
variable [One M₀] [Zero M₀] [Group G] [MulAction G α]

@[to_additive (dont_translate := M₀) (attr := simp) indicator_one_vadd]
lemma indicator_one_smul (g : G) (s : Set α) (a : α) : 𝟭_[g • s, M₀] a = 𝟭_[s] (g⁻¹ • a) := by
  classical simp [Set.indicator_apply, Set.mem_smul_set_iff_inv_smul_mem]

end OneZero
