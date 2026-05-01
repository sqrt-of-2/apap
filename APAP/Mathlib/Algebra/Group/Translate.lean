module

public import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Group.Translate

public section

open scoped Pointwise translate Indicator

variable {G M₀ : Type*}

section Semiring
variable [One M₀] [Zero M₀] [AddCommGroup G]

variable (M₀) in
lemma translate_indicator_one (a : G) (s : Set G) : τ a 𝟭_[s, M₀] = 𝟭_[a +ᵥ s] := by
  classical ext; simp [Set.indicator_apply, Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end Semiring
