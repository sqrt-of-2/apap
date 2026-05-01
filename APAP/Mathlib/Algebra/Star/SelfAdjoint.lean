module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Star.SelfAdjoint

public section

open scoped ComplexConjugate Indicator

variable {ι α R : Type*}

section Semiring
variable [Semiring R] [StarRing R]

lemma isSelfAdjoint_indicator_one (s : Set α) : IsSelfAdjoint 𝟭_[s, R] :=
  Pi.isSelfAdjoint.2 fun g ↦ by classical rw [Set.indicator_apply]; split_ifs <;> simp

end Semiring
