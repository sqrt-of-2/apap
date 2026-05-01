module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.BigOperators.Expect

public section

open Finset
open scoped BigOperators Indicator

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {α R : Type*}

section NNRatModule
variable [Fintype α] [Semiring R] [Module ℚ≥0 R]

lemma expect_indicator_one (s : Finset α) : 𝔼 x, 𝟭_[(s : Set α), R] x = #s /ℚ Fintype.card α := by
  classical
  simp only [expect_univ, Set.indicator_apply, mem_coe]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, Nat.smul_one_eq_cast]

end NNRatModule
