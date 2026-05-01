module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Lattice

open Finset Function
open scoped Indicator

public section

variable {ι α M₀ : Type*}

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] [DecidableEq α]

lemma indicator_one_inf_apply [Fintype α] (s : Finset ι) (t : ι → Finset α) (x : α) :
    𝟭_[↑(s.inf t), M₀] x = ∏ i ∈ s, 𝟭_[t i] x := by simp [Set.indicator_apply, mem_inf, prod_boole]

lemma indicator_one_inf [Fintype α] (s : Finset ι) (t : ι → Finset α) :
    𝟭_[↑(s.inf t), M₀] = ∏ i ∈ s, 𝟭_[(t i : Set α)] :=
  funext fun x ↦ by rw [Finset.prod_apply, indicator_one_inf_apply]

end CommMonoidWithZero
