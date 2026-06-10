module

public import AddCombi.Convolution.Finite.Defs
public import APAP.Prereqs.Convolution.Discrete.Defs

import Mathlib.Analysis.Complex.Basic

/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `conv`: Discrete convolution of two functions in the compact normalisation
* `dconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterCConv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ₙ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a division ring. Doesn't seem very useful given that
the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.
-/

@[expose] public section

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise Indicator translate

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G H R S : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` and difference convolution `f ○ g` of functions
`f g : G → R`, and show how they interact.
-/

/-! ### Trivial character -/

section Semifield
variable [Semifield R]

/-- The trivial character. -/
def trivNChar : G → R := fun a ↦ if a = 0 then card G else 0

@[simp] lemma trivNChar_apply (a : G) : (trivNChar a : R) = if a = 0 then (card G : R) else 0 := rfl

variable [StarRing R]

@[simp] lemma conj_trivNChar : conj (trivNChar : G → R) = trivNChar := by
  ext; simp; split_ifs <;> simp

@[simp] lemma conjneg_trivNChar : conjneg (trivNChar : G → R) = trivNChar := by
  ext; simp; split_ifs <;> simp

@[simp] lemma isSelfAdjoint_trivNChar : IsSelfAdjoint (trivNChar : G → R) := conj_trivNChar

end Semifield

/-! ### Convolution -/

section Semifield
variable [Semifield R] [CharZero R] {f g : G → R}

lemma conv_apply_eq_smul_ddconv (f g : G → R) (a : G) :
    (f ∗ g) a = (f ∗ᵈ g) a /ℚ Fintype.card G := by
  rw [conv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (b, a - b)) Prod.fst ?_ ?_ ?_ ?_ <;>
    simp [Set.LeftInvOn, Set.MapsTo, eq_sub_iff_add_eq', eq_comm]

lemma conv_eq_smul_ddconv (f g : G → R) : f ∗ g = (f ∗ᵈ g) /ℚ Fintype.card G :=
  funext <| conv_apply_eq_smul_ddconv _ _

@[simp] lemma conv_trivNChar (f : G → R) : f ∗ trivNChar = f := by
  ext a; simp [conv_eq_expect_sub, card_univ, NNRat.smul_def, mul_comm]

@[simp] lemma trivNChar_conv (f : G → R) : trivNChar ∗ f = f := by
  rw [conv_comm, conv_trivNChar]

variable [StarRing R]

lemma dconv_apply_eq_smul_dddconv (f g : G → R) (a : G) :
    (f ○ g) a = (f ○ᵈ g) a /ℚ Fintype.card G := by
  rw [dconv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (a + b, b)) Prod.snd ?_ ?_ ?_ ?_ <;>
    simp [Set.MapsTo, Set.LeftInvOn, eq_sub_iff_add_eq, eq_comm]

lemma dconv_eq_smul_dddconv (f g : G → R) : (f ○ g) = (f ○ᵈ g) /ℚ Fintype.card G :=
  funext <| dconv_apply_eq_smul_dddconv _ _

@[simp] lemma dconv_trivNChar (f : G → R) : f ○ trivNChar = f := by
  rw [← conv_conjneg, conjneg_trivNChar, conv_trivNChar]

@[simp] lemma trivNChar_dconv (f : G → R) : trivNChar ○ f = conjneg f := by
  rw [← conv_conjneg, trivNChar_conv]

-- lemma indicator_one_conv_Set.indicator_apply (s t : Finset G) (a : G) :
--     (𝟭_[s, R] ∗ 𝟭_[t]) a = ((s ×ˢ t).filter fun x : G × G ↦ x.1 + x.2 = a).card := by
--   simp only [conv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, expect_boole]
--   simp_rw [← mem_product, filter_univ_mem]

-- lemma indicator_one_dconv_Set.indicator_apply (s t : Finset G) (a : G) :
--     (𝟭_[s, R] ○ 𝟭_[t]) a = ((s ×ˢ t).filter fun x : G × G ↦ x.1 - x.2 = a).card := by
--   simp only [dconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, expect_boole,
--     apply_ite conj, map_one, map_zero, Pi.conj_apply]
--   simp_rw [← mem_product, filter_univ_mem]

end Semifield

section Semifield
variable [Semifield R] [CharZero R]

@[simp] lemma one_conv_one : (1 : G → R) ∗ 1 = 1 := by ext; simp [conv_eq_expect_add, *]

variable [StarRing R]

@[simp] lemma one_dconv_one : (1 : G → R) ○ 1 = 1 := by ext; simp [dconv_eq_expect_add, *]

end Semifield

/-! ### Iterated convolution -/

section Semifield
variable [Semifield R] [CharZero R] {f g : G → R} {n : ℕ}

/-- Iterated convolution. -/
def iterCConv (f : G → R) : ℕ → G → R
  | 0 => trivNChar
  | n + 1 => iterCConv f n ∗ f

infixl:78 " ∗^ₙ " => iterCConv

@[simp] lemma iterCConv_zero (f : G → R) : f ∗^ₙ 0 = trivNChar := rfl
@[simp] lemma iterCConv_one (f : G → R) : f ∗^ₙ 1 = f := trivNChar_conv _

lemma iterCConv_succ (f : G → R) (n : ℕ) : f ∗^ₙ (n + 1) = f ∗^ₙ n ∗ f := rfl
lemma iterCConv_succ' (f : G → R) (n : ℕ) : f ∗^ₙ (n + 1) = f ∗ f ∗^ₙ n := conv_comm _ _

lemma iterCConv_add (f : G → R) (m : ℕ) : ∀ n, f ∗^ₙ (m + n) = f ∗^ₙ m ∗ f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [← add_assoc, iterCConv_succ', iterCConv_add, conv_left_comm]

lemma iterCConv_mul (f : G → R) (m : ℕ) : ∀ n : ℕ, f ∗^ₙ (m * n) = f ∗^ₙ m ∗^ₙ n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterCConv_succ, iterCConv_add, iterCConv_mul]

lemma iterCConv_mul' (f : G → R) (m n : ℕ) : f ∗^ₙ (m * n) = f ∗^ₙ n ∗^ₙ m := by
  rw [mul_comm, iterCConv_mul]

lemma iterCConv_conv_distrib (f g : G → R) : ∀ n, (f ∗ g) ∗^ₙ n = f ∗^ₙ n ∗ g ∗^ₙ n
  | 0 => (conv_trivNChar _).symm
  | n + 1 => by simp_rw [iterCConv_succ, iterCConv_conv_distrib, conv_conv_conv_comm]

@[simp] lemma zero_iterCConv : ∀ {n}, n ≠ 0 → (0 : G → R) ∗^ₙ n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => conv_zero _

@[simp] lemma smul_iterCConv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c : H) (f : G → R) : ∀ n, (c • f) ∗^ₙ n = c ^ n • f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp_rw [iterCConv_succ, smul_iterCConv _ _ n, pow_succ, mul_smul_conv_comm]

lemma comp_iterCConv [Semifield S] [CharZero S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (f ∗^ₙ n) = m ∘ f ∗^ₙ n
  | 0 => by ext; simp; split_ifs <;> simp
  | n + 1 => by simp [iterCConv_succ, comp_conv, comp_iterCConv]

lemma expect_iterCConv (f : G → R) : ∀ n, 𝔼 a, (f ∗^ₙ n) a = (𝔼 a, f a) ^ n
  | 0 => by simp [card_univ, NNRat.smul_def]
  | n + 1 => by simp only [iterCConv_succ, expect_conv, expect_iterCConv, pow_succ]

@[simp] lemma iterCConv_trivNChar : ∀ n, (trivNChar : G → R) ∗^ₙ n = trivNChar
  | 0 => rfl
  | _n + 1 => (conv_trivNChar _).trans <| iterCConv_trivNChar _

lemma support_iterCConv_subset (f : G → R) : ∀ n, support (f ∗^ₙ n) ⊆ n • support f
  | 0 => by
    simp only [iterCConv_zero, zero_smul, support_subset_iff, Ne, ite_eq_right_iff, exists_prop,
      not_forall, Set.mem_zero, and_imp, forall_eq, imp_true_iff, trivNChar_apply]
  | n + 1 =>
    (support_conv_subset _ _).trans <| Set.add_subset_add_right <| support_iterCConv_subset _ _

lemma map_iterCConv [Semifield S] [CharZero S] (m : R →+* S) (f : G → R) (a : G)
    (n : ℕ) : m ((f ∗^ₙ n) a) = (m ∘ f ∗^ₙ n) a := congr_fun (comp_iterCConv m _ _) _

variable [StarRing R]

@[simp] lemma conj_iterCConv (f : G → R) : ∀ n, conj (f ∗^ₙ n) = conj f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [iterCConv_succ, conj_iterCConv]

@[simp] lemma conjneg_iterCConv (f : G → R) : ∀ n, conjneg (f ∗^ₙ n) = conjneg f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [iterCConv_succ, conjneg_iterCConv]

lemma iterCConv_dconv_distrib (f g : G → R) : ∀ n, (f ○ g) ∗^ₙ n = f ∗^ₙ n ○ g ∗^ₙ n
  | 0 => (dconv_trivNChar _).symm
  | n + 1 => by simp_rw [iterCConv_succ, iterCConv_dconv_distrib, conv_dconv_conv_comm]

-- lemma indicator_one_iterCConv_apply (s : Finset G) (n : ℕ) (a : G) :
--     (𝟭_[ℝ] s ∗^ₙ n) a = #{x ∈ piFinset fun _i ↦ s | ∑ i, x i = a} := by
--   induction' n with n ih generalizing a
--   · simp [apply_ite card, eq_comm]
--   simp_rw [iterCConv_succ, conv_eq_expect_sub', ih, Set.indicator_apply, boole_mul, expect_ite,
--     filter_univ_mem, expect_const_zero, add_zero, ← Nat.cast_expect, ← Finset.card_sigma,
--     Nat.cast_inj]
--   refine Finset.card_bij (fun f _ ↦ Fin.cons f.1 f.2) _ _ _
--   · simp only [Fin.expect_cons, eq_sub_iff_add_eq', mem_sigma, mem_filter, mem_piFinset, and_imp]
--     refine fun bf hb hf ha ↦ ⟨Fin.cases _ _, ha⟩
--     · exact hb
--     · simpa only [Fin.cons_succ]
--   · simp only [Sigma.ext_iff, Fin.cons_eq_cons, heq_iff_eq, imp_self, imp_true_iff, forall_const,
--       Sigma.forall]
--   · simp only [mem_filter, mem_piFinset, mem_sigma, exists_prop, Sigma.exists, and_imp,
--       eq_sub_iff_add_eq', and_assoc]
--     exact fun f hf ha ↦
--       ⟨f 0, Fin.tail f, hf _, fun _ ↦ hf _, (Fin.expect_univ_succ _).symm.trans ha,
--         Fin.cons_self_tail _⟩

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_iterCConv (f : G → R) : ∀ {n}, n ≠ 0 → balance (f ∗^ₙ n) = balance f ∗^ₙ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterCConv_succ _ (n + 1), balance_iterCConv _ n.succ_ne_zero]

end Field

namespace NNReal
variable {f : G → ℝ≥0}

@[simp, norm_cast]
lemma coe_iterCConv (f : G → ℝ≥0) (n : ℕ) (a : G) : (↑((f ∗^ₙ n) a) : ℝ) = ((↑) ∘ f ∗^ₙ n) a :=
  map_iterCConv NNReal.toRealHom _ _ _

end NNReal
