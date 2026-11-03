module

public import PaperP1.Algebra.RungeQPolynomial
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exact integer height bounds for actual split-radical point coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalPointHeight

open Finset

def integerProduct (I : Finset ℤ) (x : ℤ) : ℤ := ∏ i ∈ I, (x + i)

theorem product_height (I : Finset ℤ) (x : ℤ) (H W : ℕ)
    (hx : x.natAbs ≤ H) (hI : ∀ i ∈ I, i.natAbs ≤ W) :
    (integerProduct I x).natAbs ≤ (H + W) ^ I.card := by
  rw [integerProduct, RungeQPolynomial.int_natAbs_finset_prod]
  calc
    (∏ i ∈ I, (x + i).natAbs) ≤ ∏ _i ∈ I, (H + W) :=
      prod_le_prod fun i hi ↦ (Int.natAbs_add_le x i).trans (Nat.add_le_add hx (hI i hi))
    _ = (H + W) ^ I.card := by simp

theorem square_height (I J : Finset ℤ) (x y w c : ℤ) (H W : ℕ)
    (hx : x.natAbs ≤ H) (hy : y.natAbs ≤ H)
    (hI : ∀ i ∈ I, i.natAbs ≤ W) (hJ : ∀ j ∈ J, j.natAbs ≤ W)
    (heq : w ^ 2 = c * integerProduct I x * integerProduct J y) :
    w.natAbs ^ 2 ≤ c.natAbs * (H + W) ^ (I.card + J.card) := by
  have habs := congrArg Int.natAbs heq
  rw [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_mul] at habs
  rw [habs, pow_add, ← mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left c.natAbs (product_height I x H W hx hI))
    (product_height J y H W hy hJ)

theorem dyadic_square_height (I J : Finset ℤ) (x y w c : ℤ) (N K : ℕ) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i ∈ I, i.natAbs ≤ N) (hJ : ∀ j ∈ J, j.natAbs ≤ N)
    (hK : I.card + J.card ≤ K) (heq : w ^ 2 = c * integerProduct I x * integerProduct J y) :
    w.natAbs ^ 2 ≤ c.natAbs * (3 * N) ^ K := by
  have hh := square_height I J x y w c (2 * N) N hx hy hI hJ heq
  have he : 2 * N + N = 3 * N := by omega
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_left c.natAbs (Nat.pow_le_pow_right (by omega) hK))

theorem monomial_height (x y : ℤ) (N a b D : ℕ) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N) (hdegree : a + b ≤ D) :
    (x ^ a * y ^ b).natAbs ≤ 2 ^ D * N ^ D := by
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, ← mul_pow]
  calc
    x.natAbs ^ a * y.natAbs ^ b ≤ (2 * N) ^ a * (2 * N) ^ b :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hx a) (Nat.pow_le_pow_left hy b)
    _ = (2 * N) ^ (a + b) := (pow_add _ _ _).symm
    _ ≤ (2 * N) ^ D := Nat.pow_le_pow_right (by omega) hdegree

theorem sum_natAbs_le {ι : Type*} [DecidableEq ι] (A : Finset ι) (w : ι → ℤ) :
    (∑ i ∈ A, w i).natAbs ≤ ∑ i ∈ A, (w i).natAbs := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

end PaperP1.SplitRadicalPointHeight
