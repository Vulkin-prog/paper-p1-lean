module

public import PaperP1.Arithmetic.SplitRadicalPointHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A common coefficient-uniform point height for the actual affine and weighted-Veronese coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalEmbeddingHeight

open Finset PaperP1.SplitRadicalPointHeight

theorem radical_height (I J : Finset ℤ) (x y w c : ℤ) (N K : ℕ) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i ∈ I, i.natAbs ≤ N) (hJ : ∀ j ∈ J, j.natAbs ≤ N) (hK : I.card + J.card ≤ K)
    (A D : ℝ) (hdegree : A + (K : ℝ) ≤ 2 * D) (hc : (c.natAbs : ℝ) ≤ (N : ℝ) ^ A)
    (heq : w ^ 2 = c * integerProduct I x * integerProduct J y) :
    (w.natAbs : ℝ) ≤ (3 : ℝ) ^ K * (N : ℝ) ^ D := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hsq : (w.natAbs : ℝ) ^ 2 ≤ (c.natAbs : ℝ) * (3 * (N : ℝ)) ^ K := by
    exact_mod_cast dyadic_square_height I J x y w c N K hN hx hy hI hJ hK heq
  have hproduct : (c.natAbs : ℝ) * (3 * (N : ℝ)) ^ K ≤
      (3 : ℝ) ^ K * (N : ℝ) ^ (A + (K : ℝ)) := by
    calc
      (c.natAbs : ℝ) * (3 * (N : ℝ)) ^ K ≤ (N : ℝ) ^ A * (3 * (N : ℝ)) ^ K :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (3 : ℝ) ^ K * (N : ℝ) ^ (A + (K : ℝ)) := by
        rw [mul_pow, Real.rpow_add hNp, Real.rpow_natCast]
        ring
  have hexp := Real.rpow_le_rpow_of_exponent_le hNr hdegree
  have htwo : (N : ℝ) ^ (2 * D) = ((N : ℝ) ^ D) ^ 2 := by
    rw [mul_comm (2 : ℝ) D, Real.rpow_mul hNp.le, Real.rpow_two]
  have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hthreesq : (3 : ℝ) ^ K ≤ ((3 : ℝ) ^ K) ^ 2 := by nlinarith
  have hbound : (w.natAbs : ℝ) ^ 2 ≤ ((3 : ℝ) ^ K * (N : ℝ) ^ D) ^ 2 := by
    calc
      (w.natAbs : ℝ) ^ 2 ≤ (3 : ℝ) ^ K * (N : ℝ) ^ (A + (K : ℝ)) := hsq.trans hproduct
      _ ≤ (3 : ℝ) ^ K * (N : ℝ) ^ (2 * D) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (3 : ℝ) ^ K * ((N : ℝ) ^ D) ^ 2 := by rw [htwo]
      _ ≤ ((3 : ℝ) ^ K) ^ 2 * ((N : ℝ) ^ D) ^ 2 := mul_le_mul_of_nonneg_right hthreesq (sq_nonneg _)
      _ = ((3 : ℝ) ^ K * (N : ℝ) ^ D) ^ 2 := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp hbound

theorem sum_height {ι : Type*} [Fintype ι] (w : ι → ℤ) (C Q : ℝ)
    (hw : ∀ i, ((w i).natAbs : ℝ) ≤ C * Q) :
    ((∑ i, w i).natAbs : ℝ) ≤ Fintype.card ι * C * Q := by
  classical
  have hsum : ((∑ i, w i).natAbs : ℝ) ≤ ∑ i, ((w i).natAbs : ℝ) := by
    exact_mod_cast sum_natAbs_le univ w
  calc
    ((∑ i, w i).natAbs : ℝ) ≤ ∑ i, ((w i).natAbs : ℝ) := hsum
    _ ≤ ∑ _i : ι, C * Q := sum_le_sum fun i _ ↦ hw i
    _ = Fintype.card ι * C * Q := by rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]

def commonConstant (k K D : ℕ) : ℝ := (2 : ℝ) ^ D + (k + 1 : ℕ) * (3 : ℝ) ^ K

theorem commonConstant_pos (k K D : ℕ) : 0 < commonConstant k K D := by
  unfold commonConstant
  positivity

theorem coordinates_height {ι : Type*} [Fintype ι]
    (I J : ι → Finset ℤ) (c w : ι → ℤ) (x y : ℤ) (N K D : ℕ) (A : ℝ)
    (hN : 1 ≤ N) (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i, ∀ a ∈ I i, a.natAbs ≤ N) (hJ : ∀ i, ∀ a ∈ J i, a.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A + (K : ℝ) ≤ 2 * D)
    (hc : ∀ i, ((c i).natAbs : ℝ) ≤ (N : ℝ) ^ A)
    (heq : ∀ i, w i ^ 2 = c i * integerProduct (I i) x * integerProduct (J i) y) :
    (∀ a b : ℕ, a + b ≤ D → ((x ^ a * y ^ b).natAbs : ℝ) ≤
      commonConstant (Fintype.card ι) K D * (N : ℝ) ^ D) ∧
    (∀ i, ((w i).natAbs : ℝ) ≤ commonConstant (Fintype.card ι) K D * (N : ℝ) ^ D) ∧
    ((∑ i, w i).natAbs : ℝ) ≤ commonConstant (Fintype.card ι) K D * (N : ℝ) ^ D := by
  have hrad : ∀ i, ((w i).natAbs : ℝ) ≤ (3 : ℝ) ^ K * (N : ℝ) ^ D := by
    intro i
    simpa only [Real.rpow_natCast] using radical_height (I i) (J i) x y (w i) (c i) N K hN hx hy
      (hI i) (hJ i) (hK i) A D hdegree (hc i) (heq i)
  have hpow : (0 : ℝ) ≤ (N : ℝ) ^ D := by positivity
  have hconst_mono : (2 : ℝ) ^ D ≤ commonConstant (Fintype.card ι) K D := by
    unfold commonConstant
    exact le_add_of_nonneg_right (by positivity)
  have hconst_rad : (3 : ℝ) ^ K ≤ commonConstant (Fintype.card ι) K D := by
    unfold commonConstant
    have hcard : (1 : ℝ) ≤ (Fintype.card ι + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 (Fintype.card ι)
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) K, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) D]
  have hconst_sum : (Fintype.card ι : ℝ) * (3 : ℝ) ^ K ≤ commonConstant (Fintype.card ι) K D := by
    unfold commonConstant
    push_cast
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) K, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) D]
  refine ⟨?_, fun i ↦ (hrad i).trans (mul_le_mul_of_nonneg_right hconst_rad hpow), ?_⟩
  · intro a b hab
    have hh : ((x ^ a * y ^ b).natAbs : ℝ) ≤ (2 : ℝ) ^ D * (N : ℝ) ^ D := by
      exact_mod_cast monomial_height x y N a b D hN hx hy hab
    exact hh.trans (mul_le_mul_of_nonneg_right hconst_mono hpow)
  · exact (sum_height w ((3 : ℝ) ^ K) ((N : ℝ) ^ D) hrad).trans
      (mul_le_mul_of_nonneg_right hconst_sum hpow)

end PaperP1.SplitRadicalEmbeddingHeight
