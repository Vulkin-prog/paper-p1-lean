module

public import PaperP1.Algebra.IntegerRowWeightDeterminant
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # The actual free-coordinate height weight of normalized P³ monomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedP3MonomialHeight

open Finset

def freeDegree (m : Fin 4 →₀ ℕ) : ℕ := ∑ i : Fin 3, m i.castSucc

theorem degree_split (m : Fin 4 →₀ ℕ) : freeDegree m + m 3 = m.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]
  rfl

theorem monomial_bound (m : Fin 4 →₀ ℕ) (v : Fin 4 → ℤ) (hvlast : v 3 = 1) (H : ℕ)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) : |m.prod (fun i e ↦ v i ^ e)| ≤ (H : ℤ) ^ freeDegree m := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fin.prod_univ_castSucc]
  have hlast : v (Fin.last 3) = 1 := hvlast
  rw [hlast, one_pow, mul_one, abs_prod]
  calc
    (∏ i : Fin 3, |v i.castSucc ^ m i.castSucc|) ≤ ∏ i : Fin 3, (H : ℤ) ^ m i.castSucc := by
      apply Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _)
      intro i _hi
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hv i.castSucc) _
    _ = (H : ℤ) ^ freeDegree m := by rw [prod_pow_eq_pow_sum]; rfl

theorem determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Fin 4 →₀ ℕ) (v : ι → Fin 4 → ℤ) (H : ℕ)
    (hvlast : ∀ j, v j 3 = 1) (hv : ∀ j i, |v j i| ≤ (H : ℤ)) :
    (Matrix.det (fun i j ↦ (m i).prod (fun k e ↦ v j k ^ e))).natAbs ≤
      (Fintype.card ι).factorial * H ^ (∑ i, freeDegree (m i)) := by
  have h := IntegerRowWeightDeterminant.natAbs_bound
    (fun i j ↦ (m i).prod (fun k e ↦ v j k ^ e)) (fun i ↦ H ^ freeDegree (m i)) (by
      intro i j
      simpa only [Nat.cast_pow] using monomial_bound (m i) (v j) (hvlast j) H (hv j))
  simpa only [prod_pow_eq_pow_sum] using h

end PaperP1.NormalizedP3MonomialHeight
