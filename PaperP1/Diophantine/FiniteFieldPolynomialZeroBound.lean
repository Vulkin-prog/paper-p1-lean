module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Field.Rat

/-! # An actual Schwartz-Zippel cardinality bound in every positive finite dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldPolynomialZeroBound

open MvPolynomial Finset
open scoped Classical

theorem cardinality {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (hn : 0 < n) (P : MvPolynomial (Fin n) F) (hP : P ≠ 0) (S : Finset (Fin n → F))
    (hS : ∀ x ∈ S, eval x P = 0) :
    S.card ≤ P.totalDegree * Fintype.card F ^ (n - 1) := by
  let Z := (univ : Finset (Fin n → F)).filter (fun x ↦ eval x P = 0)
  have hsub : S ⊆ Z := fun x hx ↦ mem_filter.mpr ⟨mem_univ _, hS x hx⟩
  have hs : (Z.card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n ≤
      (P.totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    simpa only [Fintype.piFinset_univ, card_univ] using schwartz_zippel_totalDegree hP (univ : Finset F)
  have hN : (0 : ℚ≥0) < Fintype.card F := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hm := (div_le_div_iff₀ (pow_pos hN n) hN).mp hs
  have hpow : n = (n - 1) + 1 := by omega
  have hpower : (Fintype.card F : ℚ≥0) ^ n =
      (Fintype.card F : ℚ≥0) ^ (n - 1) * Fintype.card F := by
    conv_lhs => rw [hpow, pow_succ]
  have hm' : (Z.card : ℚ≥0) * Fintype.card F ≤
      ((P.totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ (n - 1)) * Fintype.card F := by
    simpa only [hpower, mul_assoc] using hm
  have hb : (Z.card : ℚ≥0) ≤ (P.totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ (n - 1) :=
    (mul_le_mul_iff_of_pos_right hN).mp hm'
  have hbNat : Z.card ≤ P.totalDegree * Fintype.card F ^ (n - 1) := by exact_mod_cast hb
  exact (card_le_card hsub).trans hbNat

end PaperP1.FiniteFieldPolynomialZeroBound
