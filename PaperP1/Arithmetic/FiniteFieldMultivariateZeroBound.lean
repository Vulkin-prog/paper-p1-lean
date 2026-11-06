module

public import PaperP1.Diophantine.FiniteFieldSurfaceZeroBound

/-! # Actual finite-field multivariate zero counts in every positive number of variables -/

set_option autoImplicit false

@[expose] public noncomputable section
namespace PaperP1.FiniteFieldMultivariateZeroBound
open Finset
open scoped Classical

theorem cardinality {F : Type*} [Field F] [Fintype F] (n : ℕ) (hn : 0 < n)
    (P : MvPolynomial (Fin n) F) (hP : P ≠ 0) (S : Finset (Fin n → F))
    (hS : ∀ z ∈ S, MvPolynomial.eval z P = 0) :
    S.card ≤ P.totalDegree * Fintype.card F ^ (n-1) := by
  let Z := (univ : Finset (Fin n → F)).filter (fun z ↦ MvPolynomial.eval z P = 0)
  have hsub : S ⊆ Z := fun z hz ↦ mem_filter.mpr ⟨mem_univ _, hS z hz⟩
  have hs : (Z.card : ℚ≥0) / (Fintype.card F : ℚ≥0)^n ≤
      (P.totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    simpa only [Fintype.piFinset_univ, card_univ] using
      MvPolynomial.schwartz_zippel_totalDegree hP (univ : Finset F)
  have hN : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hm := (div_le_div_iff₀ (pow_pos hN n) hN).mp hs
  have hpow : (Fintype.card F : ℚ≥0)^n = (Fintype.card F : ℚ≥0)^(n-1) * Fintype.card F := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ (Fintype.card F : ℚ≥0) (n-1)
  rw [hpow] at hm
  have hb : (Z.card : ℚ≥0) ≤ (P.totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0)^(n-1) := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    simpa only [mul_assoc] using hm
  have hbN : Z.card ≤ P.totalDegree * Fintype.card F^(n-1) := by exact_mod_cast hb
  exact (card_le_card hsub).trans hbN


end PaperP1.FiniteFieldMultivariateZeroBound
