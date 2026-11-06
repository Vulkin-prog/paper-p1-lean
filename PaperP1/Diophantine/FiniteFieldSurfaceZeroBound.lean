module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! # A proved coarse finite-field bound for actual three-coordinate hypersurface zeros -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldSurfaceZeroBound

open Finset

theorem multivariate_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : MvPolynomial (Fin 3) F) (hP : P ≠ 0) (S : Finset (Fin 3 → F))
    (hS : ∀ z ∈ S, MvPolynomial.eval z P = 0) :
    S.card ≤ P.totalDegree * Fintype.card F ^ 2 := by
  classical
  let Z := (univ : Finset (Fin 3 → F)).filter (fun z ↦ MvPolynomial.eval z P = 0)
  have hsub : S ⊆ Z := fun z hz ↦ mem_filter.mpr ⟨mem_univ _, hS z hz⟩
  have hs : (Z.card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ 3 ≤
      (P.totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    simpa only [Fintype.piFinset_univ, card_univ] using
      MvPolynomial.schwartz_zippel_totalDegree hP (univ : Finset F)
  have hN : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hm := (div_le_div_iff₀ (pow_pos hN 3) hN).mp hs
  have hm' : (Z.card : ℚ≥0) * Fintype.card F ≤
      ((P.totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ 2) * Fintype.card F := by
    simpa only [pow_succ, mul_assoc] using hm
  have hb : (Z.card : ℚ≥0) ≤ (P.totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ 2 :=
    (mul_le_mul_iff_of_pos_right hN).mp hm'
  have hn : Z.card ≤ P.totalDegree * Fintype.card F ^ 2 := by exact_mod_cast hb
  exact (card_le_card hsub).trans hn

end PaperP1.FiniteFieldSurfaceZeroBound
