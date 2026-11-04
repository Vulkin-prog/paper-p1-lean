module

public import PaperP1.Probability.PositionalFiniteLaw
public import PaperP1.Probability.FiniteCoupling

/-! # Restoring original positions on their common sample

For nested grounds, equal active counts on the same sample imply equal
full configurations. The resulting field coupling charges removed marginals.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalFiniteCoupling

open Finset PaperP1.Algebra PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw

variable {Ω ι : Type*}

local instance positionalFiniteCouplingDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem configuration_eq_of_count_eq (G H : Finset ι) (hGH : G ⊆ H) (J : ι → Ω → Bool) (ω : Ω)
    (hc : Probability.indicatorCount H J ω = Probability.indicatorCount G J ω) :
    configuration G J ω = configuration H J ω := by
  classical
  have hsum := Probability.indicatorCount_sdiff_add hGH J ω
  have hzero : Probability.indicatorCount (H \ G) J ω = 0 := by omega
  unfold configuration
  apply sum_subset hGH
  intro x hxH hxnotG
  have hx : x ∈ H \ G := mem_sdiff.mpr ⟨hxH, hxnotG⟩
  have hpart : (J x ω).toNat ≤ Probability.indicatorCount (H \ G) J ω := by
    change (J x ω).toNat ≤ ∑ y ∈ H \ G, (J y ω).toNat
    exact single_le_sum (fun y _ ↦ Nat.zero_le (J y ω).toNat) hx
  rw [hzero] at hpart
  have hJ : J x ω = false := by cases he : J x ω <;> simp_all
  simp only [hJ, Bool.toNat_false, Finsupp.single_zero]

theorem coupling [Fintype Ω] (P : Probability.FiniteProbability Ω) (G H : Finset ι) (hGH : G ⊆ H)
    (J : ι → Ω → Bool) :
    l1Norm (law H P.weight J - law G P.weight J) ≤
      2 * Probability.disagreementProbability P (Probability.indicatorCount H J) (Probability.indicatorCount G J) := by
  classical
  unfold law
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ ω, l1Norm (scalar (P.weight ω) * atom (configuration H J ω) -
        scalar (P.weight ω) * atom (configuration G J ω)) := l1Norm_sum _ _
    _ ≤ ∑ ω, 2 * P.weight ω *
        (if Probability.indicatorCount H J ω ≠ Probability.indicatorCount G J ω then 1 else 0) := by
      apply sum_le_sum
      intro ω _
      by_cases hc : Probability.indicatorCount H J ω = Probability.indicatorCount G J ω
      · have he := configuration_eq_of_count_eq G H hGH J ω hc
        simp only [he, sub_self, l1Norm_zero, hc, ne_eq, not_true_eq_false, ite_false, mul_zero]
        exact le_rfl
      · simp only [hc, ne_eq, not_false_eq_true, ite_true, mul_one]
        rw [scalar_mul_atom, scalar_mul_atom]
        have hh := l1Norm_sub (AddMonoidAlgebra.single (configuration H J ω) (P.weight ω))
          (AddMonoidAlgebra.single (configuration G J ω) (P.weight ω))
        rw [l1Norm_single, l1Norm_single, abs_of_nonneg (P.weight_nonneg ω)] at hh
        simpa only [two_mul] using hh
    _ = _ := by
      unfold Probability.disagreementProbability finiteExpectation
      rw [mul_sum]
      apply sum_congr rfl
      intro ω _
      ring

theorem restoration_bound [Fintype Ω] (P : Probability.FiniteProbability Ω) (G H : Finset ι) (hGH : G ⊆ H)
    (J : ι → Ω → Bool) :
    l1Norm (law H P.weight J - law G P.weight J) ≤ 2 * ∑ x ∈ H \ G, Probability.exactMarginal P J x :=
  (coupling P G H hGH J).trans (mul_le_mul_of_nonneg_left
    (Probability.disagreement_count_subset_le P hGH J) (by norm_num))

end PaperP1.PositionalFiniteCoupling
