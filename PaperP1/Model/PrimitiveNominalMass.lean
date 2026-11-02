module

public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Combinatorics.OrderedSubsetWeights

/-! # Nominal homogeneous primitive weights and their exact ordered enumeration -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveNominalMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Probability
  PaperP1.ConnectedWindowFamilies

def weight (L : ℕ) (I : Finset ℕ) : ℝ :=
  ((2 ^ L : ℝ)⁻¹) ^ I.card * (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ)

def mass (F : Finset (Finset ℕ)) (L : ℕ) : ℝ := ∑ I ∈ F, weight L I

theorem weight_nonneg (L : ℕ) (I : Finset ℕ) : 0 ≤ weight L I := by
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) _)
    (pow_nonneg (by norm_num) _)

theorem primitive_mass_cap (F : Finset (Finset ℕ)) (L r : ℕ) (hr : 0 < r)
    (hF : ∀ I ∈ F, I.card = r ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x) :
    mass F L ≤ (F.card : ℝ) * (((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ L : ℝ)) := by
  calc
    _ ≤ ∑ _I ∈ F, ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ L : ℝ) := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hcard, hprim, hpos⟩ := hF I hI
      have hne : I.Nonempty := card_pos.mp (hcard.symm ▸ hr)
      unfold weight
      rw [hcard]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (PrimitiveWindowMass.primitive_nullity_le L I hne hprim hpos)) (by positivity)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem ordered_sum (G : Finset ℕ) (L r : ℕ) (F : Finset (Finset ℕ)) (hF : F ⊆ G.powersetCard r) :
    (∑ t ∈ OrderedSubsetWeights.population G r F,
      ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) (tupleValues t) : ℝ)) =
        (r.factorial : ℝ) * mass F L := by
  simpa only [weight, tupleValues_card, mass] using OrderedSubsetWeights.weighted_sum G r F hF (weight L)

end PaperP1.PrimitiveNominalMass
