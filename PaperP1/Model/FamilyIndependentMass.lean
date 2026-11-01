module

public import PaperP1.Model.MissingBlockProbabilities
public import PaperP1.Model.ConnectedWindowFamilies

/-! # Actual independent masses retain all exact heterogeneous marginals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FamilyIndependentMass

open Finset PaperP1.Model.InfiniteStarts

def independentMass (F : Finset (Finset ℕ)) (L : ℕ) : ℝ :=
  ∑ I ∈ F, ∏ x ∈ I, infiniteMarginal x L

theorem finite_mass_cap (F : Finset (Finset ℕ)) (G : Finset ℕ) (L r : ℕ) (R : ℝ)
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.card = r) (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ R) :
    independentMass F L ≤ (F.card : ℝ) * R ^ r := by
  calc
    _ ≤ ∑ _I ∈ F, R ^ r := by
      apply sum_le_sum
      intro I hI
      have hprod : (∏ x ∈ I, infiniteMarginal x L) ≤ ∏ _x ∈ I, R :=
        prod_le_prod₀ (fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
          (fun x hx ↦ hcap x ((hF I hI).1 hx))
      exact hprod.trans_eq (by simp only [prod_const, (hF I hI).2])
    _ = _ := by simp

end PaperP1.FamilyIndependentMass
