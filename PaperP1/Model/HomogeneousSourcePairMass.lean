module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Model.SourcePairPositiveWeight

/-! # Literal full-source homogeneous pair mass, including irregular windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSourcePairMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedPairRankLoss PaperP1.HomogeneousRunMass PaperP1.SubspaceFamilyRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem rank_add_loss {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) + pairLoss x y L = 2 * L := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have hrx := LocalRunRank.squareClass_rank_le x L hx
  have hry := LocalRunRank.squareClass_rank_le y L hy
  unfold pairLoss
  omega

theorem probability_pair {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    probability L {x, y} = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
  have hscale : ((2 ^ L : ℝ)⁻¹) ^ 2 = (2 ^ (2 * L) : ℝ)⁻¹ := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm L 2]
  rw [probability_rank, rank, RetainedNullity.span_pair, hscale, ← rank_add_loss hx hy, pow_add]
  field_simp

theorem positive_power_bound {d : ℕ} (hd : 0 < d) : (2 ^ d : ℝ) ≤ 2 * ((2 ^ d : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ 2 ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ d by omega)
  linarith

theorem probability_positive_loss {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (hdep : 0 < pairLoss x y L) :
    probability L {x, y} ≤ 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 * SourcePairPositiveWeight.setWeight L {x, y} := by
  rw [probability_pair hx hy, SourcePairPositiveWeight.setWeight_pair hxy]
  have h := mul_le_mul_of_nonneg_left (positive_power_bound hdep) (sq_nonneg ((2 ^ L : ℝ)⁻¹))
  simpa only [SourcePairPositiveWeight.weight, mul_left_comm, mul_assoc] using h

theorem regular_loss_eq {N L x y : ℕ} (hx : x ∈ RegularStarts.regularStarts N L)
    (hy : y ∈ RegularStarts.regularStarts N L) (hxy : x ≠ y) :
    pairLoss x y L = runRelativeNullity L {x, y} := by
  have hrx := (RegularStarts.mem_regularStarts.mp hx).2
  have hry := (RegularStarts.mem_regularStarts.mp hy).2
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  rw [hrx, hry] at hdim
  rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ _ _ hxy]
  change 2 * L - Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) =
    Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L)
  omega

theorem regular_dependent_bound {N L : ℕ} {e : Finset ℕ}
    (he : e ∈ (RegularStarts.regularStarts N L).powersetCard 2)
    (hdep : 0 < runRelativeNullity L e) :
    PrimitiveNominalMass.weight L e ≤
      2 * ((2 ^ L : ℝ)⁻¹) ^ 2 * SourcePairPositiveWeight.setWeight L e := by
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp he
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hecard
  have hx := heG (mem_insert_self x {y})
  have hy := heG (mem_insert_of_mem (mem_singleton_self y))
  have hxpos : 0 < x := by have h := mem_Ico.mp (RegularStarts.mem_regularStarts.mp hx).1; omega
  have hypos : 0 < y := by have h := mem_Ico.mp (RegularStarts.mem_regularStarts.mp hy).1; omega
  rw [← regular_weight heG]
  exact probability_positive_loss hxpos hypos hxy (by rwa [regular_loss_eq hx hy hxy])

end PaperP1.HomogeneousSourcePairMass
