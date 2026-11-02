module

public import PaperP1.Algebra.TripleCentering
public import PaperP1.Algebra.SubsetPowerSums
public import PaperP1.Combinatorics.TriplePairIncidence

/-! # Exact third factorial cumulant from heterogeneous joint data -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ThirdFactorialCumulant

open Finset PaperP1.Algebra

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def jointSum (q : Finset ι → R) (G : Finset ι) (r : ℕ) : R := ∑ I ∈ G.powersetCard r, q I

def weightedPairs (p : ι → R) (q : Finset ι → R) (G : Finset ι) : R :=
  ∑ e ∈ G.powersetCard 2, q e * ∑ x ∈ e, p x

def fromSubsetData (p : ι → R) (q : Finset ι → R) (G : Finset ι) : R :=
  6 * jointSum q G 3 - 6 * jointSum q G 2 * (∑ x ∈ G, p x) + 2 * (∑ x ∈ G, p x) ^ 3

theorem pair_formula (p : ι → R) (q : Finset ι → R) (h0 : q ∅ = 1)
    (hs : ∀ x, q {x} = p x) (e : Finset ι) (he : e.card = 2) :
    centeredCoefficient p q e = q e - ∏ x ∈ e, p x := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  rw [centeredCoefficient_pair_eq_covariance p q hxy h0 (hs x) (hs y), prod_pair hxy]

theorem triple_formula (p : ι → R) (q : Finset ι → R) (h0 : q ∅ = 1)
    (hs : ∀ x, q {x} = p x) (T : Finset ι) (hT : T.card = 3) :
    centeredCoefficient p q T = q T - (∑ z ∈ T, q (T.erase z) * p z) + 2 * ∏ x ∈ T, p x := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hT
  rw [TripleCentering.normalized p q hxy hxz hyz h0 (hs x) (hs y) (hs z)]
  simp [hxy, hxz, hyz, erase_insert_of_ne hxy, erase_insert_of_ne hxz, erase_insert_of_ne hyz]
  ring

theorem complementary_pair_sum (p : ι → R) (q : Finset ι → R) (G : Finset ι) :
    (∑ T ∈ G.powersetCard 3, ∑ z ∈ T, q (T.erase z) * p z) =
      jointSum q G 2 * (∑ x ∈ G, p x) - weightedPairs p q G := by
  rw [TriplePairIncidence.erased_sum G 2 (fun e z ↦ q e * p z)]
  unfold jointSum weightedPairs
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  rw [← mul_sum, ← mul_sub, sum_sdiff_eq_sub (mem_powersetCard.mp he).1]

theorem triple_sum (p : ι → R) (q : Finset ι → R) (G : Finset ι)
    (h0 : q ∅ = 1) (hs : ∀ x, q {x} = p x) :
    (∑ T ∈ G.powersetCard 3, centeredCoefficient p q T) =
      jointSum q G 3 - jointSum q G 2 * (∑ x ∈ G, p x) + weightedPairs p q G +
        2 * SubsetPowerSums.elementary p G 3 := by
  have heq : (∑ T ∈ G.powersetCard 3, centeredCoefficient p q T) =
      ∑ T ∈ G.powersetCard 3, (q T - (∑ z ∈ T, q (T.erase z) * p z) + 2 * ∏ x ∈ T, p x) := by
    apply sum_congr rfl
    intro T hT
    exact triple_formula p q h0 hs T (mem_powersetCard.mp hT).2
  rw [heq, sum_add_distrib, sum_sub_distrib, ← mul_sum, complementary_pair_sum]
  change jointSum q G 3 - (jointSum q G 2 * (∑ x ∈ G, p x) - weightedPairs p q G) +
    2 * SubsetPowerSums.elementary p G 3 = _
  ring

theorem weighted_centered_pairs (p : ι → R) (q : Finset ι → R) (G : Finset ι)
    (h0 : q ∅ = 1) (hs : ∀ x, q {x} = p x) :
    (∑ e ∈ G.powersetCard 2, (∑ x ∈ e, p x) * centeredCoefficient p q e) =
      weightedPairs p q G - SubsetPowerSums.pairPower p G := by
  unfold weightedPairs SubsetPowerSums.pairPower
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  rw [pair_formula p q h0 hs e (mem_powersetCard.mp he).2]
  ring

theorem exact_formula (p : ι → R) (q : Finset ι → R) (G : Finset ι)
    (h0 : q ∅ = 1) (hs : ∀ x, q {x} = p x) :
    fromSubsetData p q G =
      6 * (∑ T ∈ G.powersetCard 3, centeredCoefficient p q T) -
      6 * (∑ e ∈ G.powersetCard 2, (∑ x ∈ e, p x) * centeredCoefficient p q e) +
      2 * ∑ x ∈ G, (p x) ^ 3 := by
  rw [triple_sum p q G h0 hs, weighted_centered_pairs p q G h0 hs, fromSubsetData,
    SubsetPowerSums.cube]
  ring

end PaperP1.ThirdFactorialCumulant
