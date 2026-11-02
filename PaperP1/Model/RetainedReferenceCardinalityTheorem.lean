module

public import PaperP1.Model.RetainedDeficitGrouping
public import PaperP1.Probability.FiniteLawEmbedding

/-! # Companion T17.2 with the exact source cardinality coefficients and total deficits -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedReferenceCardinalityTheorem

open Finset PaperP1.Probability PaperP1.RegularStarts PaperP1.RetainedReferenceTheorem
  PaperP1.RetainedCardinalityDeficits PaperP1.RetainedDeficitGrouping

def Ftotal (N L : ℕ) : ℝ :=
  ∑ r ∈ range ((regularStarts N L).card + 1), (2 : ℝ) ^ r * firstCoefficient N L r

def Gtotal (H : ℝ) (N L : ℕ) : ℝ :=
  ∑ r ∈ range ((regularStarts N L).card + 1), (2 : ℝ) ^ r * secondCoefficient H N L r

theorem deficit_polynomial_grouped {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    firstDeficit N L + secondDeficit H N L =
      ∑ r ∈ range ((regularStarts N L).card + 1),
        scalar (firstCoefficient N L r + secondCoefficient H N L r) * forwardDifference ^ r := by
  rw [firstDeficit_grouped hN hL, secondDeficit_grouped hN hL H, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _hr
  rw [map_add, add_mul]

theorem Ftotal_nonneg (N L : ℕ) : 0 ≤ Ftotal N L :=
  sum_nonneg (fun r _hr ↦ mul_nonneg (by positivity) (firstCoefficient_nonneg N L r))

theorem Gtotal_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ Gtotal H N L :=
  sum_nonneg (fun r _hr ↦ mul_nonneg (by positivity) (secondCoefficient_nonneg H N L r))

theorem Ftotal_eq_tsum (N L : ℕ) : Ftotal N L = ∑' r : ℕ, (2 : ℝ) ^ r * firstCoefficient N L r := by
  symm
  apply tsum_eq_sum
  intro r hr
  have hlarge : (regularStarts N L).card < r := by
    simp only [mem_range, not_lt] at hr
    omega
  rw [firstCoefficient_zero_large N L r hlarge, mul_zero]

theorem Gtotal_eq_tsum {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    Gtotal H N L = ∑' r : ℕ, (2 : ℝ) ^ r * secondCoefficient H N L r := by
  symm
  apply tsum_eq_sum
  intro r hr
  have hlarge : (regularStarts N L).card < r := by
    simp only [mem_range, not_lt] at hr
    omega
  rw [secondCoefficient_zero_large hN H r hlarge, mul_zero]

theorem companion_T17_2 {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    actualReference H N L = binomialReference H N L -
      ∑ r ∈ range ((regularStarts N L).card + 1),
        scalar (firstCoefficient N L r + secondCoefficient H N L r) * forwardDifference ^ r ∧
    l1Norm (actualReference H N L - binomialReference H N L) ≤ Ftotal N L + Gtotal H N L := by
  constructor
  · rw [← deficit_polynomial_grouped hN hL H, finite_identity hN hL H]
    ring1
  · have h := finite_norm_bound hN hL H
    rw [firstMass_grouped hN hL, secondMass_grouped hN hL H] at h
    exact h

theorem embed_sum {ι : Type*} (s : Finset ι) (f : ι → SignedLaw ℝ) :
    FiniteLawEmbedding.embed (∑ i ∈ s, f i) = ∑ i ∈ s, FiniteLawEmbedding.embed (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    apply AtomicSignedLaw.signedMeasure_ext_singleton
    intro k
    rw [FiniteLawEmbedding.embed_singleton]
    simp
  | insert i s hi ih => rw [sum_insert hi, FiniteLawEmbedding.embed_add, ih, sum_insert hi]

theorem companion_T17_2_measures {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    FiniteLawEmbedding.embed (actualReference H N L) = FiniteLawEmbedding.embed (binomialReference H N L) -
      ∑ r ∈ range ((regularStarts N L).card + 1),
        (firstCoefficient N L r + secondCoefficient H N L r) •
          FiniteLawEmbedding.embed ((forwardDifference : SignedLaw ℝ) ^ r) ∧
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (actualReference H N L) -
      FiniteLawEmbedding.embed (binomialReference H N L)) {k}|) ≤ Ftotal N L + Gtotal H N L := by
  obtain ⟨hid, hnorm⟩ := companion_T17_2 hN hL H
  constructor
  · rw [hid, FiniteLawEmbedding.embed_sub, embed_sum]
    simp only [FiniteLawEmbedding.embed_scalar_mul]
  · rwa [FiniteLawEmbedding.l1Norm_eq_signed_singleton_tsum, FiniteLawEmbedding.embed_sub] at hnorm

end PaperP1.RetainedReferenceCardinalityTheorem
