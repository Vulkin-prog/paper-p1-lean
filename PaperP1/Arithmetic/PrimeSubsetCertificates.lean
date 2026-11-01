module

public import PaperP1.Arithmetic.ShortIntervalCongruences
public import PaperP1.Combinatorics.BoundedSubsetWeights
public import Mathlib.Data.Fintype.Pi

/-! # Counting centers by a bounded prime subset and offset assignments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeSubsetCertificates

open Finset PaperP1.ShortIntervalCongruences PaperP1.BoundedSubsetWeights

def qualifying (P : Finset ℕ) (m N : ℕ) : Finset (Finset ℕ) :=
  (boundedSubsets P m).filter (fun S ↦ N ≤ S.prod id)

def targets (P : Finset ℕ) (m b U N : ℕ) (offset : Fin b → ℕ) : Finset ℕ :=
  (qualifying P m N).biUnion fun S ↦
    univ.biUnion fun w : S → Fin b ↦ fibre U N (fun p : S ↦ p.val) (fun p ↦ offset (w p))

theorem mem_qualifying (P S : Finset ℕ) (m N : ℕ) :
    S ∈ qualifying P m N ↔ S ⊆ P ∧ S.card ≤ m ∧ N ≤ S.prod id := by
  simp only [qualifying, mem_filter, mem_boundedSubsets, and_assoc]

theorem mem_targets (P : Finset ℕ) (m b U N z : ℕ) (offset : Fin b → ℕ) :
    z ∈ targets P m b U N offset ↔ z ∈ Ico U (U + N) ∧
      ∃ S : Finset ℕ, S ⊆ P ∧ S.card ≤ m ∧ N ≤ S.prod id ∧
        ∃ w : S → Fin b, ∀ p : S, p.val ∣ z - 1 + offset (w p) := by
  constructor
  · intro hz
    obtain ⟨S, hS, hz⟩ := mem_biUnion.mp hz
    obtain ⟨w, _, hz⟩ := mem_biUnion.mp hz
    obtain ⟨hSP, hSm, hSN⟩ := (mem_qualifying P S m N).mp hS
    obtain ⟨hz, hdiv⟩ := (mem_fibre U N _ _ z).mp hz
    exact ⟨hz, S, hSP, hSm, hSN, w, hdiv⟩
  · rintro ⟨hz, S, hSP, hSm, hSN, w, hdiv⟩
    exact mem_biUnion.mpr ⟨S, (mem_qualifying P S m N).mpr ⟨hSP, hSm, hSN⟩,
      mem_biUnion.mpr ⟨w, mem_univ _, (mem_fibre U N _ _ z).mpr ⟨hz, hdiv⟩⟩⟩

theorem primes_pairwise_coprime (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Pairwise (fun p q : S ↦ Nat.Coprime p.val q.val) := by
  intro p q hpq
  apply (Nat.coprime_primes (hS p.val p.property) (hS q.val q.property)).mpr
  exact fun h ↦ hpq (Subtype.ext h)

theorem card_targets_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (m b U N : ℕ) (hU : 1 ≤ U) (offset : Fin b → ℕ) :
    ((targets P m b U N offset).card : ℝ) ≤ weightSum P (b : ℝ) m := by
  have hcard : (targets P m b U N offset).card ≤ ∑ S ∈ boundedSubsets P m, b ^ S.card := by
    calc
      _ ≤ ∑ S ∈ qualifying P m N,
          (univ.biUnion fun w : S → Fin b ↦ fibre U N (fun p : S ↦ p.val) (fun p ↦ offset (w p))).card :=
        card_biUnion_le
      _ ≤ ∑ S ∈ qualifying P m N, b ^ S.card := by
        apply sum_le_sum
        intro S hS
        obtain ⟨hSP, _, hSN⟩ := (mem_qualifying P S m N).mp hS
        have hcop := primes_pairwise_coprime S (fun p hp ↦ hP p (hSP hp))
        calc
          _ ≤ ∑ w : S → Fin b, (fibre U N (fun p : S ↦ p.val) (fun p ↦ offset (w p))).card := card_biUnion_le
          _ ≤ ∑ _w : S → Fin b, 1 := by
            apply sum_le_sum
            intro w _
            apply card_fibre_le_one U N _ _ hU hcop
            change N ≤ ∏ p : S, p.val
            rw [show (∏ p : S, p.val) = S.prod id from prod_coe_sort S id]
            exact hSN
          _ = b ^ S.card := by simp only [sum_const, card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_coe, smul_eq_mul, mul_one]
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  unfold weightSum
  exact_mod_cast hcard

theorem card_targets_le_full (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (m b U N : ℕ) (hU : 1 ≤ U) (offset : Fin b → ℕ) :
    ((targets P m b U N offset).card : ℝ) ≤ (1 + (b : ℝ)) ^ P.card := by
  calc
    _ ≤ weightSum P (b : ℝ) m := card_targets_le P hP m b U N hU offset
    _ ≤ ∑ S ∈ P.powerset, (b : ℝ) ^ S.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
    _ = _ := powerset_weight_identity P (b : ℝ)

end PaperP1.PrimeSubsetCertificates
