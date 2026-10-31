module

public import PaperP1.Arithmetic.ShortIntervalCongruences
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Prod

/-! # Finite product-certificate counting with a fixed source family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProductCertificate

open Finset PaperP1.ShortIntervalCongruences

variable {ι : Type*} [Fintype ι]

def divisorPool (v : ι → ℕ) : Finset ℕ :=
  (univ.biUnion fun a ↦ (v a).divisors).filter (1 < ·)

def alphabet (v : ι → ℕ) (B : ℕ) : Finset (ℕ × ℕ) := divisorPool v ×ˢ range B

def codes (v : ι → ℕ) (B k : ℕ) : Finset (Fin k → ℕ × ℕ) :=
  Fintype.piFinset fun _ : Fin k ↦ alphabet v B

def validCodes (v : ι → ℕ) (B k N : ℕ) : Finset (Fin k → ℕ × ℕ) := by
  classical
  exact (codes v B k).filter fun c ↦
    Pairwise (fun i j ↦ Nat.Coprime (c i).1 (c j).1) ∧ N ≤ ∏ i, (c i).1

def targets (v : ι → ℕ) (B k U N : ℕ) : Finset ℕ :=
  (validCodes v B k N).biUnion fun c ↦ fibre U N (fun i ↦ (c i).1) (fun i ↦ (c i).2)

theorem mem_divisorPool (v : ι → ℕ) (hv : ∀ a, 0 < v a) (g : ℕ) :
    g ∈ divisorPool v ↔ 1 < g ∧ ∃ a, g ∣ v a := by
  constructor
  · intro hg
    obtain ⟨hg, hg1⟩ := mem_filter.mp hg
    obtain ⟨a, _, hga⟩ := mem_biUnion.mp hg
    exact ⟨hg1, a, (Nat.mem_divisors.mp hga).1⟩
  · rintro ⟨hg, a, hga⟩
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨a, mem_univ _, Nat.mem_divisors.mpr ⟨hga, (hv a).ne'⟩⟩, hg⟩

theorem mem_codes (v : ι → ℕ) (B k : ℕ) (c : Fin k → ℕ × ℕ) :
    c ∈ codes v B k ↔ ∀ i, (c i).1 ∈ divisorPool v ∧ (c i).2 < B := by
  simp only [codes, Fintype.mem_piFinset, alphabet, mem_product, mem_range]

theorem mem_validCodes (v : ι → ℕ) (B k N : ℕ) (c : Fin k → ℕ × ℕ) :
    c ∈ validCodes v B k N ↔ c ∈ codes v B k ∧
      Pairwise (fun i j ↦ Nat.Coprime (c i).1 (c j).1) ∧ N ≤ ∏ i, (c i).1 := by
  classical
  exact mem_filter

theorem mem_targets (v : ι → ℕ) (hv : ∀ a, 0 < v a) (B k U N z : ℕ) :
    z ∈ targets v B k U N ↔ z ∈ Finset.Ico U (U + N) ∧
      ∃ G w : Fin k → ℕ,
        (∀ i, 1 < G i ∧ ∃ a, G i ∣ v a) ∧ (∀ i, w i < B) ∧
        Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧ N ≤ ∏ i, G i ∧
        ∀ i, G i ∣ z - 1 + w i := by
  constructor
  · intro hz
    obtain ⟨c, hc, hz⟩ := mem_biUnion.mp hz
    obtain ⟨hc, hcop, hprod⟩ := (mem_validCodes v B k N c).mp hc
    have hletters := (mem_codes v B k c).mp hc
    obtain ⟨hz, hdiv⟩ := (mem_fibre U N _ _ z).mp hz
    refine ⟨hz, (fun i ↦ (c i).1), (fun i ↦ (c i).2), ?_, ?_, hcop, hprod, hdiv⟩
    · intro i
      exact (mem_divisorPool v hv _).mp (hletters i).1
    · exact fun i ↦ (hletters i).2
  · rintro ⟨hz, G, w, hG, hw, hcop, hprod, hdiv⟩
    let c : Fin k → ℕ × ℕ := fun i ↦ (G i, w i)
    have hc : c ∈ codes v B k := (mem_codes v B k c).mpr
      (fun i ↦ ⟨(mem_divisorPool v hv _).mpr (hG i), hw i⟩)
    exact mem_biUnion.mpr ⟨c, (mem_validCodes v B k N c).mpr ⟨hc, hcop, hprod⟩,
      (mem_fibre U N _ _ z).mpr ⟨hz, hdiv⟩⟩

theorem card_divisorPool_le (v : ι → ℕ) :
    (divisorPool v).card ≤ ∑ a, (v a).divisors.card := by
  exact (card_filter_le _ _).trans card_biUnion_le

theorem card_alphabet_le (v : ι → ℕ) (B : ℕ) :
    (alphabet v B).card ≤ B * ∑ a, (v a).divisors.card := by
  rw [alphabet, card_product, card_range]
  exact (Nat.mul_le_mul_right B (card_divisorPool_le v)).trans_eq (Nat.mul_comm _ _)

theorem card_codes (v : ι → ℕ) (B k : ℕ) : (codes v B k).card = (alphabet v B).card ^ k :=
  Fintype.card_piFinset_const _ _

theorem card_targets_le_codes (v : ι → ℕ) (B k U N : ℕ) (hU : 1 ≤ U) :
    (targets v B k U N).card ≤ (codes v B k).card := by
  calc
    _ ≤ ∑ c ∈ validCodes v B k N, (fibre U N (fun i ↦ (c i).1) (fun i ↦ (c i).2)).card := card_biUnion_le
    _ ≤ ∑ _c ∈ validCodes v B k N, 1 := by
      apply sum_le_sum
      intro c hc
      obtain ⟨_, hcop, hprod⟩ := (mem_validCodes v B k N c).mp hc
      exact card_fibre_le_one U N _ _ hU hcop hprod
    _ = (validCodes v B k N).card := by simp
    _ ≤ _ := by classical exact card_filter_le _ _

theorem card_targets_le (v : ι → ℕ) (B k U N : ℕ) (hU : 1 ≤ U) :
    (targets v B k U N).card ≤ (B * ∑ a, (v a).divisors.card) ^ k := by
  calc
    _ ≤ (codes v B k).card := card_targets_le_codes v B k U N hU
    _ = (alphabet v B).card ^ k := card_codes v B k
    _ ≤ _ := Nat.pow_le_pow_left (card_alphabet_le v B) k

end PaperP1.ProductCertificate
