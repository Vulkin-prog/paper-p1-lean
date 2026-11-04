module

public import PaperP1.Arithmetic.AsymmetricSupportEnvelope

/-! # Actual asymmetric support on a fixed expansion of the dyadic range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricSupportEnvelope

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricSupportEnvelope

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def block (N Q : ℕ) : Finset ℕ := Ico N (N + Q * N)

theorem dyadic_subset_block {N Q : ℕ} (hQ : 1 ≤ Q) : PaperP1.Model.dyadicBlock N ⊆ block N Q := by
  have hNM : N ≤ Q * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
  intro y hy
  obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
  apply mem_Ico.mpr
  change N ≤ y ∧ y < N + Q * N
  omega

def population (N Q L H : ℕ) (old : ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  (block N Q ×ˢ block N Q).filter fun p ↦ 0 < loss H (old p.1) p.2 L

theorem translated_old {H R x n : ℕ} (hx : R < x) (hH : 2 * R + 1 ≤ H)
    (hn : |(n : ℤ) - x| ≤ (R : ℤ)) :
    n ∈ Ico ((x - R + 1) - 1) ((x - R + 1) - 1 + H) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply mem_Ico.mpr
  omega

theorem translated_new {L H R y n : ℕ} (hy : R < y) (hR : L + 1 ≤ R)
    (hH : 2 * R + 1 ≤ H) (hn : n ∈ NormalizedWindowSets.values y L) :
    n ∈ Ico ((y - R + 1) - 1) ((y - R + 1) - 1 + H) := by
  have hypos : 0 < y := by omega
  rw [NormalizedWindowSets.values_eq_interval hypos] at hn
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hn
  apply mem_Ico.mpr
  omega

theorem translated_related {L H R x y : ℕ} {old : Finset ℕ}
    (hx : R < x) (hy : R < y) (hR : L + 1 ≤ R) (hH : 2 * R + 1 ≤ H)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (hloss : 0 < loss H old y L) :
    TruncatedAsymmetricSupport.Related H (x - R + 1) (y - R + 1) := by
  obtain ⟨A, I, hA, hI, _heven, hcard, he⟩ :=
    AsymmetricLossSelections.exists_selections (by omega : 0 < y) hloss
  exact ⟨A, I, fun n hn ↦ translated_old hx hH (hold n (hA hn)),
    fun n hn ↦ translated_new hy hR hH (hI hn), hcard, he.symm⟩

theorem population_card {N Q L H R : ℕ} (old : ℕ → Finset ℕ) (hRN : R < N)
    (hR : L + 1 ≤ R) (hH : 2 * R + 1 ≤ H)
    (hold : ∀ x ∈ block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) :
    (population N Q L H old).card ≤ (TruncatedAsymmetricSupport.population (Q * N) H (N - R + 1)).card := by
  apply card_le_card_of_injOn (translate R)
  · intro p hp
    obtain ⟨hpblock, hloss⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hpblock
    obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
    obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
    refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩,
      translated_related (by omega) (by omega) hR hH (hold p.1 hx) hloss⟩
    · apply mem_Ico.mpr
      change N - R + 1 ≤ p.1 - R + 1 ∧ p.1 - R + 1 < N - R + 1 + Q * N
      omega
    · apply mem_Ico.mpr
      change N - R + 1 ≤ p.2 - R + 1 ∧ p.2 - R + 1 < N - R + 1 + Q * N
      omega
  · intro p hp q hq he
    have hpD := mem_product.mp (mem_filter.mp hp).1
    have hqD := mem_product.mp (mem_filter.mp hq).1
    have hpx := (mem_Ico.mp hpD.1).1
    have hpy := (mem_Ico.mp hpD.2).1
    have hqx := (mem_Ico.mp hqD.1).1
    have hqy := (mem_Ico.mp hqD.2).1
    have hex := congrArg Prod.fst he
    have hey := congrArg Prod.snd he
    change p.1 - R + 1 = q.1 - R + 1 at hex
    change p.2 - R + 1 = q.2 - R + 1 at hey
    exact Prod.ext (by omega) (by omega)

end PaperP1.ExpandedAsymmetricSupportEnvelope
