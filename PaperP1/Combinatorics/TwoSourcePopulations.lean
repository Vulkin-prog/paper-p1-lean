module

public import PaperP1.Arithmetic.MultiAnchorSaturation
public import PaperP1.Model.FiniteRademacher
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Literal two-source populations for rare windows and saturated certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSourcePopulations

open Finset PaperP1.Model PaperP1.MultiAnchorSaturation

def markedPairs (A G : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((A ×ˢ G).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ {p.1, p.2}

theorem marked_properties {A G E : Finset ℕ} (hA : A ⊆ G) (hE : E ∈ markedPairs A G) :
    E ⊆ G ∧ E.card = 2 := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hE
  obtain ⟨hpG, hne⟩ := mem_filter.mp hp
  obtain ⟨hpA, hqG⟩ := mem_product.mp hpG
  refine ⟨?_, by simp only [card_pair hne]⟩
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hA hpA
  · exact (mem_singleton.mp hx) ▸ hqG

theorem marked_card (A G : Finset ℕ) : (markedPairs A G).card ≤ A.card * G.card := by
  exact (card_image_le).trans ((card_filter_le _ _).trans_eq (card_product A G))

theorem marked_cover {A G I : Finset ℕ} (hI : I ⊆ G) (hcard : 2 ≤ I.card)
    (hmarked : ∃ x ∈ I, x ∈ A) : ∃ E ∈ markedPairs A G, E ⊆ I := by
  obtain ⟨x, hx, hxA⟩ := hmarked
  have hother : (I.erase x).Nonempty := card_pos.mp (by rw [card_erase_of_mem hx]; omega)
  obtain ⟨y, hy⟩ := hother
  obtain ⟨hyx, hyI⟩ := mem_erase.mp hy
  refine ⟨{x, y}, mem_image.mpr ⟨(x, y), mem_filter.mpr
    ⟨mem_product.mpr ⟨hxA, hI hyI⟩, hyx.symm⟩, rfl⟩, ?_⟩
  exact insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hyI⟩

theorem pair_card (A : Finset ℕ) : (A.powersetCard 2).card ≤ A.card ^ 2 := by
  rw [card_powersetCard]
  exact Nat.choose_le_pow _ _

theorem pair_cover {A I : Finset ℕ} (hI : I ⊆ A) (hcard : 2 ≤ I.card) :
    ∃ E ∈ A.powersetCard 2, E ⊆ I := by
  obtain ⟨E, hEI, hEcard⟩ := exists_subset_card_eq hcard
  exact ⟨E, mem_powersetCard.mpr ⟨hEI.trans hI, hEcard⟩, hEI⟩

def saturatedPairs (t L N : ℕ) (Y : ℝ) : Finset (Finset ℕ) :=
  (dyadicBlock N).biUnion fun x ↦ (outgoing t (L + 1) N Y x).image fun y ↦ {x, y}

theorem saturated_properties {t L N : ℕ} {Y : ℝ} {E : Finset ℕ}
    (hE : E ∈ saturatedPairs t L N Y) : E ⊆ dyadicBlock N ∧ E.card = 2 := by
  obtain ⟨x, hx, hxy⟩ := mem_biUnion.mp hE
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hxy
  obtain ⟨hyD, hedge⟩ := (mem_outgoing t (L + 1) N Y x y).mp hy
  exact ⟨insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hyD⟩, card_pair hedge.1⟩

theorem saturated_card (t L N : ℕ) (Y D : ℝ)
    (hdegree : ∀ x ∈ dyadicBlock N, ((outgoing t (L + 1) N Y x).card : ℝ) ≤ D) :
    ((saturatedPairs t L N Y).card : ℝ) ≤ N * D := by
  calc
    _ ≤ ∑ x ∈ dyadicBlock N, (((outgoing t (L + 1) N Y x).image fun y ↦ ({x, y} : Finset ℕ)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (saturatedPairs t L N Y).card ≤ _)
    _ ≤ ∑ x ∈ dyadicBlock N, ((outgoing t (L + 1) N Y x).card : ℝ) := by
      apply sum_le_sum
      intro x _
      exact_mod_cast (card_image_le : ((outgoing t (L + 1) N Y x).image fun y ↦ ({x, y} : Finset ℕ)).card ≤ _)
    _ ≤ ∑ _x ∈ dyadicBlock N, D := sum_le_sum hdegree
    _ = _ := by rw [sum_const, nsmul_eq_mul, dyadicBlock_card]

theorem saturated_cover {t L N : ℕ} {Y : ℝ} {I : Finset ℕ} (hI : I ⊆ dyadicBlock N)
    (hpair : ∃ x ∈ I, ∃ y ∈ I, Edge t (L + 1) N Y x y) :
    ∃ E ∈ saturatedPairs t L N Y, E ⊆ I := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hpair
  refine ⟨{x, y}, mem_biUnion.mpr ⟨x, hI hx, mem_image.mpr
    ⟨y, (mem_outgoing t (L + 1) N Y x y).mpr ⟨hI hy, hxy⟩, rfl⟩⟩, ?_⟩
  exact insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩

end PaperP1.TwoSourcePopulations
