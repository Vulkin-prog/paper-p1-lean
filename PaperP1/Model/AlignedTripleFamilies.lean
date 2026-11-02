module

public import PaperP1.Arithmetic.AlignedTargetCount
public import PaperP1.Model.InfiniteJointMoments
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # All pairwise aligned triples are covered by an actual two-target star -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTripleFamilies

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AlignedTargetCount
  PaperP1.CompressedTargetAlignment

local instance alignedTripleFamiliesDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def AlignedFamily (L : ℕ) (I : Finset ℕ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → Aligned 1 x y L

def families (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  (G.powersetCard 3).filter (AlignedFamily L)

def starPopulation (G : Finset ℕ) (L : ℕ) : Finset (Σ _x : ℕ, ℕ × ℕ) :=
  G.sigma fun x ↦ targets G 1 x L ×ˢ targets G 1 x L

def familyOf (z : Σ _x : ℕ, ℕ × ℕ) : Finset ℕ := {z.1, z.2.1, z.2.2}

def jointMass (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ I ∈ families G L, infiniteJointMoment L I

theorem mem_families {G I : Finset ℕ} {L : ℕ} :
    I ∈ families G L ↔ I ⊆ G ∧ I.card = 3 ∧ AlignedFamily L I := by
  simp only [families, mem_filter, mem_powersetCard, and_assoc]

theorem family_cover (G : Finset ℕ) (L : ℕ) :
    families G L ⊆ (starPopulation G L).image familyOf := by
  intro I hI
  obtain ⟨hIG, hcard, halign⟩ := mem_families.mp hI
  obtain ⟨x, y, z, hxy, hxz, _hyz, rfl⟩ := card_eq_three.mp hcard
  have hxI : x ∈ ({x, y, z} : Finset ℕ) := by simp
  have hyI : y ∈ ({x, y, z} : Finset ℕ) := by simp
  have hzI : z ∈ ({x, y, z} : Finset ℕ) := by simp
  refine mem_image.mpr ⟨⟨x, (y, z)⟩, ?_, rfl⟩
  exact mem_sigma.mpr ⟨hIG hxI, mem_product.mpr
    ⟨mem_filter.mpr ⟨hIG hyI, halign x hxI y hyI hxy⟩,
      mem_filter.mpr ⟨hIG hzI, halign x hxI z hzI hxz⟩⟩⟩

theorem star_card (G : Finset ℕ) (L : ℕ) :
    (starPopulation G L).card = ∑ x ∈ G, (targets G 1 x L).card ^ 2 := by
  rw [starPopulation, card_sigma]
  apply sum_congr rfl
  intro x _
  rw [card_product, pow_two]

theorem card_cap (G : Finset ℕ) (L K : ℕ) (hcap : ∀ x ∈ G, (targets G 1 x L).card ≤ K) :
    (families G L).card ≤ G.card * K ^ 2 := by
  calc
    _ ≤ ((starPopulation G L).image familyOf).card := card_le_card (family_cover G L)
    _ ≤ (starPopulation G L).card := card_image_le
    _ = _ := star_card G L
    _ ≤ ∑ _x ∈ G, K ^ 2 := sum_le_sum (fun x hx ↦ Nat.pow_le_pow_left (hcap x hx) 2)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]

theorem card_bound (G : Finset ℕ) (L : ℕ) :
    (families G L).card ≤ G.card * 25 * (L + 1) ^ 20 := by
  have h := card_cap G L (5 * (L + 1) ^ 10)
    (fun x _ ↦ by simpa only [show 4 * (1 : ℕ) + 1 = 5 by norm_num] using card_power_bound G 1 x L)
  convert h using 1
  ring

end PaperP1.AlignedTripleFamilies
