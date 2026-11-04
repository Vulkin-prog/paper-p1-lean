module

public import PaperP1.Arithmetic.SubsetTargetComponents

/-! # Singleton-target components cost only actual defects, bounded degree types and a small old-vertex tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetSingletonBudget

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.SubsetEnvelopeRank
  PaperP1.AsymmetricComponentOffsets PaperP1.SubsetTargetComponents
  PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def singles (x y H R : ℕ) (U V : Finset ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (components x y H R U V).filter fun c ↦ (right x y H R c).card = 1

def largeSingles (x y H R : ℕ) (U V : Finset ℕ) (K : ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (singles x y H R U V).filter fun c ↦ K < (left x y H R c).card

theorem singletonCount_eq {x y H R : ℕ} (hy : R < y) (U V : Finset ℕ) :
    singletonCount x y H R U V = (singles x y H R U V).card := by
  rw [singletonCount, TargetComponentBudget.singleton, PinnedTargetBudget.family,
    filter_image, card_image_of_injective _ (PinnedTargetBudget.support_injective _)]
  change ((components x y H R U V).filter fun c ↦
    (PinnedTargetBudget.support _ c ∩ SubsetEnvelopeGraph.targets y H R V).card = 1).card = _
  apply congrArg Finset.card
  apply filter_congr
  intro c hc
  have hfree := ((mem_components x y H R U V c).mp hc).1
  rw [intersection_card hy U V c hfree]

theorem singles_cover {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (U V : Finset ℕ) (K : ℕ) :
    singles x y H R U V ⊆
      (isolated x y H R U V ∪ (Icc 1 K).biUnion
        (fun a ↦ SubsetComponentHostData.typed x y H R U V a)) ∪
          largeSingles x y H R U V K := by
  intro c hc
  obtain ⟨hcT, hright⟩ := mem_filter.mp hc
  have hfree := ((mem_components x y H R U V c).mp hcT).1
  by_cases htwo : 2 ≤ Fintype.card c.supp
  · by_cases hsmall : (left x y H R c).card ≤ K
    · have hpos := ((AsymmetricComponentOffsets.nonempty hx hy c htwo).1).card_pos
      apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨(left x y H R c).card, mem_Icc.mpr ⟨by omega, hsmall⟩,
        (SubsetComponentHostData.mem_typed x y H R U V _ c).mpr ⟨hfree, htwo, rfl, hright⟩⟩
    · exact mem_union_right _ (mem_filter.mpr ⟨hc, by omega⟩)
  · have hp : 0 < Fintype.card c.supp := Fintype.card_pos_iff.mpr ⟨⟨c.out, c.out_eq⟩⟩
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hcT, by omega⟩))

theorem singleton_card_bound {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (U V : Finset ℕ) (K k : ℕ)
    (htyped : ∀ a ∈ Icc 1 K, (SubsetComponentHostData.typed x y H R U V a).card ≤ k) :
    singletonCount x y H R U V ≤ (defective y H R V).card + K * k +
      (largeSingles x y H R U V K).card := by
  let T := (Icc 1 K).biUnion fun a ↦ SubsetComponentHostData.typed x y H R U V a
  have hT : T.card ≤ K * k := by
    calc
      _ ≤ ∑ a ∈ Icc 1 K, (SubsetComponentHostData.typed x y H R U V a).card := card_biUnion_le
      _ ≤ ∑ _a ∈ Icc 1 K, k := sum_le_sum htyped
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.card_Icc, Nat.add_sub_cancel]
  have hcover := (card_le_card (singles_cover (H := H) hx hy U V K)).trans (card_union_le _ _)
  have hleft := card_union_le (isolated x y H R U V) T
  have hisolated := isolated_card (H := H) hx hy U V
  have heq := singletonCount_eq (x := x) (H := H) hy U V
  change (singles x y H R U V).card ≤
    (isolated x y H R U V ∪ T).card + (largeSingles x y H R U V K).card at hcover
  omega

theorem large_left_budget {x y H R : ℕ} (hx : R < x) (U V : Finset ℕ)
    (hold : ∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ)) (K : ℕ) :
    (K + 1) * (largeSingles x y H R U V K).card ≤ 2 * R + 1 := by
  let Q := largeSingles x y H R U V K
  have hfree (c) (hc : c ∈ Q) : ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c := by
    have hcT := (mem_filter.mp (mem_filter.mp hc).1).1
    exact ((mem_components x y H R U V c).mp hcT).1
  have hdisj : (Q : Set (largePrimeGraph (start x R) (start y R) H).ConnectedComponent).Pairwise
      (fun c d ↦ Disjoint (left x y H R c) (left x y H R d)) :=
    fun c _hc d _hd hne ↦ left_disjoint hx c d hne
  have hsub : Q.biUnion (left x y H R) ⊆ BoundedIntegerMotifs.offsets R := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := mem_biUnion.mp hz
    exact ((BoundedIntegerMotifs.subset_offsets R (left x y H R c)).mpr
      (SubsetComponentOffsets.left_bound U V hold c (hfree c hc))) hzc
  have hsum : (∑ c ∈ Q, (left x y H R c).card) ≤ 2 * R + 1 := by
    rw [← card_biUnion hdisj]
    exact (card_le_card hsub).trans_eq (BoundedIntegerMotifs.offsets_card R)
  have hmin : (∑ _c ∈ Q, (K + 1)) ≤ ∑ c ∈ Q, (left x y H R c).card := by
    apply sum_le_sum
    intro c hc
    have hh := (mem_filter.mp hc).2
    omega
  have hh := hmin.trans hsum
  simpa only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using hh

theorem singleton_budget {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (U V : Finset ℕ)
    (hold : ∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ)) (K k : ℕ)
    (htyped : ∀ a ∈ Icc 1 K, (SubsetComponentHostData.typed x y H R U V a).card ≤ k) :
    (singletonCount x y H R U V : ℝ) ≤ (defective y H R V).card + (K : ℝ) * k +
      ((2 * R + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
  have hcard : (singletonCount x y H R U V : ℝ) ≤ (defective y H R V).card + (K : ℝ) * k +
      (largeSingles x y H R U V K).card := by
    exact_mod_cast singleton_card_bound hx hy U V K k htyped
  have hlarge : ((largeSingles x y H R U V K).card : ℝ) ≤
      ((2 * R + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).mpr
    have hh : ((K + 1 : ℕ) : ℝ) * (largeSingles x y H R U V K).card ≤ ((2 * R + 1 : ℕ) : ℝ) := by
      exact_mod_cast large_left_budget (H := H) hx U V hold K
    linarith only [hh]
  linarith only [hcard, hlarge]

end PaperP1.SubsetSingletonBudget
