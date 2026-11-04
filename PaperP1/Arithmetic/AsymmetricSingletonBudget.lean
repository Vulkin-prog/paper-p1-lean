module

public import PaperP1.Arithmetic.AsymmetricTargetComponents

/-! # Singleton-target components cost only actual defects, bounded degree types and a small old-vertex tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricSingletonBudget

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.AsymmetricEnvelopeRank
  PaperP1.AsymmetricComponentOffsets PaperP1.AsymmetricTargetComponents
  PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def singles (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (components x y L H R hnew hamb old).filter fun c ↦ (right x y H R c).card = 1

def largeSingles (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (K : ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (singles x y L H R hnew hamb old).filter fun c ↦ K < (left x y H R c).card

theorem singletonCount_eq {x y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    singletonCount x y L H R hnew hamb old = (singles x y L H R hnew hamb old).card := by
  rw [singletonCount, TargetComponentBudget.singleton, PinnedTargetBudget.family,
    filter_image, card_image_of_injective _ (PinnedTargetBudget.support_injective _)]
  change ((components x y L H R hnew hamb old).filter fun c ↦
    (PinnedTargetBudget.support _ c ∩ targetPositions L H R hnew hamb).card = 1).card = _
  apply congrArg Finset.card
  apply filter_congr
  intro c hc
  have hfree := ((mem_components x y L H R hnew hamb old c).mp hc).1
  rw [intersection_card hy hnew hamb old c hfree]

theorem singles_cover {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (K : ℕ) :
    singles x y L H R hnew hamb old ⊆
      (isolated x y L H R hnew hamb old ∪ (Icc 1 K).biUnion
        (fun a ↦ AsymmetricComponentHostData.typed x y L H R hnew hamb old a)) ∪
          largeSingles x y L H R hnew hamb old K := by
  intro c hc
  obtain ⟨hcT, hright⟩ := mem_filter.mp hc
  have hfree := ((mem_components x y L H R hnew hamb old c).mp hcT).1
  by_cases htwo : 2 ≤ Fintype.card c.supp
  · by_cases hsmall : (left x y H R c).card ≤ K
    · have hpos := ((AsymmetricComponentOffsets.nonempty hx hy c htwo).1).card_pos
      apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨(left x y H R c).card, mem_Icc.mpr ⟨by omega, hsmall⟩,
        (AsymmetricComponentHostData.mem_typed x y L H R hnew hamb old _ c).mpr ⟨hfree, htwo, rfl, hright⟩⟩
    · exact mem_union_right _ (mem_filter.mpr ⟨hc, by omega⟩)
  · have hp : 0 < Fintype.card c.supp := Fintype.card_pos_iff.mpr ⟨⟨c.out, c.out_eq⟩⟩
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hcT, by omega⟩))

theorem singleton_card_bound {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (K k : ℕ)
    (htyped : ∀ a ∈ Icc 1 K, (AsymmetricComponentHostData.typed x y L H R hnew hamb old a).card ≤ k) :
    singletonCount x y L H R hnew hamb old ≤ (defective y L H).card + K * k +
      (largeSingles x y L H R hnew hamb old K).card := by
  let T := (Icc 1 K).biUnion fun a ↦ AsymmetricComponentHostData.typed x y L H R hnew hamb old a
  have hT : T.card ≤ K * k := by
    calc
      _ ≤ ∑ a ∈ Icc 1 K, (AsymmetricComponentHostData.typed x y L H R hnew hamb old a).card := card_biUnion_le
      _ ≤ ∑ _a ∈ Icc 1 K, k := sum_le_sum htyped
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.card_Icc, Nat.add_sub_cancel]
  have hcover := (card_le_card (singles_cover hx hy hnew hamb old K)).trans (card_union_le _ _)
  have hleft := card_union_le (isolated x y L H R hnew hamb old) T
  have hisolated := isolated_card hx hy hnew hamb old
  have heq := singletonCount_eq (x := x) hy hnew hamb old
  change (singles x y L H R hnew hamb old).card ≤
    (isolated x y L H R hnew hamb old ∪ T).card + (largeSingles x y L H R hnew hamb old K).card at hcover
  omega

theorem large_left_budget {x y L H R : ℕ} (hx : R < x) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (K : ℕ) :
    (K + 1) * (largeSingles x y L H R hnew hamb old K).card ≤ 2 * R + 1 := by
  let Q := largeSingles x y L H R hnew hamb old K
  have hfree (c) (hc : c ∈ Q) : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c := by
    have hcT := (mem_filter.mp (mem_filter.mp hc).1).1
    exact ((mem_components x y L H R hnew hamb old c).mp hcT).1
  have hdisj : (Q : Set (largePrimeGraph (start x R) (start y R) H).ConnectedComponent).Pairwise
      (fun c d ↦ Disjoint (left x y H R c) (left x y H R d)) :=
    fun c _hc d _hd hne ↦ left_disjoint hx c d hne
  have hsub : Q.biUnion (left x y H R) ⊆ BoundedIntegerMotifs.offsets R := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := mem_biUnion.mp hz
    exact ((BoundedIntegerMotifs.subset_offsets R (left x y H R c)).mpr
      (left_bound hnew hamb old hold c (hfree c hc))) hzc
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

theorem singleton_budget {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (K k : ℕ)
    (htyped : ∀ a ∈ Icc 1 K, (AsymmetricComponentHostData.typed x y L H R hnew hamb old a).card ≤ k) :
    (singletonCount x y L H R hnew hamb old : ℝ) ≤ (defective y L H).card + (K : ℝ) * k +
      ((2 * R + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
  have hcard : (singletonCount x y L H R hnew hamb old : ℝ) ≤ (defective y L H).card + (K : ℝ) * k +
      (largeSingles x y L H R hnew hamb old K).card := by
    exact_mod_cast singleton_card_bound hx hy hnew hamb old K k htyped
  have hlarge : ((largeSingles x y L H R hnew hamb old K).card : ℝ) ≤
      ((2 * R + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).mpr
    have hh : ((K + 1 : ℕ) : ℝ) * (largeSingles x y L H R hnew hamb old K).card ≤ ((2 * R + 1 : ℕ) : ℝ) := by
      exact_mod_cast large_left_budget hx hnew hamb old hold K
    linarith only [hh]
  linarith only [hcard, hlarge]

end PaperP1.AsymmetricSingletonBudget
