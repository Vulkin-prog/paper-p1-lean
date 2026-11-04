module

public import PaperP1.Model.PrivatePairInteractions
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Exact finite reduction of raw homogeneous edge-pair mass to interactions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousEdgeInteractions

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.HomogeneousRunMass PaperP1.SubspaceFamilyRank

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def space (L : ℕ) (e : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) := span (fun x ↦ squareClassSpace x L) e

def pairs (L : ℕ) (E F : Finset (Finset ℕ)) : Finset (Finset ℕ × Finset ℕ) :=
  (E ×ˢ F).filter fun p ↦ p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) ∧
    space L p.1 ⊓ space L p.2 ≠ ⊥

def mass (L : ℕ) (E F : Finset (Finset ℕ)) : ℝ :=
  ∑ p ∈ pairs L E F, probability L (p.1 ∪ p.2)

def second (L : ℕ) (E : Finset (Finset ℕ)) : ℝ :=
  ∑ p ∈ (E ×ˢ E).filter (fun p ↦ p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)),
    probability L (p.1 ∪ p.2)

theorem independent (L : ℕ) (e f : Finset ℕ) (hi : space L e ⊓ space L f = ⊥) :
    probability L (e ∪ f) = probability L e * probability L f := by
  rw [HomogeneousBlockIntersection.exact L e f]
  change _ * (2 ^ Module.finrank F₂ ↥(space L e ⊓ space L f) : ℝ) = _
  rw [hi, finrank_bot, pow_zero, mul_one]

theorem mass_nonneg (L : ℕ) (E F : Finset (Finset ℕ)) : 0 ≤ mass L E F :=
  sum_nonneg (fun p _ ↦ (probability_pos L (p.1 ∪ p.2)).le)

theorem mass_mono (L : ℕ) {E F E' F' : Finset (Finset ℕ)} (hE : E ⊆ E') (hF : F ⊆ F') :
    mass L E F ≤ mass L E' F' := by
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ ↦ (probability_pos L (p.1 ∪ p.2)).le)
  intro p hp
  obtain ⟨hbox, hne, hsep, hi⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hE (mem_product.mp hbox).1, hF (mem_product.mp hbox).2⟩, hne, hsep, hi⟩

theorem union_left (L : ℕ) (E F G : Finset (Finset ℕ)) : mass L (E ∪ F) G ≤ mass L E G + mass L F G := by
  have heq : pairs L (E ∪ F) G = pairs L E G ∪ pairs L F G := by
    ext p
    simp only [pairs, mem_filter, mem_product, mem_union]
    tauto
  unfold mass
  rw [heq]
  exact GraphStarWeights.sum_union_le_nonneg _ _ _ (fun p ↦ (probability_pos L (p.1 ∪ p.2)).le)

theorem symmetric (L : ℕ) (E F : Finset (Finset ℕ)) : mass L E F = mass L F E := by
  have heq : (pairs L E F).image Prod.swap = pairs L F E := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨hbox, hne, hsep, hi⟩ := mem_filter.mp hq
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_product.mp hbox).2, (mem_product.mp hbox).1⟩,
        Ne.symm hne, by simpa only [Prod.fst_swap, Prod.snd_swap, union_comm] using hsep,
        by simpa only [Prod.fst_swap, Prod.snd_swap, inf_comm] using hi⟩
    · intro hp
      obtain ⟨hbox, hne, hsep, hi⟩ := mem_filter.mp hp
      refine mem_image.mpr ⟨p.swap, ?_, Prod.swap_swap p⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_product.mp hbox).2, (mem_product.mp hbox).1⟩,
        Ne.symm hne, by simpa only [Prod.fst_swap, Prod.snd_swap, union_comm] using hsep,
        by simpa only [Prod.fst_swap, Prod.snd_swap, inf_comm] using hi⟩
  unfold mass
  rw [← heq, sum_image (Function.Involutive.injective Prod.swap_swap).injOn]
  exact sum_congr rfl (fun p _ ↦ by rw [Prod.fst_swap, Prod.snd_swap, union_comm])

theorem union_right (L : ℕ) (E F G : Finset (Finset ℕ)) : mass L E (F ∪ G) ≤ mass L E F + mass L E G := by
  rw [symmetric L E (F ∪ G), symmetric L E F, symmetric L E G]
  exact union_left L F G E

theorem finite_upper (L : ℕ) (E : Finset (Finset ℕ)) :
    second L E ≤ (∑ e ∈ E, probability L e) ^ 2 + mass L E E := by
  let b := fun p : Finset ℕ × Finset ℕ ↦ probability L p.1 * probability L p.2
  have hpoint (p : Finset ℕ × Finset ℕ) (_hp : p ∈ E ×ˢ E) :
      (if p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) then probability L (p.1 ∪ p.2) else 0) ≤
      b p + (if p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) ∧ space L p.1 ⊓ space L p.2 ≠ ⊥ then
        probability L (p.1 ∪ p.2) else 0) := by
    have hb : 0 ≤ b p := mul_nonneg (probability_pos L _).le (probability_pos L _).le
    by_cases hg : p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)
    · rw [ite_eq_left hg]
      by_cases hi : space L p.1 ⊓ space L p.2 = ⊥
      · rw [ite_eq_right (by tauto), independent L p.1 p.2 hi, add_zero]
      · rw [ite_eq_left ⟨hg.1, hg.2, hi⟩]
        linarith only [hb]
    · rw [ite_eq_right hg, ite_eq_right (by tauto), add_zero]
      exact hb
  calc
    _ ≤ ∑ p ∈ E ×ˢ E, (b p +
        if p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) ∧ space L p.1 ⊓ space L p.2 ≠ ⊥ then
          probability L (p.1 ∪ p.2) else 0) := by rw [second, sum_filter]; exact sum_le_sum hpoint
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter, sum_product, ← sum_mul_sum, pow_two]
      rfl

theorem source_pairs_eq (N H₁ H₂ a b c d L : ℕ) :
    (PrivatePairInteractions.points N H₁ H₂ a b c d L).image PrivatePairInteractions.pairKey =
      pairs L (PrivateChannelActivity.pairs N H₁ a b L) (PrivateChannelActivity.pairs N H₂ c d L) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hp₁, hp₂, hne, hsep, hi⟩ := PrivatePairInteractions.source_data hp
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_image.mpr ⟨p.1, hp₁, rfl⟩, mem_image.mpr ⟨p.2, hp₂, rfl⟩⟩, hne, hsep, ?_⟩
    simpa only [PrivatePairInteractions.pairKey, PrivatePairInteractions.edge, space, PaperP1.RetainedNullity.span_pair] using hi
  · intro hq
    obtain ⟨hbox, hne, hsep, hi⟩ := mem_filter.mp hq
    obtain ⟨p, hp, heq⟩ := mem_image.mp (mem_product.mp hbox).1
    obtain ⟨r, hr, hreq⟩ := mem_image.mp (mem_product.mp hbox).2
    have hkey : PrivatePairInteractions.pairKey (p, r) = q := Prod.ext heq hreq
    apply mem_image.mpr
    refine ⟨(p, r), mem_filter.mpr ⟨mem_product.mpr ⟨hp, hr⟩, ?_, ?_, ?_⟩, hkey⟩
    · simpa only [← heq, ← hreq, PrivatePairInteractions.edge] using hne
    · simpa only [← heq, ← hreq, WindowPairInteractionHosts.family] using hsep
    · simpa only [← heq, ← hreq, space, PaperP1.RetainedNullity.span_pair] using hi

theorem source_mass_eq {N H₁ H₂ a b c d L : ℕ} (hN : 2 ≤ N) (hab : a < b) (hcd : c < d)
    (hlarge₁ : (a + b) * (L + 1) < N) (hlarge₂ : (c + d) * (L + 1) < N) :
    mass L (PrivateChannelActivity.pairs N H₁ a b L) (PrivateChannelActivity.pairs N H₂ c d L) =
      PrivatePairInteractions.mass N H₁ H₂ a b c d L := by
  unfold mass
  rw [← source_pairs_eq N H₁ H₂ a b c d L, sum_image]
  · rfl
  · exact PrivatePairInteractions.pair_key_injective hN hab hcd hlarge₁ hlarge₂ _
      (fun p hp ↦ ⟨(PrivatePairInteractions.source_data hp).1, (PrivatePairInteractions.source_data hp).2.1⟩)

end PaperP1.HomogeneousEdgeInteractions
