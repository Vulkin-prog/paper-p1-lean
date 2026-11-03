module

public import PaperP1.Model.RelativeParticipatingUnion
public import PaperP1.Model.FixedPairExtensions
public import PaperP1.Combinatorics.DistinguishedSeedWeights

/-! # Large relative target seeds of a dependent pair reduce to original coordinatewise participating families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairExtensionSeedTail

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedPairExtensions

def largeSeeds (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (s : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G \ e).powerset.filter fun A ↦ s ≤ A.card ∧ RelativeWindowFamilies.Witnesses L (sourceSpace e L) A

def participating (G : Finset ℕ) (L s : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun I ↦ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I

theorem mem_largeSeeds (G : Finset ℕ) (L : ℕ) (e A : Finset ℕ) (s : ℕ) :
    A ∈ largeSeeds G L e s ↔ A ⊆ G \ e ∧ s ≤ A.card ∧ RelativeWindowFamilies.Witnesses L (sourceSpace e L) A := by
  classical
  simp only [largeSeeds, mem_filter, mem_powerset]

theorem mem_participating (G I : Finset ℕ) (L s : ℕ) :
    I ∈ participating G L s ↔ I ⊆ G ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I := by
  classical
  simp only [participating, mem_filter, mem_powerset]

theorem union_mem (G : Finset ℕ) (L : ℕ) (e A : Finset ℕ) (s : ℕ)
    (heG : e ⊆ G) (hecard : e.card = 2) (hepos : 0 < runRelativeNullity L e)
    (hA : A ∈ largeSeeds G L e s) : Disjoint e A ∧ e ∪ A ∈ participating G L s := by
  obtain ⟨hAG, hsize, hw⟩ := (mem_largeSeeds G L e A s).mp hA
  have hdis : Disjoint e A := disjoint_left.mpr (fun x he hx ↦ (mem_sdiff.mp (hAG hx)).2 he)
  refine ⟨hdis, (mem_participating G (e ∪ A) L s).mpr ⟨union_subset heG (hAG.trans sdiff_subset),
    hsize.trans (card_le_card subset_union_right), ?_⟩⟩
  exact RelativeParticipatingUnion.union_witnesses L e A
    (RelativeParticipatingUnion.pair_witnesses L e hecard hepos) hw

theorem weighted_bound (G : Finset ℕ) (L s : ℕ) (P : Finset (Finset ℕ))
    (hP : ∀ e ∈ P, e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e)
    (w : ℕ → ℝ) (c : Finset ℕ → ℝ) (R : ℝ) (hw : ∀ x, 0 ≤ w x) (hR : 0 ≤ R)
    (hc : ∀ e ∈ P, 0 ≤ c e ∧ c e ≤ R * ∏ x ∈ e, w x) :
    (∑ e ∈ P, c e * ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, w x) ≤
      R * ∑ I ∈ participating G L s, ∏ x ∈ I, 2 * w x := by
  apply DistinguishedSeedWeights.mass_bound P (participating G L s) (fun e ↦ largeSeeds G L e s) w c R hw hR hc
  intro e he A hA
  obtain ⟨heG, hecard, hepos⟩ := hP e he
  exact union_mem G L e A s heG hecard hepos hA

end PaperP1.PairExtensionSeedTail
