module

public import PaperP1.Model.IndependentFullSupportTail
public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Combinatorics.AllCardinalitySeedBound

/-! # Every non-direct original family contains an ordinary primitive independent seed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryIndependentDeficit

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

def families (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun I ↦ runRelativeNullity L I ≠ 0

def seeds (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter (ConnectedWindowFamilies.Primitive L)

def mass (G : Finset ℕ) (L : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ I ∈ families G L, ∏ x ∈ I, w x

theorem seed_data (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (hI : I ∈ seeds G L) :
    I ⊆ G ∧ 2 ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I := by
  classical
  obtain ⟨hIG, hprim⟩ := mem_filter.mp hI
  exact ⟨mem_powerset.mp hIG, PrimitiveActiveSeeds.primitive_card_ge_two L I hprim,
    IndependentFullSupportTail.witnesses L I (IndependentFullSupportTail.primitive_fullSupport L I hprim)⟩

theorem seed_cover (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (hI : I ∈ families G L) :
    I ⊆ G ∧ ∃ D ∈ seeds G L, D ⊆ I := by
  classical
  obtain ⟨hIG, hdep⟩ := mem_filter.mp hI
  obtain ⟨D, hDI, hprim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L I (Nat.pos_of_ne_zero hdep)
  have hsub := mem_powerset.mp hIG
  exact ⟨hsub, D, mem_filter.mpr ⟨mem_powerset.mpr (hDI.trans hsub), hprim⟩, hDI⟩

theorem finite_bound (G : Finset ℕ) (L : ℕ) (w : ℕ → ℝ) (hw : ∀ x, 0 ≤ w x) :
    mass G L w ≤ Real.exp (∑ x ∈ G, w x) * ∑ I ∈ seeds G L, ∏ x ∈ I, w x :=
  AllCardinalitySeedBound.cover_bound G (families G L) (seeds G L) w hw
    (fun I hI ↦ (seed_data G L I hI).1) (fun I hI ↦ seed_cover G L I hI)

end PaperP1.OrdinaryIndependentDeficit
