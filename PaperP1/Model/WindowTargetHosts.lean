module

public import PaperP1.Model.IndependentTargetDeficit
public import PaperP1.Arithmetic.RelativeBlockRelations
public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Combinatorics.FiniteFamilyEnumeration

/-! # Actual dependent targets inject into one-block effective relation lists -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowTargetHosts

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.IndependentTargetDeficit

local instance windowTargetHostsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def targets (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) : Finset ℕ :=
  (G \ e).filter (targetDependent L e)

def sourceValues (L : ℕ) (e : Finset ℕ) : Finset ℕ :=
  e.biUnion (fun x ↦ NormalizedWindowSets.values x L)

def blocks (L : ℕ) : Fin 1 → ℕ → Finset ℕ := fun _ x ↦ NormalizedWindowSets.values x L

theorem source_span_le_full (L : ℕ) (e : Finset ℕ) :
    SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e ≤
      OldSpaceProjection.oldSpace (sourceValues L e) := by
  refine iSup_le fun x ↦ ?_
  change squareClassSpace x.val L ≤ OldSpaceProjection.oldSpace (sourceValues L e)
  rw [← NormalizedWindowSets.space_values x.val L]
  refine (RelativeBlockRelations.effective_le_full _).trans (ProjectedWindowLists.oldSpace_mono ?_)
  intro v hv
  exact mem_biUnion.mpr ⟨x.val, x.property, hv⟩

theorem sourceValues_enumeration {s : ℕ} (L : ℕ) (e : Finset ℕ) (he : e.card = s) :
    sourceValues L e = univ.biUnion (fun i : Fin s ↦
      NormalizedWindowSets.values (FiniteFamilyEnumeration.centres e he i) L) := by
  ext v
  simp only [sourceValues, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, hv⟩
    obtain ⟨i, hi⟩ := (FiniteFamilyEnumeration.enumeration e he).surjective ⟨x, hx⟩
    refine ⟨i, ?_⟩
    simpa only [FiniteFamilyEnumeration.centres, hi] using hv
  · rintro ⟨i, hv⟩
    exact ⟨_, (FiniteFamilyEnumeration.enumeration e he i).property, hv⟩

theorem lift_target (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (z : ℕ) (hz : z ∈ targets G L e) :
    (fun _ : Fin 1 ↦ z) ∈ EffectiveWindowLists.lists G (blocks L) (sourceValues L e) := by
  obtain ⟨hz, hdep⟩ := mem_filter.mp hz
  obtain ⟨u, hu, hne⟩ := (squareClassSpace z L ⊓
    SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e).ne_bot_iff.mp hdep
  apply (EffectiveWindowLists.mem_lists _ _ _ _).mpr
  refine ⟨fun _ ↦ (mem_sdiff.mp hz).1, fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ u, ?_, ?_⟩
  · intro i
    refine ⟨?_, hne⟩
    change u ∈ FiniteEvenSquareClasses.space (NormalizedWindowSets.values z L)
    rw [NormalizedWindowSets.space_values]
    exact hu.1
  · simpa only [Fin.sum_univ_one] using source_span_le_full L e hu.2

theorem card_le_lists (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) :
    (targets G L e).card ≤ (EffectiveWindowLists.lists G (blocks L) (sourceValues L e)).card := by
  apply card_le_card_of_injOn (fun z ↦ fun _ : Fin 1 ↦ z)
  · exact lift_target G L e
  · intro z _ w _ hzw
    exact congrFun hzw 0

end PaperP1.WindowTargetHosts
