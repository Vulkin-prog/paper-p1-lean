module

public import PaperP1.Affine.PrimitiveRelations
public import PaperP1.Arithmetic.ConnectedBlockLists
public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Combinatorics.FiniteFamilyEnumeration

/-! # Actual unordered connected and primitive original-window families

Both actual family populations are images of injective participating tuples.
Connectedness is the canonical direct decomposition; primitiveness is positive
relative nullity with every proper subfamily direct.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedWindowFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.FiniteFamilyEnumeration

def Connected (L : ℕ) (I : Finset ℕ) : Prop :=
  canonicalRelationPartition (fun x : I ↦ squareClassSpace x.val L) = ⊤

def Primitive (L : ℕ) (I : Finset ℕ) : Prop :=
  0 < relativeNullityOn (fun x ↦ squareClassSpace x L) I ∧
    ∀ J : Finset ℕ, J ⊂ I → relativeNullityOn (fun x ↦ squareClassSpace x L) J = 0

def connectedFamilies (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard r).filter (Connected L)

def primitiveFamilies (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard r).filter (Primitive L)

def blocks (L r : ℕ) : Fin r → ℕ → Finset ℕ := fun _ x ↦ PaperP1.NormalizedWindowSets.values x L

theorem connected_enumeration {r : ℕ} (L : ℕ) (I : Finset ℕ) (hI : I.card = r)
    (hr : 2 ≤ r) (hconnected : Connected L I) :
    PaperP1.RelativeBlockRelations.Covered (blocks L r) ∅ (centres I hI) := by
  let e := enumeration I hI
  intro i
  have hex : ∃ j : Fin r, i ≠ j := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro hij
      have hval := congrArg Fin.val hij
      change i.val = 1 at hval
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro hij
      have hval := congrArg Fin.val hij
      change i.val = 0 at hval
      omega
  obtain ⟨j, hij⟩ := hex
  let S := fun x : I ↦ squareClassSpace x.val L
  obtain ⟨s, hs, hne⟩ := PaperP1.ConnectedRelations.coordinate_relation S hconnected (e i) (e j)
    (fun h ↦ hij (e.injective h))
  refine ⟨fun k ↦ (s (e k)).val, ?_, hne, ?_⟩
  · intro k
    change (s (e k)).val ∈ PaperP1.FiniteEvenSquareClasses.space (PaperP1.NormalizedWindowSets.values (e k).val L)
    rw [PaperP1.NormalizedWindowSets.space_values]
    exact (s (e k)).property
  · have hsum : (∑ k : Fin r, (s (e k)).val) = 0 := (Equiv.sum_comp e _).trans hs
    rw [hsum]
    exact Submodule.zero_mem _

theorem primitive_enumeration {r : ℕ} (L : ℕ) (I : Finset ℕ) (hI : I.card = r)
    (hprimitive : Primitive L I) :
    PaperP1.RelativeBlockRelations.Covered (blocks L r) ∅ (centres I hI) := by
  let e := enumeration I hI
  obtain ⟨s, hfull, hsum⟩ := PaperP1.PrimitiveRelations.full_relation_of_minimal_nullity
    (fun x ↦ squareClassSpace x L) I hprimitive.1 hprimitive.2
  intro i
  refine ⟨fun k ↦ (s (e k)).val, ?_, ?_, ?_⟩
  · intro k
    change (s (e k)).val ∈ PaperP1.FiniteEvenSquareClasses.space (PaperP1.NormalizedWindowSets.values (e k).val L)
    rw [PaperP1.NormalizedWindowSets.space_values]
    exact (s (e k)).property
  · exact fun hz ↦ hfull (e i) (Subtype.ext hz)
  · have hzero : (∑ k : Fin r, (s (e k)).val) = 0 := (Equiv.sum_comp e _).trans hsum
    rw [hzero]
    exact Submodule.zero_mem _

theorem connected_family_count (G : Finset ℕ) (L r : ℕ) (hr : 2 ≤ r) :
    (connectedFamilies G L r).card ≤
      (PaperP1.RelativeBlockRelations.population G (blocks L r) ∅).card := by
  classical
  apply family_count
  intro I hI
  obtain ⟨hIG, hconnected⟩ := mem_filter.mp hI
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
  refine ⟨centres I hcard, ?_, centres_tupleSet I hcard⟩
  apply (PaperP1.RelativeBlockRelations.mem_population G (blocks L r) ∅ _).mpr
  exact ⟨centres_mem G I hcard hsub, centres_injective I hcard,
    connected_enumeration L I hcard hr hconnected⟩

theorem primitive_family_count (G : Finset ℕ) (L r : ℕ) :
    (primitiveFamilies G L r).card ≤
      (PaperP1.RelativeBlockRelations.population G (blocks L r) ∅).card := by
  classical
  apply family_count
  intro I hI
  obtain ⟨hIG, hprimitive⟩ := mem_filter.mp hI
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
  refine ⟨centres I hcard, ?_, centres_tupleSet I hcard⟩
  apply (PaperP1.RelativeBlockRelations.mem_population G (blocks L r) ∅ _).mpr
  exact ⟨centres_mem G I hcard hsub, centres_injective I hcard,
    primitive_enumeration L I hcard hprimitive⟩

end PaperP1.ConnectedWindowFamilies
