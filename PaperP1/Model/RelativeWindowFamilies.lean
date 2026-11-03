module

public import PaperP1.Affine.MinimalRelativeRelations
public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Arithmetic.RelativeBlockRelations
public import PaperP1.Model.FamilyIndependentMass

/-! # Actual unordered target families in which every window participates relative to a prescribed effective space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeWindowFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.FiniteFamilyEnumeration
  PaperP1.ConnectedWindowFamilies

local instance relativeWindowFamiliesPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def Witnesses (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (A : Finset ℕ) : Prop :=
  ∀ i : A, ∃ u : (j : A) → squareClassSpace j.val L, u i ≠ 0 ∧ (∑ j : A, (u j).val) ∈ W

def families (G : Finset ℕ) (L r : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard r).filter (Witnesses L W)

theorem minimal_witnesses (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) [Fintype W] (A : Finset ℕ)
    (hpositive : 0 < MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) A)
    (hproper : ∀ B : Finset ℕ, B ⊂ A → MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) B = 0) :
    Witnesses L W A := by
  obtain ⟨u, hnonzero, hsum⟩ := MinimalRelativeRelations.exists_relation W (fun x ↦ squareClassSpace x L) A
    hpositive hproper
  exact fun i ↦ ⟨u, hnonzero i, hsum⟩

theorem covered_enumeration {r : ℕ} (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (O A : Finset ℕ) (hcard : A.card = r) (hW : W ≤ OldSpaceProjection.oldSpace O)
    (hA : Witnesses L W A) : RelativeBlockRelations.Covered (blocks L r) O (centres A hcard) := by
  let e := enumeration A hcard
  intro i
  obtain ⟨u, hi, hsum⟩ := hA (e i)
  refine ⟨fun j ↦ (u (e j)).val, ?_, fun hz ↦ hi (Subtype.ext hz), ?_⟩
  · intro j
    change (u (e j)).val ∈ FiniteEvenSquareClasses.space (NormalizedWindowSets.values (e j).val L)
    rw [NormalizedWindowSets.space_values]
    exact (u (e j)).property
  · have heq : (∑ j : Fin r, (u (e j)).val) = ∑ j : A, (u j).val :=
      Equiv.sum_comp e (fun j : A ↦ (u j).val)
    rw [heq]
    exact hW hsum

theorem family_count (G : Finset ℕ) (L r : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (O : Finset ℕ) (hW : W ≤ OldSpaceProjection.oldSpace O) :
    (families G L r W).card ≤ (RelativeBlockRelations.population G (blocks L r) O).card := by
  classical
  apply FiniteFamilyEnumeration.family_count
  intro A hA
  obtain ⟨hAG, hwitness⟩ := mem_filter.mp hA
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hAG
  refine ⟨centres A hcard, ?_, centres_tupleSet A hcard⟩
  exact (RelativeBlockRelations.mem_population G (blocks L r) O _).mpr
    ⟨centres_mem G A hcard hsub, centres_injective A hcard, covered_enumeration L W O A hcard hW hwitness⟩

theorem old_space_bound {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ⨆ i, squareClassSpace (x i) L) :
    W ≤ OldSpaceProjection.oldSpace (univ.biUnion fun i ↦ NormalizedWindowSets.values (x i) L) := by
  apply hW.trans
  apply iSup_le
  intro i
  calc
    _ = FiniteEvenSquareClasses.space (NormalizedWindowSets.values (x i) L) := (NormalizedWindowSets.space_values _ _).symm
    _ ≤ OldSpaceProjection.oldSpace (NormalizedWindowSets.values (x i) L) := RelativeBlockRelations.effective_le_full _
    _ ≤ _ := ProjectedWindowLists.oldSpace_mono
      (fun n hn ↦ mem_biUnion.mpr ⟨i, mem_univ _, hn⟩)

theorem singleton_iff (L z : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) :
    Witnesses L W {z} ↔ squareClassSpace z L ⊓ W ≠ ⊥ := by
  constructor
  · intro hw
    let i : ({z} : Finset ℕ) := ⟨z, mem_singleton_self _⟩
    obtain ⟨u, hu, hsum⟩ := hw i
    have heq (j : ({z} : Finset ℕ)) : j = i := Subtype.ext (mem_singleton.mp j.property)
    have hs : (∑ j : ({z} : Finset ℕ), (u j).val) = (u i).val := by
      calc
        _ = ∑ _j : ({z} : Finset ℕ), (u i).val := sum_congr rfl (fun j _ ↦ congrArg (fun j ↦ (u j).val) (heq j))
        _ = _ := by simp
    rw [hs] at hsum
    exact (Submodule.ne_bot_iff _).mpr ⟨(u i).val, ⟨(u i).property, hsum⟩,
      fun hz ↦ hu (Subtype.ext hz)⟩
  · intro hnot
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (squareClassSpace z L ⊓ W)).mp hnot
    have hmem : v ∈ squareClassSpace z L ∧ v ∈ W := by
      with_unfolding_all exact hv
    let u : (j : ({z} : Finset ℕ)) → squareClassSpace j.val L := fun j ↦
      ⟨v, by simpa only [mem_singleton.mp j.property] using hmem.1⟩
    intro i
    refine ⟨u, fun hz ↦ hv0 (congrArg Subtype.val hz), ?_⟩
    change (∑ _j : ({z} : Finset ℕ), v) ∈ W
    simpa only [sum_const, card_univ, Fintype.card_coe, card_singleton, one_nsmul] using hmem.2

theorem unary_families (G : Finset ℕ) (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) :
    families G L 1 W = (G.filter fun z ↦ squareClassSpace z L ⊓ W ≠ ⊥).image singleton := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨hAG, hw⟩ := mem_filter.mp hA
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hAG
    obtain ⟨z, rfl⟩ := card_eq_one.mp hcard
    exact mem_image.mpr ⟨z, mem_filter.mpr ⟨hsub (mem_singleton_self _), (singleton_iff L z W).mp hw⟩, rfl⟩
  · intro hA
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hA
    obtain ⟨hzG, hnot⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨singleton_subset_iff.mpr hzG, card_singleton _⟩,
      (singleton_iff L z W).mpr hnot⟩

theorem unary_mass (G : Finset ℕ) (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) :
    FamilyIndependentMass.independentMass (families G L 1 W) L =
      ∑ z ∈ G.filter (fun z ↦ squareClassSpace z L ⊓ W ≠ ⊥), PaperP1.Model.InfiniteStarts.infiniteMarginal z L := by
  classical
  rw [FamilyIndependentMass.independentMass, unary_families,
    sum_image (fun _ _ _ _ h ↦ singleton_injective h)]
  simp only [prod_singleton]

end PaperP1.RelativeWindowFamilies
