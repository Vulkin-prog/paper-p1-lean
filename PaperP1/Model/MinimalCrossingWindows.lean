module

public import PaperP1.Affine.MinimalSpanCrossing
public import PaperP1.Model.RelativeWindowFamilies

/-! # A true minimal span crossing supplies the actual relative-window witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MinimalCrossingWindows

open Finset PaperP1.Arithmetic PaperP1.SubspaceFamilyRank

theorem witnesses (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (A : Finset ℕ)
    (hcross : W ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥)
    (hproper : ∀ B : Finset ℕ, B ⊂ A → Disjoint W (span (fun x ↦ squareClassSpace x L) B)) :
    RelativeWindowFamilies.Witnesses L W A := by
  obtain ⟨u, hnonzero, hsum, _hne⟩ := MinimalSpanCrossing.exists_relation _ W A hcross hproper
  exact fun i ↦ ⟨u, hnonzero i, hsum⟩

theorem mem_families (G : Finset ℕ) (L r : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (A : Finset ℕ)
    (hAG : A ⊆ G) (hcard : A.card = r)
    (hcross : W ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥)
    (hproper : ∀ B : Finset ℕ, B ⊂ A → Disjoint W (span (fun x ↦ squareClassSpace x L) B)) :
    A ∈ RelativeWindowFamilies.families G L r W := by
  classical
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hAG, hcard⟩, witnesses L W A hcross hproper⟩

end PaperP1.MinimalCrossingWindows
