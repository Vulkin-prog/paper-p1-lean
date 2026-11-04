module

public import PaperP1.Model.RelativeWindowFamilies

/-! # Literal full-support relations with one additional effective block -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneBlockFullSupport

open Finset PaperP1.Arithmetic PaperP1.Model

def FullSupport (L : ℕ) (U I : Finset ℕ) : Prop :=
  ∃ t : FiniteEvenSquareClasses.space U, t ≠ 0 ∧
    ∃ u : (i : I) → squareClassSpace i.val L,
      (∀ i, u i ≠ 0) ∧ t.val + (∑ i : I, (u i).val) = 0

def families (G : Finset ℕ) (L : ℕ) (U : Finset ℕ) (s : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun I ↦ s ≤ I.card ∧ FullSupport L U I

theorem mem_families (G I U : Finset ℕ) (L s : ℕ) :
    I ∈ families G L U s ↔ I ⊆ G ∧ s ≤ I.card ∧ FullSupport L U I := by
  classical
  simp only [families, mem_filter, mem_powerset]

theorem witnesses {L : ℕ} {U I : Finset ℕ} (h : FullSupport L U I) :
    RelativeWindowFamilies.Witnesses L (FiniteEvenSquareClasses.space U) I := by
  obtain ⟨t, _ht, u, hu, hsum⟩ := h
  have hmem : (∑ i : I, (u i).val) ∈ FiniteEvenSquareClasses.space U := by
    rw [eq_neg_of_add_eq_zero_right hsum]
    exact (FiniteEvenSquareClasses.space U).neg_mem t.property
  exact fun i ↦ ⟨u, hu i, hmem⟩

theorem families_antitone (G U : Finset ℕ) (L : ℕ) {s t : ℕ} (hst : s ≤ t) :
    families G L U t ⊆ families G L U s := by
  intro I hI
  obtain ⟨hIG, hsize, hfull⟩ := (mem_families G I U L t).mp hI
  exact (mem_families G I U L s).mpr ⟨hIG, hst.trans hsize, hfull⟩

end PaperP1.OneBlockFullSupport
