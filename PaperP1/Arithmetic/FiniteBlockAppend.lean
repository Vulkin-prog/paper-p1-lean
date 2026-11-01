module

public import PaperP1.Arithmetic.EffectiveExposure

/-! # Adjoining fixed finite block families and their actual full value unions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteBlockAppend

open Finset

theorem biUnion_append {s d : ℕ} (O : Fin s → Finset ℕ) (P : Fin d → Finset ℕ) :
    univ.biUnion (Fin.append O P) = univ.biUnion O ∪ univ.biUnion P := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
    have hall : ∀ j : Fin (s + d), v ∈ Fin.append O P j → v ∈ univ.biUnion O ∪ univ.biUnion P := by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro k hk
        exact mem_union_left _ (mem_biUnion.mpr ⟨k, mem_univ _, by simpa only [Fin.append_left] using hk⟩)
      · intro k hk
        exact mem_union_right _ (mem_biUnion.mpr ⟨k, mem_univ _, by simpa only [Fin.append_right] using hk⟩)
    exact hall i hi
  · intro hv
    rcases mem_union.mp hv with hO | hP
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hO
      exact mem_biUnion.mpr ⟨Fin.castAdd d i, mem_univ _, by simpa only [Fin.append_left] using hi⟩
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hP
      exact mem_biUnion.mpr ⟨Fin.natAdd s i, mem_univ _, by simpa only [Fin.append_right] using hi⟩

theorem append_all {s d : ℕ} (old : Fin s → ℕ) (q : Fin d → ℕ)
    (O : Fin s → Finset ℕ) (P : Fin d → Finset ℕ) (F : ℕ → ℕ → Prop)
    (hO : ∀ i, ∀ v ∈ O i, F (old i) v) (hP : ∀ i, ∀ v ∈ P i, F (q i) v) :
    ∀ j, ∀ v ∈ Fin.append O P j, F (Fin.append old q j) v := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [Fin.append_left] using hO i
  · intro i
    simpa only [Fin.append_right] using hP i

end PaperP1.FiniteBlockAppend
