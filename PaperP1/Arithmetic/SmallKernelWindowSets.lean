module

public import PaperP1.Arithmetic.CutoffSquareParts
public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Model.FiniteRademacher
public import PaperP1.Diophantine.LinearKernelFibres

/-! # Literal window populations in the several-small-kernels lemma -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelWindowSets

open Finset PaperP1.NormalizedWindowSets PaperP1.LargeOddKernel PaperP1.CutoffSquareParts
  PaperP1.Model

def smallValues (N L Y x : ℕ) (β u : ℝ) : Finset ℕ :=
  (values x L).filter fun v ↦ (largeOddKernel Y v : ℝ) ≤ (N : ℝ) ^ β ∧
    ((largeSquarePart Y v ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ u

def severalWindows (N L Y m : ℕ) (β u : ℝ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ m ≤ (smallValues N L Y x β u).card

def twoWindows (N L H : ℕ) (q : ℝ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ ∃ v ∈ values x L, ∃ w ∈ values x L, v ≠ w ∧
    ((largeOddKernel H v * largeOddKernel H w : ℕ) : ℝ) ≤ (N : ℝ) ^ q

theorem value_offset {x L v : ℕ} (hx : 0 < x) (hv : v ∈ values x L) :
    ((v : ℤ) - x).natAbs ≤ L + 1 ∧ PaperP1.LinearKernelFibres.value x ((v : ℤ) - x) = v := by
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp ((values_eq_interval hx) ▸ hv)
  have habs : |(v : ℤ) - x| ≤ (L + 1 : ℕ) := abs_le.mpr ⟨by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  · simp only [PaperP1.LinearKernelFibres.value, add_sub_cancel, Int.natAbs_natCast]

theorem select_values {S : Finset ℕ} {m : ℕ} (hcard : m ≤ S.card) :
    ∃ v : Fin m → ℕ, Function.Injective v ∧ ∀ i, v i ∈ S := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := exists_subset_card_eq hcard
  let e : Fin m ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  exact ⟨fun i ↦ (e i).val, Subtype.val_injective.comp e.injective, fun i ↦ hTS (e i).property⟩

end PaperP1.SmallKernelWindowSets
