module

public import Mathlib.Algebra.GCDMonoid.Finset

/-! # A nonzero finite coefficient family admits a common factor with primitive quotients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveCoefficientFamily

open Finset

theorem extract {R ι : Type*} [CommMonoidWithZero R] [NormalizedGCDMonoid R] [Fintype ι]
    (A : ι → R) (hA : ∃ i, A i ≠ 0) :
    ∃ D : R, ∃ Q : ι → R, D ≠ 0 ∧ (∀ i, A i = D * Q i) ∧
      ∀ E : R, (∀ i, E ∣ Q i) → IsUnit E := by
  classical
  obtain ⟨i, hi⟩ := hA
  obtain ⟨Q, hfactor, hgcd⟩ := (univ : Finset ι).extract_gcd A ⟨i, mem_univ i⟩
  have hD : (univ : Finset ι).gcd A ≠ 0 := by
    intro hz
    exact hi (gcd_eq_zero_iff.mp hz i (mem_univ i))
  refine ⟨univ.gcd A, Q, hD, fun j ↦ hfactor j (mem_univ j), ?_⟩
  intro E hE
  apply isUnit_of_dvd_one
  rw [← hgcd]
  exact dvd_gcd_iff.mpr fun j _ ↦ hE j

end PaperP1.PrimitiveCoefficientFamily
