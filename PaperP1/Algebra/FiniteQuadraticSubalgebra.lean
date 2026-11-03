module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Adjoin.Basic

/-! # Finiteness of the literal inclusion after adjoining finitely many quadratic generators -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteQuadraticSubalgebra

theorem finite_inclusion {F A ι : Type*} [CommRing F] [CommRing A] [Algebra F A] [Finite ι]
    (B S : Subalgebra F A) (hBS : B ≤ S) (w : ι → S)
    (hgen : S = Algebra.adjoin F ((B : Set A) ∪ Set.range fun i ↦ (w i : A)))
    (hsquare : ∀ i, (w i : A) ^ 2 ∈ B) : (Subalgebra.inclusion hBS).toRingHom.Finite := by
  let f : B →+* S := (Subalgebra.inclusion hBS).toRingHom
  let : Algebra B S := f.toAlgebra
  have : IsScalarTower F B S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  change Module.Finite B S
  let T := Algebra.adjoin B (Set.range w)
  have hi : ∀ i, IsIntegral B (w i) := by
    intro i
    apply IsIntegral.of_pow (n := 2) (by decide)
    let b : B := ⟨(w i : A) ^ 2, hsquare i⟩
    have he : algebraMap B S b = w i ^ 2 := by apply Subtype.ext; rfl
    rw [← he]
    exact (algebraMap B S).isIntegralElem_map
  have ht : T = ⊤ := by
    let U : Subalgebra F A := (T.restrictScalars F).map S.val
    have hSU : S ≤ U := by
      rw [hgen]
      apply Algebra.adjoin_le
      rintro a (ha | ⟨i, rfl⟩)
      · let b : B := ⟨a, ha⟩
        exact ⟨algebraMap B S b, T.algebraMap_mem b, rfl⟩
      · exact ⟨w i, Algebra.subset_adjoin (Set.mem_range_self i), rfl⟩
    apply top_unique
    intro x _hx
    obtain ⟨y, hy, hxy⟩ := hSU x.property
    have hxy' : y = x := Subtype.ext hxy
    exact hxy' ▸ hy
  have : Module.Finite B T := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range w)
    (by rintro _ ⟨i, rfl⟩; exact hi i)
  apply Module.Finite.of_surjective T.val.toLinearMap
  intro x
  exact ⟨⟨x, by rw [ht]; trivial⟩, rfl⟩

end PaperP1.FiniteQuadraticSubalgebra
