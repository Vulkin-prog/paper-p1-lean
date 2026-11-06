module

public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Actual nonzero homogeneous divisors have finitely many homogeneous height-one components covering all their points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPrincipalComponents

def components {A : Type*} [CommRing A] [IsNoetherianRing A] (f : A) : Finset (Ideal A) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {f})).toFinset

theorem mem_components {A : Type*} [CommRing A] [IsNoetherianRing A] (f : A) (P : Ideal A) :
    P ∈ components f ↔ P ∈ (Ideal.span {f}).minimalPrimes := by
  exact Set.Finite.mem_toFinset _

theorem principal_homogeneous {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] {e : ℕ} {f : A} (hf : f ∈ H e) :
    (Ideal.span {f}).IsHomogeneous H := by
  apply Ideal.homogeneous_span H
  intro a ha
  rw [Set.mem_singleton_iff.mp ha]
  exact ⟨e, hf⟩

theorem minimal_prime_homogeneous {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (I : Ideal A) (hI : I.IsHomogeneous H)
    (P : Ideal A) (hP : P ∈ I.minimalPrimes) : P.IsHomogeneous H := by
  have hcore : (P.homogeneousCore H).toIdeal.IsPrime := hP.isPrime.homogeneousCore
  have hIcore : I ≤ (P.homogeneousCore H).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono H hP.le)
  have hle : (P.homogeneousCore H).toIdeal ≤ P := Ideal.toIdeal_homogeneousCore_le H P
  have heq : P = (P.homogeneousCore H).toIdeal :=
    le_antisymm (hP.2 ⟨hcore, hIcore⟩ hle) hle
  rw [heq]
  exact HomogeneousIdeal.isHomogeneous _

theorem height_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (f : A) (hf0 : f ≠ 0) (P : Ideal A) (hP : P ∈ (Ideal.span {f}).minimalPrimes) : P.height = 1 := by
  have hupper := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) P hP
  have hnotbot : P ≠ ⊥ := by
    intro he
    have hf : f ∈ P := hP.le (Ideal.mem_span_singleton_self f)
    rw [he, Ideal.mem_bot] at hf
    exact hf0 hf
  have hpositive : P.height ≠ 0 := fun h ↦ hnotbot (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact le_antisymm hupper (Order.one_le_iff_ne_zero.mpr hpositive)

theorem finite_cover {F A : Type*} [Field F] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra F A] (H : ℕ → Submodule F A) [GradedAlgebra H]
    {e : ℕ} {f : A} (hf : f ∈ H e) (hf0 : f ≠ 0) :
    (∀ P ∈ components f, P.IsPrime ∧ P.IsHomogeneous H ∧ P.height = 1 ∧ f ∈ P) ∧
      ∀ (φ : A →ₐ[F] F) (b : A), φ f = 0 → φ b ≠ 0 →
        ∃ P ∈ components f, P ≤ RingHom.ker φ.toRingHom ∧ b ∉ P := by
  constructor
  · intro P hP
    have hp := (mem_components f P).mp hP
    exact ⟨hp.isPrime, minimal_prime_homogeneous H _ (principal_homogeneous H hf) P hp,
      height_one f hf0 P hp, hp.le (Ideal.mem_span_singleton_self f)⟩
  · intro φ b hφf hφb
    let Q := RingHom.ker φ.toRingHom
    let : Q.IsPrime := RingHom.ker_isPrime _
    have hle : Ideal.span {f} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hφf
    obtain ⟨P, hp, hPQ⟩ := Ideal.exists_minimalPrimes_le hle
    refine ⟨P, (mem_components f P).mpr hp, hPQ, ?_⟩
    intro hb
    exact hφb (hPQ hb)

end PaperP1.HomogeneousPrincipalComponents
