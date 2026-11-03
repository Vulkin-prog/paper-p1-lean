module

public import PaperP1.Algebra.LocalizedFractionEquiv
public import Mathlib.RingTheory.Localization.Ideal

/-! # Fraction fields of the actual prime quotient and its actual localized quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalizedQuotientFractionEquiv

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S] (P : Ideal R) [P.IsPrime]
  (hM : Disjoint (M : Set R) (P : Set R))

include M hM in
theorem map_isPrime : (P.map (algebraMap R S)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint M S P inferInstance hM

abbrev BaseRing := R ⧸ P
abbrev LocalizedRing := S ⧸ P.map (algebraMap R S)

local instance baseRing : CommRing (BaseRing P) := inferInstance
local instance targetRing : CommRing (LocalizedRing (S := S) P) := inferInstance

include M hM in
theorem quotient_injective : Function.Injective (algebraMap (BaseRing P) (LocalizedRing (S := S) P)) := by
  apply Ideal.quotientMap_injective'
  exact (IsLocalization.under_map_of_isPrime_disjoint M S (inferInstance : P.IsPrime) hM).le

def equiv : FractionRing (BaseRing P) ≃+* FractionRing (LocalizedRing (S := S) P) := by
  letI := map_isPrime (S := S) M P hM
  exact (LocalizedFractionEquiv.equiv (R := BaseRing P) (S := LocalizedRing (S := S) P)
    (Algebra.algebraMapSubmonoid (BaseRing P) M) (quotient_injective M P hM)).toRingEquiv

theorem equiv_mk (r : R) :
    equiv M P hM (algebraMap (BaseRing P) (FractionRing (BaseRing P)) (Ideal.Quotient.mk P r)) =
      algebraMap (LocalizedRing (S := S) P) (FractionRing (LocalizedRing (S := S) P))
        (Ideal.Quotient.mk _ (algebraMap R S r)) := by
  let := map_isPrime (S := S) M P hM
  change LocalizedFractionEquiv.equiv (R := BaseRing P) (S := LocalizedRing (S := S) P)
    (Algebra.algebraMapSubmonoid (BaseRing P) M) (quotient_injective M P hM) _ = _
  rw [LocalizedFractionEquiv.equiv_algebraMap]
  rfl

end PaperP1.LocalizedQuotientFractionEquiv
