module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.FractionRing

/-! # The actual fraction field is unchanged by an injective localization of a domain -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalizedFractionEquiv

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  (hinj : Function.Injective (algebraMap R S))

include M hinj in
theorem fraction_isFractionRing : IsFractionRing R (FractionRing S) := by
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M
    (nonZeroDivisors S) (FractionRing S) (fun _ hu ↦ hu.mem_nonZeroDivisors)
  have heq : (nonZeroDivisors S).comap (algebraMap R S) = nonZeroDivisors R := by
    ext x
    change algebraMap R S x ∈ nonZeroDivisors S ↔ x ∈ nonZeroDivisors R
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · intro hx hz
      exact hx (hz ▸ map_zero (algebraMap R S))
    · intro hx hz
      exact hx (hinj (hz.trans (map_zero _).symm))
  simpa only [heq] using h

def equiv : FractionRing R ≃ₐ[R] FractionRing S := by
  letI := fraction_isFractionRing M hinj
  exact IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) (FractionRing S)

theorem equiv_algebraMap (r : R) : equiv M hinj (algebraMap R (FractionRing R) r) =
    algebraMap R (FractionRing S) r := (equiv M hinj).commutes r

end PaperP1.LocalizedFractionEquiv
