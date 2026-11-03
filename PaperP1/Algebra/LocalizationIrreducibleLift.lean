module

public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-! # Every irreducible element of an actual localization lifts up to association -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalizationIrreducibleLift

theorem exists_associated {R S : Type*} [CommRing R] [CommRing S] [UniqueFactorizationMonoid R]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] (s : S) (hs : Irreducible s) :
    ∃ r : R, Irreducible r ∧ Associated (algebraMap R S r) s := by
  let f := IsLocalization.toLocalizationMap M S
  obtain ⟨⟨r, m⟩, heq⟩ := f.surj s
  have hm : IsUnit (f m) := f.map_units m
  have hass : Associated (f r) s := (Associated.of_eq heq.symm).trans (associated_mul_unit_left s (f m) hm)
  have hirr : Irreducible (f r) := hass.symm.irreducible hs
  obtain ⟨u, r', hu, hr', hrr'⟩ := f.eq_isUnit_map_mul_irreducible_of_irreducible_map hirr
  refine ⟨r', hr', ?_⟩
  have hfirst : Associated (f r) (f r') := by
    rw [hrr', map_mul]
    exact associated_unit_mul_left (f r') (f u) hu
  exact hfirst.symm.trans hass

end PaperP1.LocalizationIrreducibleLift
