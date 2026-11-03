module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # An actual isomorphism after inverting a coordinate preserves every prime height on that chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalizationPrimeHeightEquiv

variable {A B : Type*} [CommRing A] [CommRing B]

theorem height_comap (f : A →+* B) (b : A) (hf : Function.Bijective (Localization.awayMap f b))
    (Q : Ideal B) [Q.IsPrime] (hb : f b ∉ Q) : (Q.comap f).height = Q.height := by
  let e : Localization.Away b ≃+* Localization.Away (f b) := RingEquiv.ofBijective _ hf
  let J := Q.map (algebraMap B (Localization.Away (f b)))
  have hdis : Disjoint (Submonoid.powers (f b) : Set B) (Q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (f b)).mpr hb
  have hJ : J.comap (algebraMap B (Localization.Away (f b))) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (f b)) (Localization.Away (f b))
      inferInstance hdis
  have hnat : e.toRingHom.comp (algebraMap A (Localization.Away b)) =
      (algebraMap B (Localization.Away (f b))).comp f := by
    ext x
    change Localization.awayMap f b (algebraMap A (Localization.Away b) x) = _
    exact IsLocalization.map_eq _ x
  have hcomap : (J.comap e.toRingHom).comap (algebraMap A (Localization.Away b)) = Q.comap f := by
    rw [Ideal.comap_comap, hnat, ← Ideal.comap_comap, hJ]
  calc
    (Q.comap f).height = ((J.comap e.toRingHom).comap (algebraMap A (Localization.Away b))).height :=
      congrArg Ideal.height hcomap.symm
    _ = (J.comap e.toRingHom).height := IsLocalization.height_under (Submonoid.powers b) _
    _ = J.height := e.height_comap J
    _ = Q.height := IsLocalization.height_map_of_disjoint (Submonoid.powers (f b)) Q hdis

end PaperP1.LocalizationPrimeHeightEquiv
