module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.GoingDown

/-! # Prime heights under integral maps and integral maps with going down -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralPrimeHeight

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

theorem comap_strictMono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  exact Ideal.IsIntegral.under_lt_under hPQ

theorem height_le (P : Ideal S) [P.IsPrime] : P.height ≤ (P.under R).height := by
  have h := Order.height_le_height_apply_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (comap_strictMono (R := R) (S := S)) (⟨P, inferInstance⟩ : PrimeSpectrum S)
  simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal, Ideal.under_def] using h

theorem height_eq [Algebra.HasGoingDown R S] (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  have hlift (Q : PrimeSpectrum S) (p : PrimeSpectrum R)
      (hp : p < PrimeSpectrum.comap (algebraMap R S) Q) :
      ∃ Q' : PrimeSpectrum S, Q' < Q ∧ PrimeSpectrum.comap (algebraMap R S) Q' = p := by
    have : Q.asIdeal.LiesOver (Q.asIdeal.under R) := ⟨rfl⟩
    obtain ⟨Q', hQ', hprime, hover⟩ := Ideal.exists_ideal_lt_liesOver_of_lt Q.asIdeal hp
    exact ⟨⟨Q', hprime⟩, hQ', PrimeSpectrum.ext hover.over.symm⟩
  have h := Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (comap_strictMono (R := R) (S := S)) hlift (⟨P, inferInstance⟩ : PrimeSpectrum S)
  simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal, Ideal.under_def] using h

end PaperP1.IntegralPrimeHeight
