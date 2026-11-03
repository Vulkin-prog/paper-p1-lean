module

public import PaperP1.Algebra.RadicalProjectionPolynomial

/-! # The actual monic projection equation commutes with base change whenever generic independence persists -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RadicalProjectionPolynomialBaseChange

open Polynomial PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.RadicalProjectionPolynomial

theorem map_equation (R S K : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [CharZero K] [Algebra S K] [IsFractionRing S K] (φ : R →+* S) (s : List R)
    (hs : IndependentQuadraticTower.Independent ((s.map φ).map (algebraMap S K))) :
    (equation R s).map φ = equation S (s.map φ) := by
  have hroot : aeval (radicalSum S (s.map φ)) ((equation R s).map φ) = 0 := by
    rw [← map_aeval, equation_root, map_zero]
  have hdvd := (root_iff_dvd S K (s.map φ) hs _).mp hroot
  apply eq_of_monic_of_dvd_of_natDegree_le (equation_monic S _) ((equation_monic R s).map φ) hdvd
  calc
    ((equation R s).map φ).natDegree = (equation R s).natDegree := (equation_monic R s).natDegree_map φ
    _ ≤ 2 ^ s.length := by
      have hh := minpoly.natDegree_le (A := R) (radicalSum R s)
      rwa [FiniteQuadraticTower.finrank] at hh
    _ = (equation S (s.map φ)).natDegree := by rw [equation_degree S K _ hs, List.length_map]

theorem mapped_equation_irreducible (R S K : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [CharZero K] [Algebra S K] [IsFractionRing S K] (φ : R →+* S) (s : List R)
    (hs : IndependentQuadraticTower.Independent ((s.map φ).map (algebraMap S K))) :
    Irreducible ((equation R s).map φ) := by
  rw [map_equation R S K φ s hs]
  exact equation_irreducible S K _ hs

end PaperP1.RadicalProjectionPolynomialBaseChange
