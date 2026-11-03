module

public import PaperP1.Asymptotics.CriticalNonalignedSourceExclusion
public import PaperP1.Geometry.OrdinaryCurveSourceHeight
public import PaperP1.Geometry.OrdinaryCurveMultiplicityComparison
public import PaperP1.Geometry.OrdinaryCurveHostImage

/-! # Nonalignment force every ordinary curve degree above a fixed cap

The actual ordinary Hilbert slope is arbitrary. Every actual ordinary surface
curve through an admissible host has slope strictly greater than the chosen cap.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalNonalignedDegreeGap

open Polynomial Finset PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.SelectedProportionalPairs PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance weightedRing (ι : Type*) : CommRing (WeightedPolynomial ℚ ι) := inferInstance

theorem eventually_degree_gt (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (s : List (PolynomialRing ℚ)) (d : Fin s.length → ℤ) (D : ℕ)
        (I : Fin s.length → Finset ℤ) (j : Fin s.length → ℤ),
      let c : Fin s.length → ℚ := fun i ↦ (d i : ℚ)
      let J₀ : Fin s.length → Finset ℤ := fun i ↦ {j i}
      ∀ (_hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J₀ i).card)) (I i) (J₀ i))
        (_hdeg : ∀ i, (I i).card + (J₀ i).card ≤ 2 * D) (_hD : 0 < D)
        (_hmin : ∀ i, 2 ≤ (I i).card + (J₀ i).card),
      ∀ (Q : Ideal (WeightedPolynomial ℚ (Fin s.length))) [Q.IsPrime],
      ∀ (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J₀ i) i ∈ Q)
        (_hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3 ⊕ Fin s.length) ℚ)),
      ∀ (e : ℕ) (β : ℚ), GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q)
        (Polynomial.C (e : ℚ) * X + Polynomial.C β) →
        (OrdinaryCurveSourceHeight.surfaceIdeal c D I J₀ Q hrel).height = 1 →
        4 * (E + 1) ^ 2 ≤ s.length →
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i k ↦ Disjoint (I i) (I k)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → (N : ℤ) ≤ Y → Y.natAbs ≤ 2 * N →
      ∀ ρ : WeightedPolynomial ℚ (Fin s.length) →ₐ[ℚ] ℚ,
        ρ (MvPolynomial.X (Sum.inl (1 : Fin 3))) = (X : ℚ) →
        ρ (MvPolynomial.X (Sum.inl (0 : Fin 3))) = (Y : ℚ) →
        ρ (MvPolynomial.X (Sum.inl (2 : Fin 3))) = 1 →
        Q ≤ RingHom.ker ρ.toRingHom →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        ¬ AffineGridAlignment.Aligned B X Y →
        E < e := by
  obtain ⟨N₀, hN₀⟩ := CriticalNonalignedSourceExclusion.eventually_no_dyadic_point C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL s d D I j c J₀ hs hdeg hD hmin Q instQ hrel hQ e β hOrd hheight hlarge a ha hd hI hj hcard hiB hjB S T hiS hjT X Y hXN hYNlower hYN ρ hX hY hZ hpoint hposS hposT hnonaligned
  by_contra hnot
  have he : e ≤ E := le_of_not_gt hnot
  have hZnot : MvPolynomial.X (Sum.inl (2 : Fin 3)) ∉ Q := by
    intro hm
    have hz := RingHom.mem_ker.mp (hpoint hm)
    exact one_ne_zero (hZ.symm.trans hz)
  let p := OrdinaryCurveSourcePoint.point c D I J₀ hD hmin hdeg Q hrel hQ hZnot
  have hsource := (OrdinaryCurveSourceHeight.height_eq c D I J₀ Q hrel hD hmin hdeg hQ hZnot).trans hheight
  have hactual := OrdinaryCurveMultiplicityComparison.source_multiplicity_le s c D I J₀ hs hD hmin hdeg
    Q hrel hQ hZnot hsource e β hOrd
  have hbound := hactual.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he) (Nat.cast_nonneg D))
  have hhost := OrdinaryCurveHostImage.host_image s c D I J₀ hs hD hmin hdeg Q hrel hQ
    ρ (X : ℚ) (Y : ℚ) hX hY hZ hpoint
  exact hN₀ N hN L B hcrit hB hBL s d D I j hs hdeg hD p hsource hbound hlarge a ha hd hI hj hcard
    hiB hjB S T hiS hjT X Y hXN hYNlower hYN hhost hposS hposT hnonaligned

end PaperP1.CriticalNonalignedDegreeGap
