module

public import PaperP1.Asymptotics.CriticalOrdinaryCurveExclusion
public import PaperP1.Geometry.OrdinaryCurveSourceHeight

/-! # Uniform exclusion for actual ordinary surface curves of bounded actual Hilbert degree

The height condition is on the actual prime in the ordinary radical surface.
The induced source height is a conclusion of the proved ambient comparison.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalOrdinarySurfaceCurveExclusion

open Polynomial Finset PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.SelectedProportionalPairs PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance weightedRing (ι : Type*) : CommRing (WeightedPolynomial ℚ ι) := inferInstance

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
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
      ∀ β : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q)
        (Polynomial.C (E : ℚ) * X + Polynomial.C β) →
        (OrdinaryCurveSourceHeight.surfaceIdeal c D I J₀ Q hrel).height = 1 →
        4 * (E + 1) ^ 2 ≤ s.length →
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i k ↦ Disjoint (I i) (I k)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
      ∀ ρ : WeightedPolynomial ℚ (Fin s.length) →ₐ[ℚ] ℚ,
        ρ (MvPolynomial.X (Sum.inl (1 : Fin 3))) = (X : ℚ) →
        ρ (MvPolynomial.X (Sum.inl (0 : Fin 3))) = (Y : ℚ) →
        ρ (MvPolynomial.X (Sum.inl (2 : Fin 3))) = 1 →
        Q ≤ RingHom.ker ρ.toRingHom →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        EvenIndependentValues.Independent (values X S) →
        Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) → False := by
  obtain ⟨N₀, hN₀⟩ := CriticalOrdinaryCurveExclusion.eventually_no_dyadic_point C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL s d D I j c J₀ hs hdeg hD hmin Q instQ hrel hQ β hOrd hheight hlarge a ha hd hI hj hcard hiB hjB S T hiS hjT X Y hXN hYN ρ hX hY hZ hpoint hposS hposT hind hdirect
  have hZnot : MvPolynomial.X (Sum.inl (2 : Fin 3)) ∉ Q := by
    intro hm
    have hz := RingHom.mem_ker.mp (hpoint hm)
    exact one_ne_zero (hZ.symm.trans hz)
  have hsource := (OrdinaryCurveSourceHeight.height_eq c D I J₀ Q hrel hD hmin hdeg hQ hZnot).trans hheight
  exact hN₀ N hN L B hcrit hB hBL s d D I j hs hdeg hD hmin Q hrel hQ β hOrd hsource hlarge a ha hd
    hI hj hcard hiB hjB S T hiS hjT X Y hXN hYN ρ hX hY hZ hpoint hposS hposT hind hdirect

end PaperP1.CriticalOrdinarySurfaceCurveExclusion
