module

public import PaperP1.Asymptotics.BoundedDegreeGridGraphExclusion
public import PaperP1.Diophantine.DisjointRationalSquareGraphBound
public import PaperP1.Algebra.OddDegreeFieldSquares

/-! # Bounded-degree rational square graphs have no large admissible critical-band hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v w

namespace PaperP1.CriticalRationalSquareGraphExclusion

open Polynomial Finset PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (ι : Type v) [DecidableEq ι],
      ∀ (a : ℕ), 0 < a → ∀ (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F),
        3 * E + 1 ≤ A.card → (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        (∀ ν ∈ A, c ν ≠ 0) →
        ∀ p q : F[X], q ≠ 0 → IsCoprime p q → max p.natDegree q.natDegree ≤ E →
          (∀ ν ∈ A, IsSquare (RationalGraphSquareRoots.value (c ν) (j ν : F)
            (FormalWordPolynomials.linearOver F (I ν)) p q)) →
        ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
        ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
          p.eval (X : F) = (Y : F) * q.eval (X : F) →
          (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
          EvenIndependentValues.Independent (values X S) →
          Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
          False := by
  obtain ⟨N₀, hN₀⟩ := BoundedDegreeGridGraphExclusion.cutoff_lt_scale C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ ι _ a ha A I j c hA hdisj hcard hiB hjB hc p q hq hcop hdegree hsq S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect
  have hXNabs : N ≤ X.natAbs := by
    have hz : (N : ℤ) ≤ (X.natAbs : ℤ) := hXN.trans Int.le_natAbs
    exact_mod_cast hz
  obtain ⟨ν, hν⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hIν : (I ν).Nonempty := Finset.card_pos.mp (by rw [hcard ν hν]; exact ha)
  have hd := RationalSquareGraphNonconstant.degree_pos (c ν) (j ν) (I ν) hIν p q hq (hc ν hν)
    (hsq ν hν) X Y hpoint (hposT (j ν) (hjT ν hν))
  have hsmall := DisjointRationalSquareGraphBound.integral_point a B ha hB A I j c hdisj hcard hiB hjB hc
    p q hq hcop (by omega) hsq S T hiS hjT X Y (hYN.trans (Nat.mul_le_mul_left 2 hXNabs)) hpoint
    hposS hposT hind hdirect
  exact Nat.not_lt_of_ge hXNabs (hsmall.trans_lt (hN₀ N hN L B hcrit hB hBL _ hd hdegree))

theorem squares_of_odd_extension {F : Type u} [Field F] {K : Type w} [Field K]
    [Algebra (FractionRing F[X]) K] {ι : Type v}
    (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F) (p q : F[X])
    (hdegree : Odd (Module.finrank (FractionRing F[X]) K))
    (r : ι → K) (hr : ∀ ν ∈ A, r ν ^ 2 = algebraMap (FractionRing F[X]) K
      (RationalGraphSquareRoots.value (c ν) (j ν : F) (FormalWordPolynomials.linearOver F (I ν)) p q)) :
    ∀ ν ∈ A, IsSquare (RationalGraphSquareRoots.value (c ν) (j ν : F)
      (FormalWordPolynomials.linearOver F (I ν)) p q) := by
  intro ν hν
  exact (OddDegreeFieldSquares.isSquare_iff hdegree _).mp ⟨r ν, by simpa only [pow_two] using (hr ν hν).symm⟩

theorem eventually_no_dyadic_point_of_odd_extension (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (ι : Type v) [DecidableEq ι],
      ∀ (a : ℕ), 0 < a → ∀ (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F),
        3 * E + 1 ≤ A.card → (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        (∀ ν ∈ A, c ν ≠ 0) →
        ∀ p q : F[X], q ≠ 0 → IsCoprime p q → max p.natDegree q.natDegree ≤ E →
        ∀ (K : Type w) [Field K] [Algebra (FractionRing F[X]) K],
          Odd (Module.finrank (FractionRing F[X]) K) → ∀ r : ι → K,
          (∀ ν ∈ A, r ν ^ 2 = algebraMap (FractionRing F[X]) K
            (RationalGraphSquareRoots.value (c ν) (j ν : F) (FormalWordPolynomials.linearOver F (I ν)) p q)) →
        ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
        ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
          p.eval (X : F) = (Y : F) * q.eval (X : F) →
          (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
          EvenIndependentValues.Independent (values X S) →
          Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
          False := by
  obtain ⟨N₀, hN₀⟩ := eventually_no_dyadic_point.{u,v} C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ ι _ a ha A I j c hA hdisj hcard hiB hjB hc p q hq hcop hdeg K _ _ hodd r hr S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect
  exact hN₀ N hN L B hcrit hB hBL F ι a ha A I j c hA hdisj hcard hiB hjB hc p q hq hcop hdeg
    (squares_of_odd_extension A I j c p q hodd r hr) S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect

end PaperP1.CriticalRationalSquareGraphExclusion
