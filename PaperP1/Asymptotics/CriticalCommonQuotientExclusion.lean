module

public import PaperP1.Diophantine.DisjointCommonQuotientBound
public import PaperP1.Asymptotics.CriticalGridGraphExclusion

/-! # A coefficient-uniform critical exclusion from the actual common-quotient curve identities -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v w

namespace PaperP1.CriticalCommonQuotientExclusion

open Polynomial Finset PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (a J : ℕ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (K : Type v) [Field K] [Algebra F K]
        (ι : Type w) [DecidableEq ι],
      ∀ (A bad : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (E e : ℕ),
        e ≤ E → 4 * (E + 1) ^ 2 ≤ A.card → bad.card ≤ 2 * e ^ 2 →
        (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        ∀ (b : ι → F), (∀ ν ∈ A \ bad, b ν ≠ 0) →
        ∀ (x y t : K), Transcendental F x →
          (∀ ν ∈ A \ bad, algebraMap F K (b ν) * aeval x (FormalWordPolynomials.linearOver F (I ν)) =
            t * (y + (j ν : K))) →
        ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
        ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
          (RingHom.ker (Polynomial.aevalAeval (R := F) x y).toRingHom ≤
            RingHom.ker (Polynomial.aevalAeval (R := F) (X : F) (Y : F)).toRingHom) →
          (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
          EvenIndependentValues.Independent (values X S) →
          Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
          False := by
  obtain ⟨N₀, hN₀⟩ := CriticalGridGraphExclusion.cutoff_lt_scale C a J ha
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ K _ _ ι _ A bad I j E e he hA hbad hdisj hcard hiB hjB b hb x y t hx hcommon S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect
  have hXNabs : N ≤ X.natAbs := by
    have hz : (N : ℤ) ≤ (X.natAbs : ℤ) := hXN.trans Int.le_natAbs
    exact_mod_cast hz
  have hgood := DisjointOffsetGrid.three_survivors A bad E e he hA hbad
  have hsmall := DisjointCommonQuotientBound.integral_point a B ha hB (A \ bad) hgood I j b
    (Set.Pairwise.mono sdiff_subset hdisj)
    (fun ν hν ↦ hcard ν (mem_sdiff.mp hν).1)
    (fun ν hν ↦ hiB ν (mem_sdiff.mp hν).1) (fun ν hν ↦ hjB ν (mem_sdiff.mp hν).1)
    hb x y t hx hcommon S T
    (fun ν hν ↦ hiS ν (mem_sdiff.mp hν).1) (fun ν hν ↦ hjT ν (mem_sdiff.mp hν).1)
    X Y (hYN.trans (Nat.mul_le_mul_left 2 hXNabs)) hpoint hposS hposT hind hdirect
  exact Nat.not_lt_of_ge hXNabs (hsmall.trans_lt (hN₀ N hN L B hcrit hB hBL))

end PaperP1.CriticalCommonQuotientExclusion
