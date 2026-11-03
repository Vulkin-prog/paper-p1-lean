module

public import PaperP1.Asymptotics.CriticalGridGraphExclusion
public import PaperP1.Diophantine.DisjointEquationGraphDescent

/-! # A uniform large-scale exclusion after the actual bounded exceptional-equation deletion -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.CriticalDisjointEquationGraphExclusion

open Polynomial Finset PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (a J : ℕ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (ι : Type v) [DecidableEq ι],
      ∀ (A bad : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (E e : ℕ),
        e ≤ E → 4 * (E + 1) ^ 2 ≤ A.card → bad.card ≤ 2 * e ^ 2 →
        (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
        ∀ p q : F[X], q ≠ 0 → IsCoprime p q → max p.natDegree q.natDegree = a →
          (∀ ν ∈ A \ bad, ∀ z ∈ I ν, p.eval (-(z : F)) = -(j ν : F) * q.eval (-(z : F))) →
          ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
            p.eval (X : F) = (Y : F) * q.eval (X : F) →
            (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
            EvenIndependentValues.Independent (values X S) →
            Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
            False := by
  obtain ⟨N₀, hN₀⟩ := CriticalGridGraphExclusion.cutoff_lt_scale C a J ha
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ ι _ A bad I j E e he hA hbad hdisj hcard hiB hjB S T hiS hjT p q hq0 hcop hdegree hgrid X Y hXN hYN hpoint hposS hposT hind hdirect
  have hXNabs : N ≤ X.natAbs := by
    have hz : (N : ℤ) ≤ (X.natAbs : ℤ) := hXN.trans Int.le_natAbs
    exact_mod_cast hz
  have hgood := DisjointOffsetGrid.three_survivors A bad E e he hA hbad
  have hsmall := DisjointEquationGraphDescent.integral_point a B ha hB (A \ bad) I j hgood
    (Set.Pairwise.mono sdiff_subset hdisj)
    (fun ν hν ↦ hcard ν (mem_sdiff.mp hν).1)
    (fun ν hν ↦ hiB ν (mem_sdiff.mp hν).1) (fun ν hν ↦ hjB ν (mem_sdiff.mp hν).1) S T
    (fun ν hν ↦ hiS ν (mem_sdiff.mp hν).1) (fun ν hν ↦ hjT ν (mem_sdiff.mp hν).1)
    p q hq0 hcop hdegree hgrid X Y (hYN.trans (Nat.mul_le_mul_left 2 hXNabs)) hpoint hposS hposT hind hdirect
  exact Nat.not_lt_of_ge hXNabs (hsmall.trans_lt (hN₀ N hN L B hcrit hB hBL))

end PaperP1.CriticalDisjointEquationGraphExclusion
