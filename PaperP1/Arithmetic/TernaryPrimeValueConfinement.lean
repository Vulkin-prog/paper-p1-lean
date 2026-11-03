module

public import PaperP1.Arithmetic.ProductConfinement
public import PaperP1.Arithmetic.TernaryPrimeTopProducts
public import PaperP1.Arithmetic.CRTSupportCover

/-! # Actual large individual primes supply the same finite product certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeValueConfinement

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryIndividualPrimes PaperP1.TernaryPrimeTopProducts

def largePrimes (U : Fin 3 → Finset ℕ) (H : ℕ) (Y : ℝ) : Finset ℕ := by
  classical
  exact (pool U H).filter fun p : ℕ ↦ Y < (p : ℝ)

theorem confinement_or_certificate (U : Fin 3 → Finset ℕ) (H k : ℕ)
    (Y N : ℝ) (hY : 1 < Y) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (htop : (topProduct U H k : ℝ) ≤ N) :
    (largePrimes U H Y).card ≤ k - 1 + ⌊Real.log N / Real.log Y⌋₊ ∨
      ∃ A ⊆ largePrimes U H Y, (∀ g ∈ A, (g : ℝ) ≤ N ^ (1 / (k : ℝ))) ∧
        N < (A.prod id : ℕ) ∧ (A.prod id : ℕ) ≤ N ^ (1 + 1 / (k : ℝ)) := by
  classical
  have hselected (A : Finset ℕ) (hA : A ⊆ largePrimes U H Y) (hcard : A.card = k) :
      (A.prod id : ℕ) ≤ N := by
    have hle := FiniteFactorTopProducts.selected_le (pool U H) A k (hA.trans (filter_subset _ _)) hcard
    exact (show ((A.prod id : ℕ) : ℝ) ≤ topProduct U H k by exact_mod_cast hle).trans htop
  exact ProductConfinement.confinement_or_certificate (largePrimes U H Y) Y N hY hN k hk
    (fun _ hg ↦ (mem_filter.mp hg).2) hselected

theorem certificate_mem {U : Fin 3 → Finset ℕ} {H R N D : ℕ} (X : Fin 3 → ℕ)
    (hoff : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    (base : Fin 3 → ℕ) (hbox : ∀ i, X i ∈ Ico (base i) (base i + D * N))
    (Y V : ℝ) (hY : 1 ≤ Y) (hV : 0 ≤ V)
    (A : Finset ℕ) (hA : A ⊆ largePrimes U H Y)
    (hlarge : (N : ℝ) < (A.prod id : ℕ)) (hsmall : (A.prod id : ℕ) ≤ V) :
    X ∈ CRTSupportCover.certificates base N D R Y V := by
  classical
  apply mem_biUnion.mpr
  refine ⟨A, mem_filter.mpr ⟨?_, hlarge⟩, ?_⟩
  · apply (OffsetFactorSupports.mem_integerSupports Y V hY hV A).mpr
    exact ⟨fun _ hg ↦ (mem_filter.mp (hA hg)).2, hsmall⟩
  · apply CRTSupportCover.mem_centres_of base (D * N) R A X hbox
    · intro p hp q hq hpq
      exact (Nat.coprime_primes (TernaryIndividualPrimes.prime_of_mem (mem_filter.mp (hA hp)).1)
        (TernaryIndividualPrimes.prime_of_mem (mem_filter.mp (hA hq)).1)).mpr hpq
    · intro p hp
      obtain ⟨u, hu, hpu⟩ := (TernaryIndividualPrimes.mem_pool U H p).mp (mem_filter.mp (hA hp)).1
      have hum := (mem_supportPool U u).mp hu
      refine ⟨fun i ↦ (u i : ℤ) - X i, fun i ↦ hoff i (u i) (hum i), ?_⟩
      intro i
      have heq : (X i : ℤ) + ((u i : ℤ) - X i) = u i := by ring
      rw [heq]
      exact Int.natCast_dvd_natCast.mpr (prime_dvd_value hpu i)

end PaperP1.TernaryPrimeValueConfinement
