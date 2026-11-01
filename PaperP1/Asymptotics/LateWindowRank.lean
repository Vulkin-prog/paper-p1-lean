module

public import PaperP1.Asymptotics.LatePrimeBudget
public import PaperP1.Arithmetic.LatePrimeStarts
public import PaperP1.Model.RawPrimeRank

/-! # The actual finite-character rank of every late source subfamily -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LateWindowRank

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.SubspaceFamilyRank PaperP1.ConditionalWindowRank
  PaperP1.OldValuePrimeBudget PaperP1.LatePrimeStarts

local instance lateWindowRankTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem finite_rank_le_cover {N q M : ℕ} (hq : 2 ≤ q) {A : Finset ℕ} (hA : A ⊆ starts N q) :
    rank (fun x ↦ effectiveRowSpace (startSystem M x (q - 1))) A ≤ (LateWindowPrimes.cover N).card := by
  have hpositive (x : ℕ) (hx : x ∈ A) : 0 < x := by
    have h := starts_late hq (hA hx)
    omega
  have hraw (n : ℕ) (hn : n ∈ rawValues A (q - 1)) : 3 * N ≤ 2 * n ∧ n < 2 * N := by
    obtain ⟨x, hx, hn⟩ := mem_biUnion.mp hn
    exact raw_values_late hq (mem_biUnion.mpr ⟨x, hA hx, hn⟩)
  exact (RawPrimeRank.family_rank_le M (q - 1) A hpositive).trans
    (card_le_card (LateWindowPrimes.oldPrimes_subset hraw))

theorem rank_bound_eventually (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ q M : ℕ, 2 ≤ q → ∀ A : Finset ℕ,
      A ⊆ starts N q →
        (rank (fun x ↦ effectiveRowSpace (startSystem M x (q - 1))) A : ℝ) ≤
          (17 / 12 + η) * N / Real.log N := by
  obtain ⟨N₀, hN₀, hbound⟩ := LatePrimeBudget.cover_bound_eventually η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN q M hq A hA
  have hfinite : (rank (fun x ↦ effectiveRowSpace (startSystem M x (q - 1))) A : ℝ) ≤
      (LateWindowPrimes.cover N).card := by exact_mod_cast finite_rank_le_cover (M := M) hq hA
  exact hfinite.trans (hbound N hN)

end PaperP1.LateWindowRank
