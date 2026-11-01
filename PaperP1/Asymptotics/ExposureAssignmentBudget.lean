module

public import PaperP1.Arithmetic.CoprimeFactorCodes
public import PaperP1.Arithmetic.PrescribedPatternDivisors
public import PaperP1.Asymptotics.GrowingDegreePrimeBudget

/-! # Counting actual new prime-pattern assignments at one exposure step -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExposureAssignmentBudget

open Finset PaperP1.EvenPrimePatterns PaperP1.PrescribedPatternDivisors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def freshPatterns (rank : ι → ℕ) (i : ι) : Finset (Finset ι) :=
  (patterns.filter fun S ↦ i ∈ S).filter (fun S ↦ ¬ ∃ j ∈ S, rank j < rank i)

theorem freshPatterns_card (rank : ι → ℕ) (i : ι) :
    (freshPatterns rank i).card ≤ 2 ^ (Fintype.card ι - 1) := by
  have hmap : Set.MapsTo (fun S : Finset ι ↦ S.erase i)
      (freshPatterns rank i) ((univ.erase i).powerset : Finset (Finset ι)) := by
    intro S _
    apply mem_powerset.mpr
    intro j hj
    obtain ⟨hne, _⟩ := mem_erase.mp hj
    exact mem_erase.mpr ⟨hne, mem_univ _⟩
  have hinj : Set.InjOn (fun S : Finset ι ↦ S.erase i) (freshPatterns rank i) := by
    intro S hS T hT hST
    have hiS := (mem_filter.mp (mem_filter.mp hS).1).2
    have hiT := (mem_filter.mp (mem_filter.mp hT).1).2
    exact erase_injOn' i hiS hiT hST
  have hc := card_le_card_of_injOn (fun S : Finset ι ↦ S.erase i) hmap hinj
  simpa only [card_powerset, card_erase_of_mem (mem_univ i), card_univ] using hc

theorem newPart_eq_quotient (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (rank : ι → ℕ) (i : ι) :
    newPart q rank i = q i / prescribed q rank i := by
  have hd := congrArg (fun m ↦ m / prescribed q rank i) (coordinate_split q hq hsq rank i)
  simpa only [Nat.mul_div_right _ (prescribed_pos q rank i)] using hd

theorem card_fresh_families (rank : ι → ℕ) (i : ι) (m q : ℕ) (hq : 0 < q) (hm : m ∣ q)
    (V : Finset (freshPatterns rank i → ℕ))
    (hsf : ∀ D ∈ V, ∀ S, Squarefree (D S)) (hprod : ∀ D ∈ V, ∏ S, D S = m)
    (hcop : ∀ D ∈ V, Pairwise fun S T ↦ Nat.Coprime (D S) (D T)) :
    V.card ≤ (2 ^ (Fintype.card ι - 1)) ^ q.primeFactors.card := by
  have hcard := PaperP1.CoprimeFactorCodes.card_families m V hsf hprod hcop
  have hb : Fintype.card (freshPatterns rank i) ≤ 2 ^ (Fintype.card ι - 1) := by
    simpa only [Fintype.card_coe] using freshPatterns_card rank i
  have hω := card_le_card (Nat.primeFactors_mono hm hq.ne')
  have hBpos : 0 < 2 ^ (Fintype.card ι - 1) := by positivity
  exact hcard.trans ((Nat.pow_le_pow_left hb m.primeFactors.card).trans
    (Nat.pow_le_pow_right (by omega) hω))

theorem uniform_fresh_assignment_budget (hv : 2 ≤ Fintype.card ι)
    (c K ε : ℝ) (hc : 0 ≤ c) (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q m d : ℕ, ∀ rank : ι → ℕ, ∀ i : ι,
      0 < q → m ∣ q → (d : ℝ) ≤ c * Real.log (Real.log N) → (q : ℝ) ≤ (K * N) ^ d →
      ∀ V : Finset (freshPatterns rank i → ℕ),
        (∀ D ∈ V, ∀ S, Squarefree (D S)) → (∀ D ∈ V, ∏ S, D S = m) →
        (∀ D ∈ V, Pairwise fun S T ↦ Nat.Coprime (D S) (D T)) →
        (V.card : ℝ) ≤ (N : ℝ) ^ (c * ((Fintype.card ι : ℝ) - 1) * Real.log 2 + ε) := by
  let B := 2 ^ (Fintype.card ι - 1)
  have hB : 2 ≤ B := by
    exact (by norm_num : 2 = 2 ^ 1).le.trans
      (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega))
  have hBr : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  obtain ⟨N₀, hN₀⟩ := PaperP1.GrowingDegreePrimeBudget.exponential_prime_budget_additive
    c K ε hc hK hε B hBr
  refine ⟨N₀, ?_⟩
  intro N hN q m d rank i hq hm hd hheight V hsf hprod hcop
  have hcount : (V.card : ℝ) ≤ (B : ℝ) ^ q.primeFactors.card := by
    exact_mod_cast card_fresh_families rank i m q hq hm V hsf hprod hcop
  have hp := hN₀ N hN q d hq hd hheight
  have hlB : Real.log (B : ℝ) = ((Fintype.card ι : ℝ) - 1) * Real.log 2 := by
    dsimp [B]
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
    norm_num
  rw [hlB] at hp
  simpa only [mul_assoc] using hcount.trans hp

end PaperP1.ExposureAssignmentBudget
