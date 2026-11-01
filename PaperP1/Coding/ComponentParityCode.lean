module

public import PaperP1.Arithmetic.EvenSquareSelection
public import PaperP1.Coding.DefectCodeHamming

/-! # A parity code on disjoint small sets of actual integer values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentParityCode

open Finset PaperP1.Arithmetic

local instance componentCodePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def columns {m r : ℕ} (smallPrime : Fin r → ℕ) (blocks : Fin m → Finset ℕ)
    (i : Fin m) : Fin (r + 1) → F₂ :=
  Fin.lastCases ((blocks i).card : F₂) (fun j ↦ ∑ n ∈ blocks i, parityVec n (smallPrime j))

def parityMap {m r : ℕ} (smallPrime : Fin r → ℕ) (blocks : Fin m → Finset ℕ) :
    (Fin m → F₂) →ₗ[F₂] (Fin (r + 1) → F₂) :=
  Fintype.linearCombination F₂ (columns smallPrime blocks)

def selected {m : ℕ} (blocks : Fin m → Finset ℕ) (x : Fin m → F₂) : Finset ℕ :=
  (HammingBound.wordSupport x).biUnion blocks

theorem parityMap_coordinate {m r : ℕ} (smallPrime : Fin r → ℕ)
    (blocks : Fin m → Finset ℕ) (x : Fin m → F₂) (j : Fin r) :
    parityMap smallPrime blocks x j.castSucc =
      ∑ i : Fin m, x i * ∑ n ∈ blocks i, parityVec n (smallPrime j) := by
  simp [parityMap, columns, Fintype.linearCombination_apply, smul_eq_mul]

theorem parityMap_last {m r : ℕ} (smallPrime : Fin r → ℕ)
    (blocks : Fin m → Finset ℕ) (x : Fin m → F₂) :
    parityMap smallPrime blocks x (Fin.last r) = ∑ i : Fin m, x i * (blocks i).card := by
  simp [parityMap, columns, Fintype.linearCombination_apply, smul_eq_mul]

theorem sum_selected {m : ℕ} (blocks : Fin m → Finset ℕ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (x : Fin m → F₂) (a : ℕ → F₂) :
    (∑ n ∈ selected blocks x, a n) = ∑ i : Fin m, x i * ∑ n ∈ blocks i, a n := by
  rw [selected, sum_biUnion (fun i _ j _ hij ↦ hdisj hij)]
  exact DefectCodeRank.sum_wordSupport_eq_weighted_sum x (fun i ↦ ∑ n ∈ blocks i, a n)

theorem selected_nonempty {m : ℕ} (blocks : Fin m → Finset ℕ)
    (hblocks : ∀ i, (blocks i).Nonempty) (x : Fin m → F₂) (hx : x ≠ 0) :
    (selected blocks x).Nonempty := by
  by_contra h
  apply hx
  funext i
  by_contra hi
  change x i ≠ 0 at hi
  have hiMem : i ∈ HammingBound.wordSupport x := by simp [HammingBound.wordSupport, hi]
  exact h (biUnion_nonempty.mpr ⟨i, hiMem, hblocks i⟩)

theorem selected_card_le {m K : ℕ} (blocks : Fin m → Finset ℕ)
    (hsize : ∀ i, (blocks i).card ≤ K) (x : Fin m → F₂) :
    (selected blocks x).card ≤ K * hammingNorm x := by
  calc
    _ ≤ ∑ i ∈ HammingBound.wordSupport x, (blocks i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ HammingBound.wordSupport x, K := sum_le_sum (fun i _ ↦ hsize i)
    _ = K * hammingNorm x := by simp [Nat.mul_comm]

theorem kernel_even {m r : ℕ} (smallPrime : Fin r → ℕ) (blocks : Fin m → Finset ℕ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (x : Fin m → F₂)
    (hx : x ∈ LinearMap.ker (parityMap smallPrime blocks)) : Even (selected blocks x).card := by
  have hlast := congrFun (LinearMap.mem_ker.mp hx) (Fin.last r)
  rw [parityMap_last] at hlast
  change (∑ i : Fin m, x i * (blocks i).card) = 0 at hlast
  have hsum := sum_selected blocks hdisj x (fun _ ↦ (1 : F₂))
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsum
  have hcast : ((selected blocks x).card : F₂) = 0 := hsum.trans hlast
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ 2).mp hcast)

theorem kernel_square {m r : ℕ} (smallPrime : Fin r → ℕ) (blocks : Fin m → Finset ℕ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (hpositive : ∀ i n, n ∈ blocks i → n ≠ 0)
    (houtside : ∀ i p, (¬∃ j : Fin r, smallPrime j = p) → ∑ n ∈ blocks i, parityVec n p = 0)
    (x : Fin m → F₂) (hx : x ∈ LinearMap.ker (parityMap smallPrime blocks)) :
    ∃ q : ℕ, ∏ n ∈ selected blocks x, n = q ^ 2 := by
  apply (sum_parityVec_eq_zero_iff_prod_eq_sq (selected blocks x) id ?_).mp
  · ext p
    rw [Finsupp.finsetSum_apply]
    change (∑ n ∈ selected blocks x, parityVec n p) = 0
    rw [sum_selected blocks hdisj x]
    by_cases hp : ∃ j : Fin r, smallPrime j = p
    · obtain ⟨j, rfl⟩ := hp
      have hcoord := congrFun (LinearMap.mem_ker.mp hx) j.castSucc
      simpa only [parityMap_coordinate, Pi.zero_apply] using hcoord
    · simp only [houtside _ _ hp, mul_zero, sum_const_zero]
  · intro n hn
    obtain ⟨i, _, hni⟩ := mem_biUnion.mp hn
    exact hpositive i n hni

end PaperP1.ComponentParityCode
