module

public import PaperP1.Arithmetic.OffsetLinePrimeProduct

/-! # The actual shared odd-valuation primes on an offset line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLinePopulation

open Finset PaperP1.OffsetLineData PaperP1.OffsetLinePrimeProduct PaperP1.IntegralLine
  PaperP1.SaturationPrimes PaperP1.DefectivePredicate PaperP1.TruncatedKernelProducts PaperP1.Arithmetic

def offsetVector {L : ℕ} (v : Fin 3 → Fin (L + 1)) : Fin 3 → ℤ := fun i ↦ (v i).val - 1

def CollinearSet (line : Set (Fin 3 → ℤ)) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, ∀ v ∈ line, OnLine a b v

theorem collinearSet_of_real_line (a d : Fin 3 → ℝ) :
    CollinearSet {v : Fin 3 → ℤ | ∃ t : ℝ, ∀ i, (v i : ℝ) = a i + t * d i} := by
  intro p hp q hq r hr i j
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq
  obtain ⟨v, hv⟩ := hr
  have h : (((q i - p i) * (r j - p j) : ℤ) : ℝ) =
      (((q j - p j) * (r i - p i) : ℤ) : ℝ) := by
    push_cast
    rw [ht i, hs i, hv j, hs j, ht j, hv i]
    ring
  exact_mod_cast h

def pool (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ)) : Finset ℕ := by
  classical
  exact (Icc 2 (3 * N)).filter fun p ↦ Nat.Prime p ∧ H < (p : ℝ) ∧
    ∃ v : Fin 3 → Fin (L + 1), offsetVector v ∈ line ∧ ∀ i, p ∈ oddPrimeSupport (value (X i) (v i))

theorem mem_pool (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ)) (p : ℕ) :
    p ∈ pool N L H X line ↔ p ∈ Icc 2 (3 * N) ∧ Nat.Prime p ∧ H < (p : ℝ) ∧
      ∃ v : Fin 3 → Fin (L + 1), offsetVector v ∈ line ∧ ∀ i, p ∈ oddPrimeSupport (value (X i) (v i)) := by
  classical
  exact mem_filter

theorem mem_pool_iff_actual (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N)) (p : ℕ) :
    p ∈ pool N L H X line ↔ Nat.Prime p ∧ H < (p : ℝ) ∧
      ∃ v : Fin 3 → Fin (L + 1), offsetVector v ∈ line ∧ ∀ i, p ∈ oddPrimeSupport (value (X i) (v i)) := by
  constructor
  · exact fun h ↦ ((mem_pool N L H X line p).mp h).2
  · rintro ⟨hp, hH, v, hline, hodd⟩
    have hv := value_bounds hN hLN (hX 0) (v 0)
    have hdiv := dvd_of_mem_oddPrimeSupport (hodd 0)
    have hbound : p ≤ 3 * N := (Nat.le_of_dvd hv.1 hdiv).trans hv.2
    exact (mem_pool N L H X line p).mpr ⟨mem_Icc.mpr ⟨hp.two_le, hbound⟩, hp, hH, v, hline, hodd⟩

def offsets (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (p : pool N L H X line) : Fin 3 → Fin (L + 1) :=
  Classical.choose (((mem_pool N L H X line p.val).mp p.property).2.2.2)

theorem offsets_on_line (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (p : pool N L H X line) : offsetVector (offsets N L H X line p) ∈ line :=
  (Classical.choose_spec (((mem_pool N L H X line p.val).mp p.property).2.2.2)).1

theorem offsets_odd (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (p : pool N L H X line) (i : Fin 3) :
    p.val ∈ oddPrimeSupport (value (X i) (offsets N L H X line p i)) :=
  (Classical.choose_spec (((mem_pool N L H X line p.val).mp p.property).2.2.2)).2 i

theorem odd_offsets_unique {L p : ℕ} (H : ℝ) (hH : ((L + 1 : ℕ) : ℝ) ≤ H)
    (hp : Nat.Prime p) (hpH : H < (p : ℝ)) (X : Fin 3 → ℕ)
    (v w : Fin 3 → Fin (L + 1))
    (hv : ∀ i, p ∈ oddPrimeSupport (value (X i) (v i)))
    (hw : ∀ i, p ∈ oddPrimeSupport (value (X i) (w i))) : v = w := by
  funext i
  by_contra hne
  have hvalues : value (X i) (v i) ≠ value (X i) (w i) := by
    intro h
    exact hne (Fin.ext (Nat.add_left_cancel h))
  have hdist : (Nat.dist (value (X i) (v i)) (value (X i) (w i)) : ℝ) ≤ H :=
    (by exact_mod_cast value_dist_le (X i) (v i) (w i) :
      (Nat.dist (value (X i) (v i)) (value (X i) (w i)) : ℝ) ≤ (L + 1 : ℕ)).trans hH
  have hcop := kernels_coprime H _ _ hvalues hdist
  have hleft : p ∣ PaperP1.RankinSmallKernel.truncatedKernel H (value (X i) (v i)) :=
    (prime_dvd_kernel_iff H _ p hp).mpr (mem_filter.mpr ⟨hv i, hpH⟩)
  have hright : p ∣ PaperP1.RankinSmallKernel.truncatedKernel H (value (X i) (w i)) :=
    (prime_dvd_kernel_iff H _ p hp).mpr (mem_filter.mpr ⟨hw i, hpH⟩)
  have hdiv : p ∣ 1 := by
    have h := Nat.dvd_gcd hleft hright
    rwa [hcop.gcd_eq_one] at h
  exact hp.not_dvd_one hdiv

theorem chosen_points_iff_actual (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hH : ((L + 1 : ℕ) : ℝ) ≤ H) (a : Fin 3 → ℤ) :
    a ∈ points (offsets N L H X line) ↔ ∃ p ∈ pool N L H X line,
      ∃ v : Fin 3 → Fin (L + 1), a = offsetVector v ∧ offsetVector v ∈ line ∧
        ∀ i, p ∈ oddPrimeSupport (value (X i) (v i)) := by
  constructor
  · intro ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    exact ⟨p.val, p.property, offsets N L H X line p, rfl,
      offsets_on_line N L H X line p, offsets_odd N L H X line p⟩
  · rintro ⟨p, hp, v, rfl, _, hv⟩
    let q : pool N L H X line := ⟨p, hp⟩
    have hpdata := ((mem_pool N L H X line p).mp hp).2
    have heq := odd_offsets_unique H hH hpdata.1 hpdata.2.1 X
      (offsets N L H X line q) v (offsets_odd N L H X line q) hv
    apply mem_image.mpr
    exact ⟨q, mem_univ _, congrArg offsetVector heq⟩

theorem offsets_collinear (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hline : CollinearSet line) : Collinear (point (offsets N L H X line)) := by
  intro a b p
  exact hline _ (offsets_on_line N L H X line a) _ (offsets_on_line N L H X line b)
    _ (offsets_on_line N L H X line p)

theorem pool_product_le (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hline : CollinearSet line) : (pool N L H X line).prod id ≤ 6 * N * (L + 1) := by
  apply product_le_uniform X (offsets N L H X line) hN hLN hX
  · intro p hp
    exact ((mem_pool N L H X line p).mp hp).2.1
  · intro p i
    exact dvd_of_mem_oddPrimeSupport (offsets_odd N L H X line p i)
  · exact hinj
  · exact hdirect
  · exact offsets_collinear N L H X line hline

end PaperP1.OffsetLinePopulation
