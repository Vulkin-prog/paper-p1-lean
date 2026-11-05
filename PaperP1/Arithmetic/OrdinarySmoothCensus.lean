module

public import PaperP1.Arithmetic.ReciprocalOddPivots

/-! # Exact largest-prime recursion for the ordinary smooth population

Every positive integer above one has exactly one representation p*m with
p its largest prime factor and all prime factors of m at most p.
This finite identity is not an asymptotic smooth-number estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySmoothCensus

open Finset OddPrimePivot DefectCounting ReciprocalOddPivots

@[simp] theorem largestPrimeFactor_one : largestPrimeFactor 1 = 1 := by
  simp [largestPrimeFactor]

theorem largestPrimeFactor_prime {p : ℕ} (hp : p.Prime) : largestPrimeFactor p = p := by
  simp only [largestPrimeFactor, hp.primeFactors, sup_singleton, id_eq]
  exact max_eq_right hp.one_lt.le

theorem largestPrimeFactor_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    largestPrimeFactor (a * b) = max (largestPrimeFactor a) (largestPrimeFactor b) := by
  simp only [largestPrimeFactor, Nat.primeFactors_mul ha hb, sup_union]
  omega

theorem largestPrimeFactor_of_dvd {a n : ℕ} (hd : a ∣ n) (hn : n ≠ 0) :
    largestPrimeFactor a ≤ largestPrimeFactor n := by
  apply max_le (le_max_left _ _)
  exact (Finset.sup_mono (Nat.primeFactors_mono hd hn)).trans (le_max_right _ _)

theorem largestPrimeFactor_prime_dvd {n : ℕ} (hn : 1 < n) :
    (largestPrimeFactor n).Prime ∧ largestPrimeFactor n ∣ n := by
  obtain ⟨p, hp, he⟩ := exists_mem_eq_sup n.primeFactors (Nat.nonempty_primeFactors.mpr hn) id
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hid : largestPrimeFactor n = p := by
    rw [largestPrimeFactor, he]
    exact max_eq_right hpprime.one_lt.le
  rw [hid]
  exact ⟨hpprime, Nat.dvd_of_mem_primeFactors hp⟩

def smoothUpTo (X Y : ℕ) : Finset ℕ := (Icc 1 X).filter fun n ↦ largestPrimeFactor n ≤ Y

@[simp] theorem mem_smoothUpTo {X Y n : ℕ} :
    n ∈ smoothUpTo X Y ↔ 1 ≤ n ∧ n ≤ X ∧ largestPrimeFactor n ≤ Y := by
  simp only [smoothUpTo, mem_filter, mem_Icc, and_assoc]

theorem smoothUpTo_mono {X X' Y Y' : ℕ} (hX : X ≤ X') (hY : Y ≤ Y') :
    smoothUpTo X Y ⊆ smoothUpTo X' Y' := by
  intro n hn
  obtain ⟨h1, hx, hy⟩ := mem_smoothUpTo.mp hn
  exact mem_smoothUpTo.mpr ⟨h1, hx.trans hX, hy.trans hY⟩

def factorPairs (X Y : ℕ) : Finset (Σ _p : ℕ, ℕ) :=
  (smallPrimesUpTo Y).sigma fun p ↦ smoothUpTo (X / p) p

def value (z : Σ _p : ℕ, ℕ) : ℕ := z.1 * z.2

theorem factorPair_properties {X Y : ℕ} {z : Σ _p : ℕ, ℕ} (hz : z ∈ factorPairs X Y) :
    1 < value z ∧ value z ≤ X ∧ largestPrimeFactor (value z) = z.1 ∧ z.1 ≤ Y := by
  obtain ⟨hp, hm⟩ := mem_sigma.mp hz
  obtain ⟨hpprime, hpY⟩ := mem_smallPrimesUpTo.mp hp
  obtain ⟨hm1, hmX, hmp⟩ := mem_smoothUpTo.mp hm
  have hm0 : z.2 ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, hpY⟩
  · change 1 < z.1 * z.2
    exact hpprime.one_lt.trans_le (by nlinarith only [hm1])
  · change z.1 * z.2 ≤ X
    have hh := (Nat.le_div_iff_mul_le hpprime.pos).mp hmX
    nlinarith only [hh]
  · rw [value, largestPrimeFactor_mul hpprime.ne_zero hm0, largestPrimeFactor_prime hpprime]
    exact max_eq_left hmp

theorem factorPairs_injective (X Y : ℕ) : Set.InjOn value (factorPairs X Y : Set (Σ _p : ℕ, ℕ)) := by
  intro z hz w hw he
  have hp : z.1 = w.1 := by
    rw [← (factorPair_properties hz).2.2.1, ← (factorPair_properties hw).2.2.1, he]
  have hp0 : z.1 ≠ 0 := (mem_smallPrimesUpTo.mp (mem_sigma.mp hz).1).1.ne_zero
  have hm : z.2 = w.2 := by
    change z.1 * z.2 = w.1 * w.2 at he
    rw [← hp] at he
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) he
  exact Sigma.ext hp (by simpa only [heq_eq_eq] using hm)

theorem factorPairs_image (X Y : ℕ) :
    (factorPairs X Y).image value = (smoothUpTo X Y).erase 1 := by
  ext n
  constructor
  · intro hn
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
    obtain ⟨h1, hx, hp, hpy⟩ := factorPair_properties hz
    exact mem_erase.mpr ⟨by omega, mem_smoothUpTo.mpr ⟨h1.le, hx, hp ▸ hpy⟩⟩
  · intro hn
    obtain ⟨hne, hs⟩ := mem_erase.mp hn
    obtain ⟨h1, hx, hy⟩ := mem_smoothUpTo.mp hs
    have h2 : 1 < n := by omega
    obtain ⟨hp, hd⟩ := largestPrimeFactor_prime_dvd h2
    let p := largestPrimeFactor n
    have hprod : p * (n / p) = n := Nat.mul_div_cancel' hd
    have hquot : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
    have hquotX : n / p ≤ X / p := Nat.div_le_div_right hx
    have hquotP : largestPrimeFactor (n / p) ≤ p :=
      largestPrimeFactor_of_dvd (Nat.div_dvd_of_dvd hd) (by omega)
    apply mem_image.mpr
    refine ⟨⟨p, n / p⟩, mem_sigma.mpr ⟨mem_smallPrimesUpTo.mpr ⟨hp, hy⟩,
      mem_smoothUpTo.mpr ⟨hquot, hquotX, hquotP⟩⟩, hprod⟩

theorem smooth_recursion (X Y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    (smoothUpTo X Y).card = 1 + ∑ p ∈ smallPrimesUpTo Y, (smoothUpTo (X / p) p).card := by
  have h1 : 1 ∈ smoothUpTo X Y := mem_smoothUpTo.mpr ⟨by omega, hX, by simpa using hY⟩
  have hh := card_image_of_injOn (factorPairs_injective X Y)
  rw [factorPairs_image, card_erase_of_mem h1, factorPairs, card_sigma] at hh
  have hpos := card_pos.mpr ⟨1, h1⟩
  omega

theorem smooth_reciprocal_identity (X Y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    (∑ n ∈ smoothUpTo X Y, 1 / (largestPrimeFactor n : ℝ)) =
      1 + ∑ p ∈ smallPrimesUpTo Y, ((smoothUpTo (X / p) p).card : ℝ) / p := by
  have h1 : 1 ∈ smoothUpTo X Y := mem_smoothUpTo.mpr ⟨by omega, hX, by simpa using hY⟩
  have hh : (∑ n ∈ (smoothUpTo X Y).erase 1, 1 / (largestPrimeFactor n : ℝ)) =
      ∑ p ∈ smallPrimesUpTo Y, ((smoothUpTo (X / p) p).card : ℝ) / p := by
    rw [← factorPairs_image]
    rw [sum_image (factorPairs_injective X Y)]
    calc
      _ = ∑ z ∈ factorPairs X Y, 1 / (z.1 : ℝ) := by
        apply sum_congr rfl
        intro z hz
        rw [(factorPair_properties hz).2.2.1]
      _ = _ := by rw [factorPairs, sum_sigma]; simp [div_eq_mul_inv, mul_comm]
  have hs := sum_erase_add (smoothUpTo X Y) (fun n ↦ 1 / (largestPrimeFactor n : ℝ)) h1
  rw [largestPrimeFactor_one] at hs
  norm_num only [Nat.cast_one, div_one] at hs
  linarith only [hs, hh]

theorem ordinary_reciprocal_identity (X : ℕ) (hX : 1 ≤ X) :
    primeSum X = 1 + ∑ p ∈ smallPrimesUpTo X, ((smoothUpTo (X / p) p).card : ℝ) / p := by
  have hs : smoothUpTo X X = Icc 1 X := by
    apply filter_eq_self.mpr
    intro n hn
    obtain ⟨hn1, hnX⟩ := mem_Icc.mp hn
    apply max_le hX
    apply Finset.sup_le
    intro p hp
    exact (Nat.le_of_mem_primeFactors hp).trans hnX
  simpa only [hs, primeSum] using smooth_reciprocal_identity X X hX hX

end PaperP1.OrdinarySmoothCensus
