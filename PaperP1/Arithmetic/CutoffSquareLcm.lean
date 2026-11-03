module

public import PaperP1.Arithmetic.CutoffSquareParts
public import PaperP1.Arithmetic.PrimePowerAllocations

/-! # The exact lcm of cutoff quotients of distinct nearby actual values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CutoffSquareLcm

open Finset PaperP1.CutoffSquareParts

variable {ι : Type*} [Fintype ι]

def smoothLcm (Y : ℕ) (v : ι → ℕ) : ℕ := univ.lcm fun i ↦ smallPart Y (v i)

def squareProduct (Y : ℕ) (v : ι → ℕ) : ℕ := ∏ i, largeSquarePart Y (v i) ^ 2

theorem smooth_lcm_pos (Y : ℕ) (v : ι → ℕ) : 0 < smoothLcm Y v := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun i _ ↦ (small_part_pos Y (v i)).ne')

theorem square_product_pos (Y : ℕ) (v : ι → ℕ) : 0 < squareProduct Y v :=
  prod_pos fun i _ ↦ pow_pos (large_square_part_pos Y (v i)) _

theorem smooth_lcm_prime {Y p : ℕ} (v : ι → ℕ) (hp : p.Prime) (hd : p ∣ smoothLcm Y v) : p ≤ Y := by
  classical
  obtain ⟨i, _hi, hpow⟩ := PrimePowerAllocations.prime_power_receiver univ (fun i ↦ smallPart Y (v i)) p 1
    hp (by decide) (fun i _ ↦ small_part_pos Y (v i)) (by simpa only [pow_one, smoothLcm] using hd)
  exact prime_dvd_small_part hp (by simpa only [pow_one] using hpow)

theorem smooth_square_coprime (Y : ℕ) (v : ι → ℕ) : Nat.Coprime (smoothLcm Y v) (squareProduct Y v) := by
  classical
  apply Nat.coprime_of_dvd
  intro p hp hs ha
  have hlo := smooth_lcm_prime v hp hs
  obtain ⟨i, _hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff (fun i ↦ largeSquarePart Y (v i) ^ 2)).mp ha
  have hhi := (prime_dvd_large_square hp (hp.dvd_of_dvd_pow hpi)).1
  omega

theorem square_product_eq (Y : ℕ) (v : ι → ℕ) :
    squareProduct Y v = (∏ i, largeSquarePart Y (v i)) ^ 2 := by
  rw [squareProduct, Finset.prod_pow]

theorem subset_square_dvd_lcm (Y : ℕ) (v : ι → ℕ) (T : Finset ι)
    (hpair : Pairwise fun i j ↦ Nat.Coprime (largeSquarePart Y (v i)) (largeSquarePart Y (v j))) :
    (T.prod fun i ↦ largeSquarePart Y (v i) ^ 2) ∣ univ.lcm (fun i ↦ quotient Y (v i)) := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _hi j _hj hij
    exact Nat.coprime_iff_isRelPrime.mp ((hpair hij).pow 2 2)
  · intro i _hi
    have hd : largeSquarePart Y (v i) ^ 2 ∣ quotient Y (v i) :=
      ⟨smallPart Y (v i), by unfold quotient; ring⟩
    exact hd.trans (dvd_lcm (mem_univ i))

theorem quotient_lcm (Y : ℕ) (v : ι → ℕ)
    (hpair : Pairwise fun i j ↦ Nat.Coprime (largeSquarePart Y (v i)) (largeSquarePart Y (v j))) :
    univ.lcm (fun i ↦ quotient Y (v i)) = smoothLcm Y v * squareProduct Y v := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i _hi
    change smallPart Y (v i) * largeSquarePart Y (v i) ^ 2 ∣ smoothLcm Y v * squareProduct Y v
    exact Nat.mul_dvd_mul (dvd_lcm (mem_univ i)) (dvd_prod_of_mem _ (mem_univ i))
  · have hs : smoothLcm Y v ∣ univ.lcm (fun i ↦ quotient Y (v i)) := by
      apply Finset.lcm_dvd
      intro i _hi
      exact (show smallPart Y (v i) ∣ quotient Y (v i) from ⟨largeSquarePart Y (v i) ^ 2, rfl⟩).trans
        (dvd_lcm (mem_univ i))
    have ha : squareProduct Y v ∣ univ.lcm (fun i ↦ quotient Y (v i)) := subset_square_dvd_lcm Y v univ hpair
    exact (smooth_square_coprime Y v).mul_dvd_of_dvd_of_dvd hs ha

theorem quotient_lcm_of_close (Y : ℕ) (v : ι → ℕ) (hinj : Function.Injective v)
    (hdist : ∀ i j, Nat.dist (v i) (v j) ≤ Y) :
    univ.lcm (fun i ↦ quotient Y (v i)) = smoothLcm Y v * squareProduct Y v :=
  quotient_lcm Y v (fun i j hij ↦ large_square_parts_coprime (fun h ↦ hij (hinj h)) (hdist i j))

theorem quotient_lcm_dvd_values (Y : ℕ) (v : ι → ℕ) (hv : ∀ i, 0 < v i) :
    univ.lcm (fun i ↦ quotient Y (v i)) ∣ univ.lcm v := by
  apply Finset.lcm_dvd
  intro i _hi
  exact (quotient_dvd Y (v i) (hv i)).trans (dvd_lcm (mem_univ i))

end PaperP1.CutoffSquareLcm
