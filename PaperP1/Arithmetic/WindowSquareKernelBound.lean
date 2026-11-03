module

public import PaperP1.Arithmetic.CutoffSquareParts
public import PaperP1.Asymptotics.TwoSmallKernelWindowUpper

/-! # Outside the two-small-kernel population, at most one value has a large square part -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowSquareKernelBound

open Finset PaperP1.Arithmetic PaperP1.LargeOddKernel PaperP1.CutoffSquareParts
  PaperP1.DefectivePredicate PaperP1.NormalizedWindowSets PaperP1.Model

theorem square_kernel_le (H Y n : ℕ) (hn : 0 < n) :
    largeSquarePart Y n ^ 2 * largeOddKernel H n ≤ n := by
  let q := smallPart Y n * largeOddKernel Y n
  have hq : 0 < q := Nat.mul_pos (small_part_pos Y n)
    (PaperP1.SmallPrimeBudget.largeOddKernel_pos Y n)
  have heq : n = largeSquarePart Y n ^ 2 * q := (decomposition Y n hn).trans (by dsimp [q]; ring)
  have hparity : parityVec n = parityVec q := by
    rw [heq, parityVec_mul (pow_ne_zero _ (large_square_part_pos Y n).ne') hq.ne',
      parityVec_pow_two, zero_add]
  have hsupp : oddPrimeSupport n = oddPrimeSupport q := by
    ext p
    simp only [mem_oddPrimeSupport_iff_parityVec_ne_zero, hparity]
  have hkernel : largeOddKernel H n = largeOddKernel H q := by
    unfold largeOddKernel
    rw [hsupp]
  have hk : largeOddKernel H q ≤ q := by
    have h := PaperP1.TruncatedKernelProducts.kernel_le (H : ℝ) q hq
    simpa only [PaperP1.RankinSmallKernel.truncatedKernel_eq_floor _ (Nat.cast_nonneg H),
      Nat.floor_natCast] using h
  rw [hkernel]
  exact (Nat.mul_le_mul_left (largeSquarePart Y n ^ 2) hk).trans_eq heq.symm

def largeSquareValues (N L Y x : ℕ) : Finset ℕ := by
  classical
  exact (values x L).filter fun v ↦ (N : ℝ) ^ (2 / 3 : ℝ) <
    ((largeSquarePart Y v ^ 2 : ℕ) : ℝ)

theorem large_square_small_kernel {N L Y x v : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hscale : (3 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) (hx : x ∈ dyadicBlock N)
    (hv : v ∈ largeSquareValues N L Y x) :
    (largeOddKernel (L + 1) v : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hvW, hvS⟩ := mem_filter.mp hv
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  have hvpos := values_positive (show 2 ≤ x by have hh := (mem_Ico.mp hx).1; omega) v hvW
  have hvhi : v ≤ 3 * N := by
    obtain ⟨_, hvhi⟩ := mem_Ico.mp ((values_eq_interval hxpos) ▸ hvW)
    have hxhi := (mem_Ico.mp hx).2
    omega
  have hbound : ((largeSquarePart Y v ^ 2 : ℕ) : ℝ) * largeOddKernel (L + 1) v ≤ 3 * N := by
    exact_mod_cast (square_kernel_le (L + 1) Y v hvpos).trans hvhi
  have hpower : (3 : ℝ) * N ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * N := mul_le_mul_of_nonneg_right hscale hn.le
      _ = _ := by
        have hpow := Real.rpow_add hn (1 / 3 : ℝ) 1
        rw [Real.rpow_one] at hpow
        rw [← hpow, ← Real.rpow_add hn]
        congr 1
        norm_num
  by_contra hk
  have hprod := mul_lt_mul_of_pos_left (lt_of_not_ge hk)
    (Real.rpow_pos_of_pos hn (2 / 3 : ℝ))
  have hprod' := mul_lt_mul_of_pos_right hvS
    (lt_trans (Real.rpow_pos_of_pos hn (2 / 3 : ℝ)) (lt_of_not_ge hk))
  linarith

theorem outside_two_kernel {N L Y x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hscale : (3 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) (hx : x ∈ dyadicBlock N)
    (hout : x ∉ PaperP1.TwoSmallKernelWindows.windows N L (L + 1) ((N : ℝ) ^ (2 / 3 : ℝ))) :
    (largeSquareValues N L Y x).card ≤ 1 := by
  classical
  have hsub : largeSquareValues N L Y x ⊆
      PaperP1.TwoSmallKernelWindows.smallValues (L + 1) x L ((N : ℝ) ^ (2 / 3 : ℝ)) := by
    intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).1, large_square_small_kernel hN hL hscale hx hv⟩
  have hsmall : (PaperP1.TwoSmallKernelWindows.smallValues (L + 1) x L
      ((N : ℝ) ^ (2 / 3 : ℝ))).card ≤ 1 := by
    by_contra h
    exact hout (mem_filter.mpr ⟨hx, by omega⟩)
  exact (card_le_card hsub).trans hsmall

end PaperP1.WindowSquareKernelBound
