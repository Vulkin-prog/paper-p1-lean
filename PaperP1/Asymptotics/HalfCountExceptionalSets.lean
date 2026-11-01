module

public import PaperP1.Asymptotics.TwoSmallKernelCount
public import PaperP1.Asymptotics.LargeSmoothExceptionalSet

/-! # Actual small-kernel exceptions and deterministic confinement at every stage -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountExceptionalSets

open Finset PaperP1.LinearKernelFibres PaperP1.LargeOddKernel PaperP1.SmallPrimeBudget

theorem zero_kernel (n : ℕ) : largeOddKernel 0 n = squarefreeKernel n := by
  have hsmall : smallOddSupport 0 n = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hd := mem_filter.mp hp
    have hprime := prime_of_mem_oddPrimeSupport hd.1
    have htwo := hprime.two_le
    omega
  have h := small_mul_large 0 n
  simpa only [smallOddPart, hsmall, prod_empty, one_mul] using h

def smallKernelCentres (G : Finset ℕ) (N W : ℕ) : Finset ℕ := by
  classical
  exact G.filter fun n ↦ PaperP1.TwoSmallKernelCount.HasPair 0 W n ((N : ℝ) ^ (1 / 2 : ℝ))

theorem small_kernel_count (a b E ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ G : Finset ℕ,
      0 < W → (W : ℝ) ≤ E * Real.log N → (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      ((smallKernelCentres G N W).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  classical
  obtain ⟨N₀, hN₀⟩ := PaperP1.TwoSmallKernelCount.companion_T6_1 a b 0 E 1 ε ha (by norm_num) hε
  refine ⟨N₀, ?_⟩
  intro N hN W G hW hwidth hG
  have hcount := hN₀ N hN 0 W (1 / 2) (by simp) hW
    (by simpa only [Real.rpow_one] using hwidth) (smallKernelCentres G N W) (by
      intro n hn
      obtain ⟨hnG, hpair⟩ := mem_filter.mp hn
      exact ⟨(hG n hnG).1, (hG n hnG).2, hpair⟩)
  exact hcount.2

theorem outside_pairs (G : Finset ℕ) (N W n : ℕ) (hn : n ∈ G)
    (hnot : n ∉ smallKernelCentres G N W) :
    ∀ a b : ℤ, a.natAbs ≤ W → b.natAbs ≤ W → a ≠ b →
      (N : ℝ) ^ (1 / 2 : ℝ) < (largeOddKernel 0 (value n a) : ℝ) * (largeOddKernel 0 (value n b) : ℝ) := by
  classical
  intro a b ha hb hab
  by_contra hprod
  have hcap : (PaperP1.TwoSmallKernelFibres.largeKernel 0 n a *
      PaperP1.TwoSmallKernelFibres.largeKernel 0 n b : ℕ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [PaperP1.TwoSmallKernelFibres.largeKernel, Nat.cast_mul] using le_of_not_gt hprod
  exact hnot (mem_filter.mpr ⟨hn, a, b, ha, hb, hab, hcap⟩)

theorem stage_confinement (a b A E ε : ℝ) (ha : 0 < a) (hA : 2 ≤ A)
    (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ M : ℕ → Finset ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((M N).card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) ∧
      ∀ W t n : ℕ, ∀ G : Finset ℕ, ∀ S : Finset ℤ,
        (W : ℝ) ≤ E * Real.log N → (∀ x ∈ G, a * N ≤ x ∧ (x : ℝ) ≤ b * N) →
        n ∈ G → n ∉ smallKernelCentres G N W → (∀ u ∈ S, u.natAbs ≤ W) → t + 26 ≤ S.card →
        (S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) <
          (PaperP1.RankinSmallKernel.truncatedKernel ((Real.log N) ^ A) (value n u) : ℝ)).card < t →
        n ∈ M N := by
  classical
  obtain ⟨M, N₀, hN₀⟩ := PaperP1.LargeSmoothExceptionalSet.constant_selection a b A E ε ha hA hE hε
  refine ⟨fun N ↦ M N ⌊(Real.log N) ^ A⌋₊, max 2 N₀, ?_⟩
  intro N hN
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : 0 ≤ (Real.log N) ^ A := Real.rpow_nonneg hl A
  have hcontrol := hN₀ N (by omega) ⌊(Real.log N) ^ A⌋₊ (Nat.floor_le hpow)
  refine ⟨hcontrol.1, ?_⟩
  intro W t n G S hwidth hG hn hnot hS hcard hlarge
  have hpairs := outside_pairs G N W n hn hnot
  have hSlog : ∀ u ∈ S, (u.natAbs : ℝ) ≤ E * Real.log N := by
    intro u hu
    exact (show (u.natAbs : ℝ) ≤ W by exact_mod_cast hS u hu).trans hwidth
  have hlarge' : (S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) <
      (largeOddKernel ⌊(Real.log N) ^ A⌋₊ (value n u) : ℝ)).card < t := by
    simpa only [PaperP1.RankinSmallKernel.truncatedKernel_eq_floor _ hpow] using hlarge
  exact (hcontrol.2 n 0 t S (hG n hn).1 (hG n hn).2 hSlog hcard
    (fun u hu v hv huv ↦ hpairs u v (hS u hu) (hS v hv) huv) hlarge').1

end PaperP1.HalfCountExceptionalSets
