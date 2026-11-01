module

public import PaperP1.Asymptotics.SmoothSelectionCertificates
public import PaperP1.Asymptotics.SmoothCertificateCount

/-! # A deterministic exceptional set for selections with few large kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeSmoothExceptionalSet

open Finset Filter PaperP1.LinearKernelFibres PaperP1.LargeOddKernel
  PaperP1.SmoothModulusHosts

def exceptional (C N Y W : ℕ) : Finset ℕ := by
  classical
  exact (Icc (W + 1) (C * N)).filter fun n ↦ ∃ m : ℕ,
    C * N ≤ m ∧ m ≤ C * N * Y ∧ Squarefree m ∧ largeOddKernel Y m = 1 ∧ HasCertificate (ι := Fin 26) m W n

theorem exceptional_count (C : ℕ) (A E A₀ ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y W : ℕ,
      (Y : ℝ) ≤ (Real.log N) ^ A → 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ →
      ((exceptional C N Y W).card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) := by
  classical
  obtain ⟨N₀, hN₀⟩ := PaperP1.SmoothCertificateCount.uniform_count (ι := Fin 26)
    A C E A₀ ε hA (Nat.cast_nonneg C) hε
  refine ⟨N₀, ?_⟩
  intro N hN Y W hY hW hwidth
  apply hN₀ N hN Y W (C * N) hY hW hwidth (exceptional C N Y W)
  intro n hn
  obtain ⟨hnbox, m, hmlo, hmhi, _hmSF, hmK, hmcert⟩ := mem_filter.mp hn
  obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hnbox
  refine ⟨by omega, hnhi, m, hmlo, ?_, hmK, hmcert⟩
  have hmcast : (m : ℝ) ≤ (C : ℝ) * N * Y := by exact_mod_cast hmhi
  exact hmcast.trans (mul_le_mul_of_nonneg_left hY (by positivity))

def radius (E : ℝ) (N : ℕ) : ℕ := ⌈E * Real.log N⌉₊ + 1

theorem radius_bounds (E : ℝ) (hE : 0 ≤ E) (N : ℕ) (hlog : 1 ≤ Real.log N) :
    0 < radius E N ∧ E * Real.log N ≤ (radius E N : ℝ) ∧
      (radius E N : ℝ) ≤ (E + 2) * Real.log N := by
  have hceil := Nat.le_ceil (E * Real.log N)
  have hupper := Nat.ceil_lt_add_one (mul_nonneg hE (by linarith : 0 ≤ Real.log N))
  dsimp [radius]
  push_cast
  refine ⟨by omega, by linarith, ?_⟩
  nlinarith only [hupper, hlog]

theorem constant_selection (a b A E ε : ℝ) (ha : 0 < a) (hA : 2 ≤ A)
    (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ M : ℕ → ℕ → Finset ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y : ℕ,
      (Y : ℝ) ≤ (Real.log N) ^ A →
      ((M N Y).card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) ∧
      ∀ n H t : ℕ, ∀ S : Finset ℤ,
        a * N ≤ n → (n : ℝ) ≤ b * N → (∀ u ∈ S, (u.natAbs : ℝ) ≤ E * Real.log N) →
        t + 26 ≤ S.card →
        (∀ u ∈ S, ∀ v ∈ S, u ≠ v → (N : ℝ) ^ (1 / 2 : ℝ) <
          (largeOddKernel H (value n u) : ℝ) * (largeOddKernel H (value n v) : ℝ)) →
        (S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) < (largeOddKernel Y (value n u) : ℝ)).card < t →
        n ∈ M N Y ∧ ∀ u ∈ S, 0 < (n : ℤ) + u ∧ (value n u : ℤ) = (n : ℤ) + u := by
  classical
  obtain ⟨C, hC, hcompare⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨Nc, hNc⟩ := exceptional_count C A (E + 2) 1 ε hA hε
  obtain ⟨Ns, hNs⟩ := PaperP1.SmoothSelectionCertificates.source_certificates C hC (E + 2) 1
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨fun N Y ↦ exceptional C N Y (radius E N), max Nc (max Ns Nl), ?_⟩
  intro N hN Y hY
  have hlog : 1 ≤ Real.log N := hNl N (by omega)
  have hR := radius_bounds E hE N hlog
  have hwidth : (radius E N : ℝ) ≤ (E + 2) * (Real.log N) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hR.2.2
  refine ⟨hNc N (by omega) Y _ hY hR.1 hwidth, ?_⟩
  intro n H t S hnlo hnhi hS hcard hpair hlarge
  have hcomp := hcompare N n hnlo hnhi
  have hS' : ∀ u ∈ S, u.natAbs ≤ radius E N := by
    intro u hu
    exact_mod_cast (hS u hu).trans hR.2.1
  obtain ⟨hWn, m, hmlo, hmhi, hmSF, hmK, hmcert⟩ := hNs N (by omega) H Y (radius E N) n t S
    hR.1 hwidth hcomp.1 hcomp.2 hS' hcard hpair hlarge
  refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hcomp.2⟩,
    m, hmlo.le, by exact_mod_cast hmhi, hmSF, hmK, hmcert⟩, ?_⟩
  intro u hu
  have habs : |u| ≤ (radius E N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hS' u hu
  have hlo := (abs_le.mp habs).1
  have hrn : (radius E N : ℤ) < n := by exact_mod_cast hWn
  exact ⟨by omega, value_cast n _ u hWn (hS' u hu)⟩

theorem companion_T6_2 (a b A D Cband c ε : ℝ) (t : ℕ) (ha : 0 < a)
    (hA : 2 ≤ A) (hD : 0 ≤ D) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M : ℕ → Finset ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      ((M N).card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) ∧
      ∀ n H : ℕ, ∀ S : Finset ℤ,
        a * N ≤ n → (n : ℝ) ≤ b * N →
        (∀ u ∈ S, (u.natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
        c * Real.log (Real.log N) < S.card →
        (∀ u ∈ S, ∀ v ∈ S, u ≠ v → (N : ℝ) ^ (1 / 2 : ℝ) <
          (largeOddKernel H (value n u) : ℝ) * (largeOddKernel H (value n v) : ℝ)) →
        (S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) <
          (PaperP1.RankinSmallKernel.truncatedKernel ((Real.log N) ^ A) (value n u) : ℝ)).card < t →
        n ∈ M N ∧ ∀ u ∈ S, 0 < (n : ℤ) + u ∧ (value n u : ℤ) = (n : ℤ) + u := by
  classical
  let E := D * PaperP1.CriticalBandScale.upperScale
  have hE : 0 ≤ E := mul_nonneg hD PaperP1.CriticalBandScale.upperScale_pos.le
  obtain ⟨M, Nc, hNc⟩ := constant_selection a b A E ε ha hA hE hε
  obtain ⟨Nb, hNb⟩ := PaperP1.CriticalBandScale.critical_band_scale Cband
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually
      (eventually_ge_atTop (((t + 26 : ℕ) : ℝ) / c)))
  refine ⟨fun N ↦ M N ⌊(Real.log N) ^ A⌋₊, max 2 (max Nc (max Nb Nl)), ?_⟩
  intro N hN L hband
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hY : (⌊(Real.log N) ^ A⌋₊ : ℝ) ≤ (Real.log N) ^ A := Nat.floor_le (Real.rpow_nonneg hl A)
  have hcount := hNc N (by omega) ⌊(Real.log N) ^ A⌋₊ hY
  refine ⟨hcount.1, ?_⟩
  intro n H S hnlo hnhi hS hlong hpair hlarge
  have hB := (hNb N (by omega) L hband).2
  have hS' : ∀ u ∈ S, (u.natAbs : ℝ) ≤ E * Real.log N := by
    intro u hu
    exact (hS u hu).trans (by simpa only [E, mul_assoc] using mul_le_mul_of_nonneg_left hB hD)
  have hsize : ((t + 26 : ℕ) : ℝ) ≤ c * Real.log (Real.log N) := by
    have h := (div_le_iff₀ hc).mp (hNl N (by omega))
    nlinarith only [h]
  have hcard : t + 26 ≤ S.card := by exact_mod_cast hsize.trans hlong.le
  have hlarge' : (S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) <
      (largeOddKernel ⌊(Real.log N) ^ A⌋₊ (value n u) : ℝ)).card < t := by
    simpa only [PaperP1.RankinSmallKernel.truncatedKernel_eq_floor _ (Real.rpow_nonneg hl A)] using hlarge
  exact hcount.2 n H t S hnlo hnhi hS' hcard hpair hlarge'

end PaperP1.LargeSmoothExceptionalSet
