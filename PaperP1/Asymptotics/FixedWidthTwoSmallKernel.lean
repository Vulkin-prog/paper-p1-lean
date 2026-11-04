module

public import PaperP1.Asymptotics.FixedWidthSmallKernel
public import PaperP1.Asymptotics.TwoSmallKernelBlockCount

/-! # The literal two-small-kernel count for selected fixed-width logarithmic blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedWidthTwoSmallKernel

open Finset PaperP1.CriticalBandScale PaperP1.TwoSmallKernelBlocks

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def realSelectedStarts (G : Finset ℤ) (V : ℤ → Finset ℕ) (Y T : ℝ) : Finset ℤ :=
  G.filter (fun x ↦ 2 ≤ ((V x).filter (fun n ↦ (PaperP1.RankinSmallKernel.truncatedKernel Y n : ℝ) ≤ T)).card)

theorem realSelectedStarts_eq (G : Finset ℤ) (V : ℤ → Finset ℕ) (Y T : ℝ) (hY : 0 ≤ Y) :
    realSelectedStarts G V Y T = selectedStarts G V ⌊Y⌋₊ T := by
  ext x
  simp only [realSelectedStarts, selectedStarts, mem_filter, PaperP1.RankinSmallKernel.truncatedKernel_eq_floor Y hY]

theorem two_kernel (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (K D : ℕ) (hK : 1 ≤ K) (E C ε : ℝ) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, (N : ℤ) ≤ (K : ℤ) * x ∧ x ≤ (K * N : ℕ)) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ |(n : ℤ) - x| ≤ (D * (L + 1) : ℕ)) →
      ∀ T : ℝ, 0 ≤ T → ((selectedStarts G V H T).card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  let Q := 2 * K + 2
  obtain ⟨Nb, hb⟩ := TwoSmallKernelBlockCount.arbitrary_selected_blocks hHB hNG Q (by dsimp only [Q]; omega)
    ((D : ℝ) * upperScale) (E * upperScale) ε (mul_nonneg (Nat.cast_nonneg D) upperScale_pos.le) hε
  obtain ⟨Nl, hl⟩ := critical_band_scale C
  obtain ⟨Nr, hr⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (2 * (K : ℝ) * D * upperScale) 1 1 (by norm_num)
  refine ⟨max Nb (max Nl Nr), ?_⟩
  intro N hN L H hcrit hH G hG V hV T hT
  have hB : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N := (hl N (by omega) L hcrit).2
  let R := D * (L + 1)
  let O := FixedWidthSmallKernel.offsets R
  have hR : (R : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    simpa only [R, Nat.cast_mul, mul_assoc] using hh
  have hHlog : (H : ℝ) ≤ (E * upperScale) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hB hE
    have hH' : (H : ℝ) ≤ E * ((L + 1 : ℕ) : ℝ) := by simpa only [Nat.cast_add, Nat.cast_one] using hH
    simpa only [mul_assoc] using hH'.trans hh
  have hKR : 2 * (K : ℝ) * (R : ℝ) ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2 * (K : ℝ) by positivity)
    have hc := hr N (by omega)
    simp only [Real.rpow_one] at hc
    nlinarith only [hh, hc]
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hRN : (R : ℝ) ≤ N := by
    have hh := mul_nonneg (show 0 ≤ 2 * (K : ℝ) - 1 by linarith only [hK₁]) (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    nlinarith only [hh, hKR]
  have hheight : ∀ x ∈ G, ∀ u ∈ O, 0 < x + u → N ≤ Q * (x + u).toNat ∧ (x + u).toNat ≤ Q * N := by
    intro x hx u hu hpos
    have hxlo : (N : ℝ) ≤ (K : ℝ) * (x : ℝ) := by exact_mod_cast (hG x hx).1
    have hxhi : (x : ℝ) ≤ (K : ℝ) * N := by exact_mod_cast (hG x hx).2
    have hulo : -(R : ℝ) ≤ (u : ℝ) := by exact_mod_cast (mem_Icc.mp hu).1
    have huhi : (u : ℝ) ≤ (R : ℝ) := by exact_mod_cast (mem_Icc.mp hu).2
    have hnat : ((x + u).toNat : ℝ) = (x : ℝ) + u := by
      have hh := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.toNat_of_nonneg hpos.le)
      simpa only [Int.cast_natCast, Int.cast_add] using hh
    have hmul := mul_le_mul_of_nonneg_left hulo (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    have hnlo : (N : ℝ) ≤ 2 * (K : ℝ) * ((x + u).toNat : ℝ) := by
      rw [hnat]
      nlinarith only [hxlo, hmul, hKR]
    have hnhi : ((x + u).toNat : ℝ) ≤ ((K : ℝ) + 1) * N := by
      rw [hnat]
      linarith only [hxhi, huhi, hRN]
    have hnloN : N ≤ (2 * K) * (x + u).toNat := by exact_mod_cast hnlo
    have hnhiN : (x + u).toNat ≤ (K + 1) * N := by exact_mod_cast hnhi
    exact ⟨hnloN.trans (Nat.mul_le_mul_right _ (by dsimp only [Q]; omega)),
      hnhiN.trans (Nat.mul_le_mul_right _ (by dsimp only [Q]; omega))⟩
  have hV' : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ (n : ℤ) - x ∈ O := by
    intro x hx n hn
    obtain ⟨hpos, habs⟩ := hV x hx n hn
    exact ⟨hpos, mem_Icc.mpr (abs_le.mp habs)⟩
  exact hb N (by omega) G O H R hR hHlog (by intro u hu; exact hu) hheight V hV' T hT

theorem two_kernel_real (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (a K D E C ε : ℝ) (ha : 0 < a) (_hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ K * N) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * (L + 1)) →
      ∀ T : ℝ, 0 ≤ T → ((selectedStarts G V H T).card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨Q, hQ⟩ := exists_nat_ge (max 1 (max K (1 / a)))
  have hQ₁ : (1 : ℝ) ≤ Q := (le_max_left _ _).trans hQ
  have hQK : K ≤ (Q : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hQa : 1 / a ≤ (Q : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQa₁ : 1 ≤ (Q : ℝ) * a := (div_le_iff₀ ha).mp hQa
  obtain ⟨N₀, hN₀⟩ := two_kernel hHB hNG Q ⌈D⌉₊ (by exact_mod_cast hQ₁) E C ε hE hε
  refine ⟨N₀, ?_⟩
  intro N hN L H hcrit hH G hG V hV T hT
  have hG' : ∀ x ∈ G, (N : ℤ) ≤ (Q : ℤ) * x ∧ x ≤ (Q * N : ℕ) := by
    intro x hx
    have hlo : (N : ℝ) ≤ (Q : ℝ) * (x : ℝ) := by
      calc
        _ = 1 * (N : ℝ) := (one_mul _).symm
        _ ≤ ((Q : ℝ) * a) * N := mul_le_mul_of_nonneg_right hQa₁ (Nat.cast_nonneg N)
        _ = (Q : ℝ) * (a * N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hG x hx).1 (Nat.cast_nonneg Q)
    have hhi : (x : ℝ) ≤ (Q : ℝ) * N :=
      (hG x hx).2.trans (mul_le_mul_of_nonneg_right hQK (Nat.cast_nonneg N))
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hV' : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ |(n : ℤ) - x| ≤ (⌈D⌉₊ * (L + 1) : ℕ) := by
    intro x hx n hn
    obtain ⟨hpos, habs⟩ := hV x hx n hn
    refine ⟨hpos, ?_⟩
    have hb : ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ ((⌈D⌉₊ * (L + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      exact habs.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (by positivity))
    exact_mod_cast hb
  exact hN₀ N hN L H hcrit hH G hG' V hV' T hT

theorem two_kernel_real_cutoff (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (a K D E C ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, 0 ≤ Y → Y ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ K * N) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * (L + 1)) →
      ∀ T : ℝ, 0 ≤ T → ((realSelectedStarts G V Y T).card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := two_kernel_real hHB hNG a K D E C ε ha hD hE hε
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit Y hY hYband G hG V hV T hT
  rw [realSelectedStarts_eq G V Y T hY]
  exact hN₀ N hN L ⌊Y⌋₊ hcrit ((Nat.floor_le hY).trans hYband) G hG V hV T hT

theorem two_kernel_power_upper (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (a K D E C θ ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, 0 ≤ Y → Y ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ K * N) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * (L + 1)) →
      ((realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (max θ (7 / 12) + ε) := by
  obtain ⟨Nb, hb⟩ := two_kernel_real_cutoff hHB hNG a K D E C (ε / 2) ha hD hE (by positivity)
  obtain ⟨Nk, hk⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow 2 0 (ε / 2) (by positivity)
  refine ⟨max 2 (max Nb Nk), ?_⟩
  intro N hN L hcrit Y hY hYband G hG V hV
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hθ : (N : ℝ) ^ θ ≤ (N : ℝ) ^ (max θ (7 / 12)) := Real.rpow_le_rpow_of_exponent_le hn₁ (le_max_left _ _)
  have hbase : (N : ℝ) ^ (7 / 12 : ℝ) ≤ (N : ℝ) ^ (max θ (7 / 12)) := Real.rpow_le_rpow_of_exponent_le hn₁ (le_max_right _ _)
  have htwo : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by simpa only [Real.rpow_zero, mul_one] using hk N (by omega)
  have hsum : (N : ℝ) ^ θ + (N : ℝ) ^ (7 / 12 : ℝ) ≤ (N : ℝ) ^ (max θ (7 / 12)) * (N : ℝ) ^ (ε / 2) := by
    have hm := mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hn.le (max θ (7 / 12)))
    linarith only [hθ, hbase, hm]
  calc
    _ ≤ ((N : ℝ) ^ θ + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ (ε / 2) :=
      hb N (by omega) L hcrit Y hY hYband G hG V hV _ (by positivity)
    _ ≤ ((N : ℝ) ^ (max θ (7 / 12)) * (N : ℝ) ^ (ε / 2)) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hn, add_halves, ← Real.rpow_add hn]

theorem critical_band_counts (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (a K D E C θ ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, 0 ≤ Y → Y ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ K * N) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * (L + 1)) →
      (∀ T : ℝ, 0 ≤ T → ((FixedWidthSmallKernel.realSelectedStarts G V Y T).card : ℝ) ≤
        (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T) ∧
      ((realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (max θ (7 / 12) + ε) ∧
      (7 / 12 ≤ θ → ((realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (θ + ε)) := by
  obtain ⟨No, ho⟩ := FixedWidthSmallKernel.one_kernel_real_cutoff K D E C ε hD hE hε
  obtain ⟨Nt, ht⟩ := two_kernel_power_upper hHB hNG a K D E C θ ε ha hD hE hε
  refine ⟨max No Nt, ?_⟩
  intro N hN L hcrit Y hY hYband G hG V hV
  have htwo := ht N (by omega) L hcrit Y hY hYband G hG V hV
  refine ⟨?_, htwo, ?_⟩
  · intro T hT
    exact ho N (by omega) L hcrit Y hY hYband G (fun x hx ↦ (hG x hx).2) V hV T hT
  · intro hθ
    simpa only [max_eq_left hθ] using htwo

theorem companion_T1_13 (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (a K D E θ ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y : ℝ, 0 ≤ Y → Y ≤ E * Real.log N →
      ∀ G : Finset ℤ, (∀ x ∈ G, a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ K * N) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * Real.log N) →
      (∀ T : ℝ, 0 ≤ T → ((FixedWidthSmallKernel.realSelectedStarts G V Y T).card : ℝ) ≤
        (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T) ∧
      ((realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (max θ (7 / 12) + ε) ∧
      (7 / 12 ≤ θ → ((realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (θ + ε)) := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨N₀, hN₀⟩ := critical_band_counts hHB hNG a K (D * Real.log 2) (E * Real.log 2) 1 θ ε
    ha (mul_nonneg hD hlogtwo.le) (mul_nonneg hE hlogtwo.le) hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN Y hY hYlog G hG V hV
  let r := Real.log (N : ℝ) / Real.log 2
  let L := ⌊r⌋₊
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hlogtwo.le
  have hlo : (L : ℝ) ≤ r := Nat.floor_le hr
  have hhi : r < (L : ℝ) + 1 := Nat.lt_floor_add_one r
  have hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith only [hhi], by linarith only [hlo]⟩
  have hlogN : Real.log (N : ℝ) ≤ Real.log 2 * ((L + 1 : ℕ) : ℝ) := by
    have hh : Real.log N < ((L : ℝ) + 1) * Real.log 2 := (div_lt_iff₀ hlogtwo).mp hhi
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hh.le
  have hYband : Y ≤ (E * Real.log 2) * (L + 1) := by
    have hh := mul_le_mul_of_nonneg_left hlogN hE
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hYlog.trans hh
  have hV' : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧
      ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ (D * Real.log 2) * (L + 1) := by
    intro x hx n hn
    obtain ⟨hpos, habs⟩ := hV x hx n hn
    have hh := mul_le_mul_of_nonneg_left hlogN hD
    exact ⟨hpos, by simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using habs.trans hh⟩
  exact hN₀ N (by omega) L hcrit Y hY hYband G hG V hV'

end PaperP1.FixedWidthTwoSmallKernel
