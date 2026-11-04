module

public import PaperP1.Asymptotics.PrefixOneSeedTail
public import PaperP1.Model.OneSeedWindowParticipation
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # A source centre in a larger fixed multiple of the original dyadic range

The targets retain their original window length and their exact independent
weights. Only their effective spaces are embedded into a common longer window.
The fixed source range and logarithmic width constants precede the threshold.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WideOneSeedTail

open Finset PaperP1.Arithmetic PaperP1.Model

theorem uniform_tail (D Q : ℕ) (hD : 1 ≤ D) (hQ : 2 ≤ Q) (C M a ε : ℝ)
    (hM : 0 ≤ M) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ W : ℕ → Submodule F₂ (ℕ →₀ F₂),
      (∀ x ∈ Ico 2 (Q * N + 2), W x ≤ squareClassSpace x (D * (L + 1))) →
      ∀ p w : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ w x) →
      (∀ x ∈ Ico 2 (Q * N + 2), p x ≤ M / N) →
      (∀ x ∈ Ico 2 (Q * N + 2), w x ≤ M / N) →
      ∀ Families : ℕ → Finset (Finset ℕ),
      (∀ x ∈ Ico 2 (Q * N + 2), ∀ I ∈ Families x,
        I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L (W x) I) →
      (∑ x ∈ Ico 2 (Q * N + 2), w x * ∑ I ∈ Families x, ∏ y ∈ I, p y) ≤ (N : ℝ) ^ (-a + ε) := by
  let D' := max 1 (((D + 1 : ℕ) : ℝ) * CriticalBandScale.upperScale)
  let M' := (Q : ℝ) * M
  obtain ⟨s, hs, NT, _hNT, ht⟩ := PrefixOneSeedTail.uniform_tail D' M' a (ε / 2)
    (le_max_left _ _) (by dsimp [M']; positivity) ha (by positivity)
  obtain ⟨NS, hscl⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((Q : ℝ) ^ (-a + ε / 2))
    (-a + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, max 10 (max NT (max NS (max NG NF))), by omega, ?_⟩
  intro N hN L hband W hW p w hp hw hpcap hwcap Families hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNQ : N ≤ Q * N := by
    simpa only [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ Q by omega)
  have htwoN : 2 * N ≤ Q * N := Nat.mul_le_mul_right N hQ
  have hL : 1 ≤ L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  let H := D * (L + 1)
  have hLH : L ≤ H := by
    have hh := Nat.mul_le_mul_right (L + 1) hD
    dsimp [H]
    omega
  have hH : 1 ≤ H := hL.trans hLH
  have hwidth : ((H + 1 : ℕ) : ℝ) ≤ D' * Real.log (Q * N : ℕ) := by
    have hb := (hscl N (by omega) L hband).2
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hNQr : (N : ℝ) ≤ (Q * N : ℕ) := by exact_mod_cast hNQ
    have hlog := Real.log_le_log hn hNQr
    have hnat : H + 1 ≤ (D + 1) * (L + 1) := by dsimp [H]; nlinarith
    have hcast : ((H + 1 : ℕ) : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (D + 1))
    have hh' := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (Nat.cast_nonneg (D + 1)) CriticalBandScale.upperScale_pos.le)
    have hd := mul_le_mul_of_nonneg_right (le_max_right 1 (((D + 1 : ℕ) : ℝ) * CriticalBandScale.upperScale))
      (hlogN.trans hlog)
    dsimp only [D']
    nlinarith only [hcast, hh, hh', hd]
  have hcapid : M' / (Q * N : ℕ) = M / (N : ℝ) := by
    dsimp only [M']
    rw [Nat.cast_mul]
    have hqr : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    field_simp
  have hfamily : ∀ x ∈ Ico 2 (Q * N + 2), ∀ I ∈ Families x,
      I ⊆ Ico 2 (Q * N + 2) ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses H (W x) I := by
    intro x hx I hI
    obtain ⟨hIG, hsize, hwit⟩ := hF x hx I hI
    refine ⟨?_, hsize, ?_⟩
    · intro y hy
      obtain ⟨hlo, hhi⟩ := mem_Ico.mp (hIG hy)
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · exact OneSeedParticipation.mono (fun y ↦ squareClassSpace y L) (fun y ↦ squareClassSpace y H)
        (W x) (W x) I (fun y hy ↦ EvenWindowEnlargement.window_mono
          (by have hh := (mem_Ico.mp (hIG hy)).1; omega) hLH) le_rfl hwit
  have htail := ht (Q * N) (by omega) H hH hwidth W hW p w hp hw
    (by simpa only [hcapid] using hpcap) (by simpa only [hcapid] using hwcap) Families hfamily
  calc
    _ ≤ ((Q * N : ℕ) : ℝ) ^ (-a + ε / 2 : ℝ) := htail
    _ = (Q : ℝ) ^ (-a + ε / 2) * (N : ℝ) ^ (-a + ε / 2) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    _ ≤ (N : ℝ) ^ (-a + ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.WideOneSeedTail
