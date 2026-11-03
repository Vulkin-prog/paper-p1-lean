module

public import PaperP1.Arithmetic.SmallKernelWindowSets
public import PaperP1.Asymptotics.SeveralSmallKernelCount
public import PaperP1.Asymptotics.TwoSmallKernelCount
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Both clauses of article Lemma 15.4 for the literal complete dyadic windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelWindows

open Finset PaperP1.SmallKernelWindowSets PaperP1.NormalizedWindowSets PaperP1.LargeOddKernel
  PaperP1.CutoffSquareParts PaperP1.LinearKernelFibres PaperP1.Model PaperP1.CriticalBandScale

theorem dyadic_several_count (m : ℕ) (A β u E A₀ ε : ℝ) (hA : 2 ≤ A) (hu : u ≤ 1)
    (hgap : 1 < (m : ℝ) * (1 - β)) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L Y : ℕ,
      (Y : ℝ) ≤ (Real.log N) ^ A → 2 * (L + 1) ≤ Y →
      ((L + 1 : ℕ) : ℝ) ≤ E * (Real.log N) ^ A₀ →
      ((severalWindows N L Y m β u).card : ℝ) ≤
        (N : ℝ) ^ (max (1 - 1 / A) ((1 + u) / 2) + ε) := by
  obtain ⟨N₀, hN₀, hc⟩ := SeveralSmallKernelCount.uniform_count m A β u E A₀ ε hA hu hgap hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L Y hY hcut hwidth
  apply hc N hN Y (L + 1) hY (by omega) hcut hwidth
  intro x hx
  obtain ⟨hxD, hxcard⟩ := mem_filter.mp hx
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hxD
  have hxp : 0 < x := by omega
  obtain ⟨v, hvinj, hv⟩ := select_values hxcard
  let a : Fin m → ℤ := fun i ↦ (v i : ℤ) - x
  have hvalues : ∀ i, v i ∈ values x L := fun i ↦ (mem_filter.mp (hv i)).1
  have hoff := fun i ↦ value_offset hxp (hvalues i)
  have hvalue : ∀ i, value x (a i) = v i := fun i ↦ (hoff i).2
  refine ⟨hxlo, hxhi.le, a, fun i ↦ (hoff i).1, ?_, ?_, ?_⟩
  · intro i j heq
    apply hvinj
    dsimp [a] at heq
    omega
  · intro i
    rw [hvalue]
    exact (mem_filter.mp (hv i)).2.1
  · intro i
    rw [hvalue]
    exact (mem_filter.mp (hv i)).2.2

theorem critical_several_count (m : ℕ) (A β u C ε : ℝ) (hA : 2 ≤ A) (hu : u ≤ 1)
    (hgap : 1 < (m : ℝ) * (1 - β)) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((severalWindows N L ⌊(Real.log N) ^ A⌋₊ m β u).card : ℝ) ≤
        (N : ℝ) ^ (max (1 - 1 / A) ((1 + u) / 2) + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := dyadic_several_count m A β u upperScale 1 ε hA hu hgap hε
  obtain ⟨NB, hb⟩ := critical_band_scale C
  obtain ⟨NL, hl⟩ := ElementaryLogGrowth.log_ge_eventually (max 1 (2 * upperScale))
  refine ⟨max NC (max NB NL), ?_⟩
  intro N hN L hband
  have hB := (hb N (by omega) L hband).2
  have hlog := (hl N (by omega)).1
  have hl1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hlE : 2 * upperScale ≤ Real.log N := (le_max_right _ _).trans hlog
  have hcut : 2 * (L + 1) ≤ ⌊(Real.log N) ^ A⌋₊ := by
    apply Nat.le_floor
    calc
      ((2 * (L + 1) : ℕ) : ℝ) ≤ 2 * upperScale * Real.log N := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ (Real.log N) ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hlE (by linarith only [hl1])]
      _ ≤ _ := by simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hl1 hA
  exact hc N (by omega) L ⌊(Real.log N) ^ A⌋₊ (Nat.floor_le (by positivity)) hcut
    (by simpa only [Real.rpow_one] using hB)

theorem critical_two_count (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ, ∀ q : ℝ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ((twoWindows N L H q).card : ℝ) ≤ (N : ℝ) ^ (q + ε) := by
  obtain ⟨N₀, hc⟩ := TwoSmallKernelCount.critical_block_count 1 2 D 1 C ε
    (by norm_num) hD (by norm_num) hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN L H q hband hH
  apply (hc N (by omega) L H (L + 1) q hband hH (by omega) (by simp)
    (twoWindows N L H q) ?_).2
  intro x hx
  obtain ⟨hxD, v, hv, w, hw, hvw, hprod⟩ := mem_filter.mp hx
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hxD
  have hxp : 0 < x := by omega
  obtain ⟨ha, hva⟩ := value_offset hxp hv
  obtain ⟨hb, hwb⟩ := value_offset hxp hw
  refine ⟨?_, ?_, (v : ℤ) - x, (w : ℤ) - x, ha, hb, ?_, ?_⟩
  · simpa only [one_mul] using (show (N : ℝ) ≤ x by exact_mod_cast hxlo)
  · exact_mod_cast hxhi.le
  · intro heq
    apply hvw
    omega
  · simpa only [TwoSmallKernelFibres.largeKernel, hva, hwb] using hprod

/-- Both source clauses share one threshold before every critical length, cutoff and product cap. -/
theorem article_15_4 (m : ℕ) (A β u D C ε : ℝ) (hA : 2 ≤ A) (hu : u ≤ 1)
    (hgap : 1 < (m : ℝ) * (1 - β)) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ, ∀ q : ℝ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ((severalWindows N L ⌊(Real.log N) ^ A⌋₊ m β u).card : ℝ) ≤
        (N : ℝ) ^ (max (1 - 1 / A) ((1 + u) / 2) + ε) ∧
      ((twoWindows N L H q).card : ℝ) ≤ (N : ℝ) ^ (q + ε) := by
  obtain ⟨NS, hs⟩ := critical_several_count m A β u C ε hA hu hgap hε
  obtain ⟨NT, ht⟩ := critical_two_count D C ε hD hε
  exact ⟨max NS NT, fun N hN L H q hband hH ↦
    ⟨hs N (by omega) L hband, ht N (by omega) L H q hband hH⟩⟩

end PaperP1.SmallKernelWindows
