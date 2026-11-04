module

public import PaperP1.Arithmetic.SmallMotifCoefficients
public import PaperP1.Asymptotics.SourceSupportedCoefficientCount

/-! # The common fixed-third-window coefficient list has subpower size and polynomial height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallMotifCoefficientBounds

open Finset PaperP1.Model PaperP1.SmallMotifCoefficients PaperP1.CriticalBandScale

theorem uniform_pool (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ z ∈ dyadicBlock N, ((pool z L H).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, h⟩ := SourceSupportedCoefficientCount.uniform_count 1 5 D C ε
    (Nat.cast_nonneg D) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband hH z hz
  exact h N hN L H hband (by exact_mod_cast hH) (fun _ ↦ z) (fun _ ↦ hz)

theorem uniform_height (C : ℝ) (D : ℕ) :
    ∃ A₀ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ z ∈ dyadicBlock N, ∀ d ∈ pool z L H, 0 < d ∧ (d : ℝ) ≤ (N : ℝ) ^ (A₀ : ℝ) := by
  let K := ⌈((D : ℝ) * upperScale) * Real.log 4⌉₊
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨K + 10, max 3 NG, by omega, ?_⟩
  intro N hN L H hband hH z hz d hd
  have hgeom := hg N (by omega) L hband
  have hLN : L ≤ N := by have hh := hgeom.2.2.2.1; omega
  have hHlog : (H : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hHR : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hH
    have hh := mul_le_mul_of_nonneg_left hgeom.2.2.2.2.2 (Nat.cast_nonneg D)
    simpa only [mul_assoc] using hHR.trans hh
  have hprime : primorial H ≤ N ^ K := primorial_le_four_pow H |>.trans
    (SmoothSupportBounds.four_pow_cutoff_le_polynomial (by omega) hHlog (Nat.le_ceil _))
  have hpos : 0 < d := SourceSupportedCoefficientPool.pool_pos _ H 5 hd
  refine ⟨hpos, ?_⟩
  obtain ⟨A, hA, hdA⟩ := mem_biUnion.mp hd
  obtain ⟨ab, hab, rfl⟩ := mem_image.mp hdA
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  let v := FixedSourceCertificate.sourceValues (fun _ : Fin 1 ↦ z) (L + 1)
  have hAc : A.card ≤ 5 := (SourceSupportedCoefficientPool.mem_positions 5 A).mp hA
  have hp : 0 < A.prod v := prod_pos (fun i _ ↦
    FixedSourceCertificate.sourceValues_pos (fun _ : Fin 1 ↦ z) (by omega) (fun _ ↦ hz) i)
  have hprod : A.prod v ≤ N ^ 10 := by
    calc
      _ ≤ ∏ _i ∈ A, N ^ 2 := prod_le_prod (fun i _ ↦
        FixedSourceCertificate.sourceValues_le_square (fun _ : Fin 1 ↦ z) (by omega) hLN (fun _ ↦ hz) i)
      _ = N ^ (2 * A.card) := by rw [prod_const, ← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < N) (by omega)
  have hn : ab.1 * ab.2 ≤ N ^ (K + 10) := by
    calc
      _ ≤ primorial H * A.prod v := Nat.mul_le_mul
        (Nat.le_of_dvd (primorial_pos H) (Nat.mem_divisors.mp ha).1)
        (Nat.le_of_dvd hp (Nat.mem_divisors.mp hb).1)
      _ ≤ N ^ K * N ^ 10 := Nat.mul_le_mul hprime hprod
      _ = _ := (pow_add N K 10).symm
  rw [Real.rpow_natCast]
  exact_mod_cast hn

end PaperP1.SmallMotifCoefficientBounds
