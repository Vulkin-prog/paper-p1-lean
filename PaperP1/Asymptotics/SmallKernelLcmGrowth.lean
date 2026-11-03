module

public import PaperP1.Arithmetic.CutoffSquareParts
public import PaperP1.Arithmetic.OffsetValueGeometry
public import PaperP1.Arithmetic.GcdLcmProductBound
public import PaperP1.Asymptotics.SmoothSelectionCertificates

/-! # Several actual small kernels force a cutoff quotient lcm beyond every fixed scale multiple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelLcmGrowth

open Finset PaperP1.LinearKernelFibres PaperP1.CutoffSquareParts PaperP1.LargeOddKernel

theorem product_budget (m : ℕ) (β C E A₀ : ℝ) (hC : 0 ≤ C)
    (hgap : 1 < (m : ℝ) * (1 - β)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ W : ℕ, 0 < W →
      (W : ℝ) ≤ E * (Real.log N) ^ A₀ →
      C * N * (2 * W : ℝ) ^ (m ^ 2) < ((1 / 4 : ℝ) * (N : ℝ) ^ (1 - β)) ^ m := by
  let δ := (m : ℝ) * (1 - β) - 1
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hgap]
  let α := (1 / 4 : ℝ)
  have hα : 0 < α := by norm_num [α]
  let K := (C + 1) * (2 * E) ^ (m ^ 2) / α ^ m
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow K (A₀ * (m ^ 2 : ℕ)) δ hδ
  refine ⟨max 2 NP, by omega, ?_⟩
  intro N hN W hW hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hw : (2 * W : ℝ) ≤ 2 * E * (Real.log N) ^ A₀ := by nlinarith only [hwidth]
  have hwpow : (2 * W : ℝ) ^ (m ^ 2) ≤ (2 * E) ^ (m ^ 2) * (Real.log N) ^ (A₀ * (m ^ 2 : ℕ)) := by
    calc
      _ ≤ (2 * E * (Real.log N) ^ A₀) ^ (m ^ 2) := pow_le_pow_left₀ (by positivity) hw _
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hl.le]
  have hpenalty : (C + 1) * (2 * W : ℝ) ^ (m ^ 2) ≤ α ^ m * (N : ℝ) ^ δ := by
    calc
      _ ≤ (C + 1) * ((2 * E) ^ (m ^ 2) * (Real.log N) ^ (A₀ * (m ^ 2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hwpow (by linarith only [hC])
      _ = α ^ m * (K * (Real.log N) ^ (A₀ * (m ^ 2 : ℕ))) := by dsimp [K]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hp N (by omega)) (by positivity)
  have hwp : 0 < (2 * W : ℝ) ^ (m ^ 2) := by positivity
  calc
    _ < (C + 1) * N * (2 * W : ℝ) ^ (m ^ 2) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (lt_add_one C) hn) hwp
    _ ≤ (N : ℝ) * (α ^ m * (N : ℝ) ^ δ) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hpenalty hn.le
    _ = α ^ m * (N : ℝ) ^ (1 + δ) := by
      rw [Real.rpow_add hn 1 δ, Real.rpow_one]
      ring
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hn.le]
      congr 1
      dsimp [δ]
      ring

theorem uniform_large_lcm (m : ℕ) (β C E A₀ : ℝ) (hC : 0 ≤ C)
    (hgap : 1 < (m : ℝ) * (1 - β)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Y W n : ℕ, ∀ a : Fin m → ℤ,
      0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ → N ≤ n → n ≤ 2 * N →
      (∀ i, (a i).natAbs ≤ W) → Function.Injective a →
      (∀ i, (largeOddKernel Y (value n (a i)) : ℝ) ≤ (N : ℝ) ^ β) →
      W < n ∧ C * N < ((univ.lcm fun i ↦ quotient Y (value n (a i)) : ℕ) : ℝ) := by
  obtain ⟨NP, _hNP, hp⟩ := product_budget m β C E A₀ hC hgap
  obtain ⟨NW, hw⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (4 * E) A₀ 1 (by norm_num)
  refine ⟨max 2 (max NP NW), by omega, ?_⟩
  intro N hN Y W n a hW hwidth hnlo hnhi ha hinj hk
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWNr : 4 * (W : ℝ) ≤ N := by
    have h := hw N (by omega)
    rw [Real.rpow_one] at h
    nlinarith only [hwidth, h]
  have hWN : 2 * 2 * W ≤ N := by exact_mod_cast hWNr
  have hv := fun i ↦ SmoothSelectionCertificates.value_bounds 2 N n W (a i) (by decide) (by omega)
    hWN (by omega) hnhi (ha i)
  have hWn : W < n := by omega
  let q : Fin m → ℕ := fun i ↦ quotient Y (value n (a i))
  have hqi : ∀ i, (1 / 4 : ℝ) * (N : ℝ) ^ (1 - β) ≤ (q i : ℝ) := by
    intro i
    have hrep : (q i : ℝ) * (largeOddKernel Y (value n (a i)) : ℝ) = value n (a i) := by
      exact_mod_cast quotient_mul_kernel Y (value n (a i)) (hv i).2.1
    have hlo : (1 / 4 : ℝ) * N ≤ value n (a i) := by
      convert (hv i).2.2.1 using 1; norm_num [SmoothSelectionCertificates.lowerConstant]
    have hmul := mul_le_mul_of_nonneg_left (hk i) (Nat.cast_nonneg (q i))
    have hid : ((1 / 4 : ℝ) * (N : ℝ) ^ (1 - β)) * (N : ℝ) ^ β = (1 / 4 : ℝ) * N := by
      rw [mul_assoc, ← Real.rpow_add hn]
      simp only [sub_add_cancel, Real.rpow_one]
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn β)).mp
    rw [hid]
    linarith only [hrep, hlo, hmul]
  have hprod : ((1 / 4 : ℝ) * (N : ℝ) ^ (1 - β)) ^ m ≤ ∏ i, (q i : ℝ) := by
    simpa only [prod_const, card_univ, Fintype.card_fin] using
      (prod_le_prod₀ (fun _i _ ↦ by positivity : ∀ i ∈ (univ : Finset (Fin m)), 0 ≤ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - β))
        (fun i _ ↦ hqi i))
  have hfinite := GcdLcmProductBound.product_le_lcm_mul_bound univ q (2 * W) (by omega)
    (fun i _ ↦ quotient_pos Y (value n (a i))) (by
      intro i _ j _ hij
      exact OffsetValueGeometry.gcd_divisors_le hWn (ha i) (ha j) (fun h ↦ hij (hinj h))
        (quotient_dvd Y (value n (a i)) (hv i).2.1) (quotient_dvd Y (value n (a j)) (hv j).2.1))
  have hcast : (∏ i, (q i : ℝ)) ≤ ((univ.lcm q : ℕ) : ℝ) * (2 * W : ℝ) ^ (m ^ 2) := by
    exact_mod_cast (by simpa only [card_univ, Fintype.card_fin] using hfinite)
  refine ⟨hWn, ?_⟩
  by_contra hnot
  have hle : ((univ.lcm q : ℕ) : ℝ) ≤ C * N := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ (2 * W : ℝ) ^ (m ^ 2))
  have hbudget := hp N (by omega) W hW hwidth
  exact (not_lt_of_ge (hprod.trans (hcast.trans hmul))) hbudget

end PaperP1.SmallKernelLcmGrowth
