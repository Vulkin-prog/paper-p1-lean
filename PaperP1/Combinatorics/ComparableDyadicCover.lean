module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-! # A finite dyadic cover of every fixed comparable positive range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableDyadicCover

open Finset

def indices (C : ℕ) : Finset ℕ := range (Nat.log2 (2 * C ^ 2) + 1)
def base (C N j : ℕ) : ℕ := (N / C) * 2 ^ j
def distortion (C : ℕ) : ℕ := 2 * C ^ 2 + 2 * C + 1

theorem distortion_ge_one (C : ℕ) : 1 ≤ distortion C := by unfold distortion; omega

theorem floor_pos (C N : ℕ) (hC : 1 ≤ C) (hN : 2 * C ≤ N) : 0 < N / C :=
  Nat.div_pos (by omega) (by omega)

theorem floor_comparison (C N : ℕ) (hC : 1 ≤ C) (hN : 2 * C ≤ N) :
    N ≤ 2 * C * (N / C) := by
  have hb := floor_pos C N hC hN
  have hrem := Nat.mod_lt N (by omega : 0 < C)
  have hdiv := Nat.div_add_mod N C
  have hCB : C ≤ C * (N / C) := by
    simpa only [mul_one] using Nat.mul_le_mul_left C (show 1 ≤ N / C by omega)
  nlinarith only [hrem, hdiv, hCB]

theorem index_power_le (C j : ℕ) (hC : 1 ≤ C) (hj : j ∈ indices C) : 2 ^ j ≤ 2 * C ^ 2 := by
  have hjle : j ≤ Nat.log2 (2 * C ^ 2) := by have h := mem_range.mp hj; omega
  have hp : 0 < 2 * C ^ 2 := by positivity
  exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hjle).trans (Nat.log2_self_le hp.ne')

theorem base_comparison (C N j : ℕ) (hC : 1 ≤ C) (hN : 2 * C ≤ N) (hj : j ∈ indices C) :
    N ≤ distortion C * base C N j ∧ base C N j ≤ distortion C * N := by
  have hfloor := floor_comparison C N hC hN
  have hb : N / C ≤ base C N j := by
    unfold base
    have hp : 0 < 2 ^ j := by positivity
    simpa only [mul_one] using Nat.mul_le_mul_left (N / C) (show 1 ≤ 2 ^ j by omega)
  constructor
  · calc
      N ≤ 2 * C * (N / C) := hfloor
      _ ≤ 2 * C * base C N j := Nat.mul_le_mul_left _ hb
      _ ≤ _ := Nat.mul_le_mul_right _ (by unfold distortion; omega)
  · calc
      base C N j ≤ N * (2 * C ^ 2) := Nat.mul_le_mul (Nat.div_le_self N C) (index_power_le C j hC hj)
      _ = (2 * C ^ 2) * N := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by unfold distortion; omega)

theorem cover (C N n : ℕ) (hC : 1 ≤ C) (hN : 2 * C ≤ N)
    (hlo : N ≤ C * n) (hhi : n ≤ C * N) :
    ∃ j ∈ indices C, base C N j ≤ n ∧ n ≤ 2 * base C N j := by
  have hCp : 0 < C := by omega
  let B := N / C
  have hBp : 0 < B := floor_pos C N hC hN
  have hBn : B ≤ n := by
    have hquot : N / C ≤ (C * n) / C := Nat.div_le_div_right hlo
    simpa only [Nat.mul_div_right n hCp] using hquot
  let q := n / B
  have hqp : 0 < q := Nat.div_pos hBn hBp
  let j := Nat.log2 q
  have hpowlo : 2 ^ j ≤ q := Nat.log2_self_le hqp.ne'
  have hpowhi : q < 2 * 2 ^ j := by
    simpa only [Nat.pow_succ, Nat.mul_comm] using (Nat.lt_log2_self (n := q))
  have hNbase : N ≤ 2 * C * B := floor_comparison C N hC hN
  have hnBound : n ≤ (2 * C ^ 2) * B := by
    calc
      n ≤ C * N := hhi
      _ ≤ C * (2 * C * B) := Nat.mul_le_mul_left _ hNbase
      _ = _ := by ring
  have hqBound : q ≤ 2 * C ^ 2 :=
    Nat.le_of_mul_le_mul_right ((Nat.div_mul_le_self n B).trans hnBound) hBp
  have hp : 0 < 2 * C ^ 2 := by positivity
  have hj : j ∈ indices C := by
    apply mem_range.mpr
    have hle := (Nat.le_log2 hp.ne').mpr (hpowlo.trans hqBound)
    omega
  refine ⟨j, hj, ?_, ?_⟩
  · calc
      base C N j = B * 2 ^ j := rfl
      _ ≤ B * q := Nat.mul_le_mul_left B hpowlo
      _ = q * B := by ring
      _ ≤ n := Nat.div_mul_le_self n B
  · have hdiv := Nat.div_add_mod n B
    change B * q + n % B = n at hdiv
    have hrem := Nat.mod_lt n hBp
    have hmul := Nat.mul_le_mul_left B (show q + 1 ≤ 2 * 2 ^ j by omega)
    change n ≤ 2 * (B * 2 ^ j)
    nlinarith only [hdiv, hrem, hmul]

theorem base_large (C N j M₀ : ℕ) (hC : 1 ≤ C) (hN : 2 * C ≤ N) (hj : j ∈ indices C)
    (hlarge : distortion C * M₀ ≤ N) : M₀ ≤ base C N j :=
  Nat.le_of_mul_le_mul_left (hlarge.trans (base_comparison C N j hC hN hj).1)
    (by have h := distortion_ge_one C; omega)

end PaperP1.ComparableDyadicCover
