module

public import PaperP1.Arithmetic.SmoothModulusHosts
public import Mathlib.Data.Nat.Dist

/-! # Positive nearby actual offset values and gcd bounds for arbitrary assigned divisors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetValueGeometry

open Finset PaperP1.LinearKernelFibres PaperP1.SmoothModulusHosts

theorem value_pos {n W : ℕ} {a : ℤ} (hn : W < n) (ha : a.natAbs ≤ W) : 0 < value n a := by
  have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hnZ : (W : ℤ) < n := by exact_mod_cast hn
  have hcast := value_cast n W a hn ha
  have hp : (0 : ℤ) < value n a := by rw [hcast]; omega
  exact_mod_cast hp

theorem value_ne {n W : ℕ} {a b : ℤ} (hn : W < n)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) (hab : a ≠ b) : value n a ≠ value n b := by
  intro heq
  have hcast := congrArg (fun t : ℕ ↦ (t : ℤ)) heq
  rw [value_cast n W a hn ha, value_cast n W b hn hb] at hcast
  exact hab (by omega)

theorem value_dist {n W : ℕ} {a b : ℤ} (hn : W < n)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) : Nat.dist (value n a) (value n b) ≤ 2 * W := by
  have hva := value_cast n W a hn ha
  have hvb := value_cast n W b hn hb
  have haa : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hbb : |b| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have hal := abs_le.mp haa
  have hbl := abs_le.mp hbb
  rcases le_total (value n a) (value n b) with h | h
  · rw [Nat.dist_eq_sub_of_le h]; omega
  · rw [Nat.dist_eq_sub_of_le_right h]; omega

theorem gcd_divisors_le {n W d e : ℕ} {a b : ℤ} (hn : W < n)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) (hab : a ≠ b)
    (hd : d ∣ value n a) (he : e ∣ value n b) : Nat.gcd d e ≤ 2 * W := by
  have hdv := (Nat.gcd_dvd_left d e).trans hd
  have hev := (Nat.gcd_dvd_right d e).trans he
  have hdiv : Nat.gcd d e ∣ Nat.dist (value n a) (value n b) := by
    rcases le_total (value n a) (value n b) with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      exact Nat.dvd_sub hev hdv
    · rw [Nat.dist_eq_sub_of_le_right h]
      exact Nat.dvd_sub hdv hev
  exact (Nat.le_of_dvd (Nat.dist_pos_of_ne (value_ne hn ha hb hab)) hdiv).trans (value_dist hn ha hb)

end PaperP1.OffsetValueGeometry
