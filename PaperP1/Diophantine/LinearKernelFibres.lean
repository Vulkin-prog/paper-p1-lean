module

public import PaperP1.Arithmetic.SplitOffsetSupports
public import PaperP1.Diophantine.UniformQuadraticCount

/-! # Two actual linear kernels have uniformly small quadratic fibres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearKernelFibres

open Finset PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate PaperP1.LargeOddKernel

def value (n : ℕ) (a : ℤ) : ℕ := ((n : ℤ) + a).natAbs
def linearKernel (n : ℕ) (a : ℤ) : ℕ := squarefreeKernel (value n a)
def squarePart (n : ℕ) (a : ℤ) : ℕ := canonicalSquarePart (value n a)
def embed (a b : ℤ) (n : ℕ) : ℤ × ℤ := (squarePart n b, squarePart n a)

theorem offset_bounds (N n W : ℕ) (a : ℤ) (hN : 2 ≤ N) (hW : 2 * W ≤ N)
    (hnlo : N ≤ n) (hnhi : n ≤ 2 * N) (ha : a.natAbs ≤ W) :
    0 < (n : ℤ) + a ∧ value n a ≤ 3 * N := by
  have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hal := (abs_le.mp habs).1
  have hWn : (W : ℤ) < n := by exact_mod_cast (show W < n by omega)
  have htri := Int.natAbs_add_le (n : ℤ) a
  rw [Int.natAbs_natCast] at htri
  exact ⟨by omega, by dsimp [value]; omega⟩

theorem linearKernel_pos (n : ℕ) (a : ℤ) : 0 < linearKernel n a := by
  apply prod_pos
  intro p hp
  exact (prime_of_mem_oddPrimeSupport hp).pos

theorem representation (n : ℕ) (a : ℤ) (hpos : 0 < (n : ℤ) + a) :
    linearKernel n a * squarePart n a ^ 2 = value n a := by
  apply squarefreeKernel_mul_squarePart
  exact Int.natAbs_ne_zero.mpr hpos.ne'

theorem squarePart_pos (n : ℕ) (a : ℤ) (hpos : 0 < (n : ℤ) + a) : 0 < squarePart n a := by
  have hr := representation n a hpos
  have hv : 0 < value n a := Int.natAbs_pos.mpr hpos.ne'
  by_contra hnot
  have hz : squarePart n a = 0 := by omega
  rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hr
  omega

theorem kernel_part_le_value (n : ℕ) (a : ℤ) (hpos : 0 < (n : ℤ) + a) :
    linearKernel n a ≤ value n a ∧ squarePart n a ≤ value n a := by
  have hr := representation n a hpos
  have hk := linearKernel_pos n a
  have hs := squarePart_pos n a hpos
  constructor
  · calc
      _ = linearKernel n a * 1 := (mul_one _).symm
      _ ≤ linearKernel n a * squarePart n a ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith : 1 ≤ squarePart n a ^ 2)
      _ = _ := hr
  · calc
      _ ≤ squarePart n a ^ 2 := by nlinarith
      _ = 1 * squarePart n a ^ 2 := (one_mul _).symm
      _ ≤ linearKernel n a * squarePart n a ^ 2 :=
        Nat.mul_le_mul_right _ (by omega : 1 ≤ linearKernel n a)
      _ = _ := hr

theorem integer_representation (n : ℕ) (a : ℤ) (hpos : 0 < (n : ℤ) + a) :
    (linearKernel n a : ℤ) * (squarePart n a : ℤ) ^ 2 = (n : ℤ) + a := by
  have hr : (linearKernel n a : ℤ) * (squarePart n a : ℤ) ^ 2 = (value n a : ℤ) := by
    exact_mod_cast representation n a hpos
  have hv : (value n a : ℤ) = (n : ℤ) + a := by
    unfold value
    rw [← Int.abs_eq_natAbs, abs_of_pos hpos]
  rwa [hv] at hr

theorem embed_injective_at (a b : ℤ) (n m v : ℕ)
    (hnb : 0 < (n : ℤ) + b) (hmb : 0 < (m : ℤ) + b)
    (hnv : linearKernel n b = v) (hmv : linearKernel m b = v)
    (heq : embed a b n = embed a b m) : n = m := by
  have hs := congrArg Prod.fst heq
  change (squarePart n b : ℤ) = (squarePart m b : ℤ) at hs
  have hn := integer_representation n b hnb
  have hm := integer_representation m b hmb
  rw [hnv, hs] at hn
  rw [hmv] at hm
  have hnm : (n : ℤ) = (m : ℤ) := by linarith
  exact_mod_cast hnm

theorem embed_equation (a b : ℤ) (n : ℕ) (hna : 0 < (n : ℤ) + a) (hnb : 0 < (n : ℤ) + b) :
    PaperP1.PellInput.pellEquation (linearKernel n b) (linearKernel n a) (b - a) (embed a b n) := by
  have ha := integer_representation n a hna
  have hb := integer_representation n b hnb
  unfold PaperP1.PellInput.pellEquation embed
  linear_combination hb - ha

theorem height_budget (N : ℕ) (hN : 2 ≤ N) : 3 * N ≤ N ^ 3 := by
  have hsq : 3 ≤ N ^ 2 := by nlinarith
  calc
    _ ≤ N ^ 2 * N := Nat.mul_le_mul_right _ hsq
    _ = _ := by ring

theorem fixed_linear_kernels_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W u v : ℕ, ∀ a b : ℤ,
      2 * W ≤ N → a.natAbs ≤ W → b.natAbs ≤ W → a ≠ b → ∀ S : Finset ℕ,
      (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ linearKernel n a = u ∧ linearKernel n b = v) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nq, hNq⟩ := PaperP1.UniformQuadraticCount.positive_count_le_rpow_eventually 3 ε hε
  refine ⟨max 2 Nq, ?_⟩
  intro N hN W u v a b hW ha hb hab S hS
  have hNtwo : 2 ≤ N := by omega
  have hheight := height_budget N hNtwo
  have hapos : ∀ n ∈ S, 0 < (n : ℤ) + a ∧ value n a ≤ 3 * N := by
    intro n hn
    exact offset_bounds N n W a hNtwo hW (hS n hn).1 (hS n hn).2.1 ha
  have hbpos : ∀ n ∈ S, 0 < (n : ℤ) + b ∧ value n b ≤ 3 * N := by
    intro n hn
    exact offset_bounds N n W b hNtwo hW (hS n hn).1 (hS n hn).2.1 hb
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    have hu : 0 < u := by rw [← (hS n₀ hn₀).2.2.1]; exact linearKernel_pos n₀ a
    have hv : 0 < v := by rw [← (hS n₀ hn₀).2.2.2]; exact linearKernel_pos n₀ b
    have huheight : u ≤ N ^ 3 := by
      rw [← (hS n₀ hn₀).2.2.1]
      exact ((kernel_part_le_value n₀ a (hapos n₀ hn₀).1).1.trans (hapos n₀ hn₀).2).trans hheight
    have hvheight : v ≤ N ^ 3 := by
      rw [← (hS n₀ hn₀).2.2.2]
      exact ((kernel_part_le_value n₀ b (hbpos n₀ hn₀).1).1.trans (hbpos n₀ hn₀).2).trans hheight
    have hshift : (b - a).natAbs ≤ N ^ 3 := by
      have htri := Int.natAbs_sub_le b a
      omega
    have hinj : Set.InjOn (embed a b) S := by
      intro n hn m hm heq
      exact embed_injective_at a b n m v (hbpos n hn).1 (hbpos m hm).1
        (hS n hn).2.2.2 (hS m hm).2.2.2 heq
    rw [← card_image_of_injOn hinj]
    apply hNq N (by omega) v u (N ^ 3) (b - a) hv hu (sub_ne_zero.mpr hab.symm)
      hvheight huheight le_rfl hshift
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    have hna := (hapos n hn).1
    have hnb := (hbpos n hn).1
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · have heq := embed_equation a b n hna hnb
      rwa [(hS n hn).2.2.1, (hS n hn).2.2.2] at heq
    · change (squarePart n b : ℤ).natAbs ≤ N ^ 3
      simpa only [Int.natAbs_natCast] using
        ((kernel_part_le_value n b hnb).2.trans (hbpos n hn).2).trans hheight
    · change (squarePart n a : ℤ).natAbs ≤ N ^ 3
      simpa only [Int.natAbs_natCast] using
        ((kernel_part_le_value n a hna).2.trans (hapos n hn).2).trans hheight
    · change (0 : ℤ) < (squarePart n b : ℕ)
      exact_mod_cast squarePart_pos n b hnb
    · change (0 : ℤ) < (squarePart n a : ℕ)
      exact_mod_cast squarePart_pos n a hna
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

end PaperP1.LinearKernelFibres
