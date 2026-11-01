module

public import PaperP1.Diophantine.LinearKernelFibres
public import PaperP1.Diophantine.WideQuadraticKernelRanges

/-! # Actual shifted linear values and a quadratic block of the split product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedQuadraticValues

open Finset PaperP1.SplitOffsetProducts PaperP1.LinearKernelFibres

def shift (a b : ℤ) : ℕ := (b - a).natAbs

theorem shift_pos (a b : ℤ) (hab : a < b) : 0 < shift a b :=
  Int.natAbs_pos.mpr (sub_ne_zero.mpr hab.ne.symm)

theorem value_cast (n : ℕ) (a : ℤ) (ha : 0 < (n : ℤ) + a) : (value n a : ℤ) = (n : ℤ) + a := by
  unfold value
  rw [← Int.abs_eq_natAbs, abs_of_pos ha]

theorem shifted_value_add (n : ℕ) (a b : ℤ) (hab : a < b)
    (ha : 0 < (n : ℤ) + a) (hb : 0 < (n : ℤ) + b) : value n a + shift a b = value n b := by
  have hs : (shift a b : ℤ) = b - a := by
    unfold shift
    rw [← Int.abs_eq_natAbs, abs_of_pos (sub_pos.mpr hab)]
  have heq : ((value n a + shift a b : ℕ) : ℤ) = (value n b : ℤ) := by
    push_cast
    rw [value_cast n a ha, value_cast n b hb, hs]
    ring
  exact_mod_cast heq

theorem shifted_bounds (N n W : ℕ) (a b : ℤ) (hN : 2 ≤ N) (hW : 2 * W ≤ N)
    (hnlo : N ≤ n) (hnhi : n ≤ 2 * N) (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) (hab : a < b) :
    N ≤ 2 * value n a ∧ value n a ≤ 3 * N ∧ shift a b ≤ 2 * W ∧
      value n a + shift a b = value n b := by
  obtain ⟨hapos, haheight⟩ := offset_bounds N n W a hN hW hnlo hnhi ha
  obtain ⟨hbpos, _⟩ := offset_bounds N n W b hN hW hnlo hnhi hb
  have hal : -(W : ℤ) ≤ a := by
    have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
    exact (abs_le.mp habs).1
  have hlo : (N : ℤ) ≤ 2 * (value n a : ℤ) := by
    rw [value_cast n a hapos]
    have hnR : (N : ℤ) ≤ n := by exact_mod_cast hnlo
    have hWR : 2 * (W : ℤ) ≤ N := by exact_mod_cast hW
    omega
  have htri := Int.natAbs_sub_le b a
  refine ⟨by exact_mod_cast hlo, haheight, ?_, shifted_value_add n a b hab hapos hbpos⟩
  dsimp [shift]
  omega

theorem quadratic_block_eq (n : ℕ) (a b : ℤ) (hab : a ≠ b)
    (hadd : value n a + shift a b = value n b) :
    kernel ({a, b} : Finset ℤ) n = PaperP1.QuadraticKernelFibres.kernel (shift a b) (value n a) := by
  unfold kernel product PaperP1.QuadraticKernelFibres.kernel
  rw [prod_pair hab]
  change PaperP1.SmallPrimeBudget.squarefreeKernel (value n a * value n b) = _
  rw [← hadd]

theorem value_injective_on (S : Finset ℕ) (a : ℤ) (hS : ∀ n ∈ S, 0 < (n : ℤ) + a) :
    Set.InjOn (fun n ↦ value n a) S := by
  intro n hn m hm heq
  have hi := congrArg (fun k : ℕ ↦ (k : ℤ)) heq
  rw [value_cast n a (hS n hn), value_cast m a (hS m hm)] at hi
  have hnm : (n : ℤ) = m := by linarith
  exact_mod_cast hnm

theorem ordered_pair_representation (B : Finset ℤ) (hB : B.card = 2) :
    ∃ a b : ℤ, a < b ∧ B = {a, b} := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hB
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact ⟨a, b, hlt, rfl⟩
  · exact ⟨b, a, hgt, Finset.pair_comm a b⟩

end PaperP1.ShiftedQuadraticValues
