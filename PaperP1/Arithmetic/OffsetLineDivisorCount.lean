module

public import PaperP1.Arithmetic.CoprimeDivisorCardinality
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Every collinear offset subfamily has bounded indexed divisor multiplicity

The line is chosen from two actual points, so no bound on a supplied defining
equation is needed. Coincident points are handled by their true common value.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLineDivisorCount

open Finset

theorem canonical_height (x y sp tp sq tq : ℤ) (X B : ℕ)
    (hx : x.natAbs ≤ X) (hy : y.natAbs ≤ X)
    (hsp : sp.natAbs ≤ B) (htp : tp.natAbs ≤ B)
    (hsq : sq.natAbs ≤ B) (htq : tq.natAbs ≤ B) :
    ((tp - tq) * x + (sq - sp) * y + (sq * tp - sp * tq)).natAbs ≤ 4 * B * X + 2 * B ^ 2 := by
  have ha : (tp - tq).natAbs ≤ 2 * B := (Int.natAbs_sub_le _ _).trans (by omega)
  have hb : (sq - sp).natAbs ≤ 2 * B := (Int.natAbs_sub_le _ _).trans (by omega)
  have hc : (sq * tp - sp * tq).natAbs ≤ 2 * B ^ 2 := by
    calc
      _ ≤ (sq * tp).natAbs + (sp * tq).natAbs := Int.natAbs_sub_le _ _
      _ = sq.natAbs * tp.natAbs + sp.natAbs * tq.natAbs := by rw [Int.natAbs_mul, Int.natAbs_mul]
      _ ≤ B * B + B * B := Nat.add_le_add (Nat.mul_le_mul hsq htp) (Nat.mul_le_mul hsp htq)
      _ = _ := by ring
  calc
    _ ≤ ((tp - tq) * x + (sq - sp) * y).natAbs + (sq * tp - sp * tq).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((tp - tq) * x).natAbs + ((sq - sp) * y).natAbs + (sq * tp - sp * tq).natAbs :=
      Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = (tp - tq).natAbs * x.natAbs + (sq - sp).natAbs * y.natAbs + (sq * tp - sp * tq).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ (2 * B) * X + (2 * B) * X + 2 * B ^ 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul ha hx) (Nat.mul_le_mul hb hy)) hc
    _ = _ := by ring

theorem collinear_card_bound {ι : Type*} (S : Finset ι) (s t : ι → ℤ) (g : ι → ℕ)
    (N A B : ℕ) (τ : ℝ) (hN : 2 ≤ N) (hA : 1 ≤ A) (hB : B < N) (hbig : 4 * A + 2 ≤ N)
    (hτ : 0 < τ) (x y : ℤ) (hvalues : ∀ i ∈ S, x + s i ≠ 0)
    (hx : x.natAbs ≤ A * N) (hy : y.natAbs ≤ A * N)
    (hs : ∀ i ∈ S, (s i).natAbs ≤ B) (ht : ∀ i ∈ S, (t i).natAbs ≤ B)
    (hcop : (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hdivs : ∀ i ∈ S, (g i : ℤ) ∣ x + s i) (hdivt : ∀ i ∈ S, (g i : ℤ) ∣ y + t i)
    (hlarge : ∀ i ∈ S, (N : ℝ) ^ τ ≤ (g i : ℝ))
    (hno : ∀ i ∈ S, ∀ j ∈ S, (s i, t i) ≠ (s j, t j) →
      (x + s i) * (y + t j) ≠ (x + s j) * (y + t i))
    (hcol : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
      (s j - s i) * (t k - t i) = (t j - t i) * (s k - s i)) :
    (S.card : ℝ) ≤ 3 / τ := by
  classical
  have hnR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp only [card_empty, Nat.cast_zero]
    positivity
  by_cases hsingle : ∀ i ∈ S, (s i, t i) = (s p, t p)
  · have hn : x + s p ≠ 0 := hvalues p hp
    have hheight : ((x + s p).natAbs : ℝ) ≤ (N : ℝ) ^ (3 : ℝ) := by
      have hval : (x + s p).natAbs ≤ N ^ 3 := by
        calc
          _ ≤ x.natAbs + (s p).natAbs := Int.natAbs_add_le _ _
          _ ≤ A * N + B := Nat.add_le_add hx (hs p hp)
          _ ≤ (A + 1) * N := by nlinarith only [hB]
          _ ≤ N * N := Nat.mul_le_mul_right N (by omega)
          _ = N ^ 2 := (pow_two N).symm
          _ ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Real.rpow_ofNat]
      exact_mod_cast hval
    apply CoprimeDivisorCardinality.card_bound S g (x + s p) (N : ℝ) τ 3 hnR hτ hn hcop
      (fun i hi ↦ ?_) hlarge hheight
    have he : s i = s p := congrArg Prod.fst (hsingle i hi)
    rw [← he]
    exact hdivs i hi
  · push Not at hsingle
    obtain ⟨q, hq, hpq⟩ := hsingle
    let a := t p - t q
    let b := s q - s p
    let c := s q * t p - s p * t q
    have hn : a * x + b * y + c ≠ 0 := by
      intro hz
      apply hno q hq p hp hpq
      dsimp [a, b, c] at hz
      nlinarith only [hz]
    have hline (i : ι) (hi : i ∈ S) : a * s i + b * t i = c := by
      have he := hcol p hp q hq i hi
      dsimp [a, b, c]
      nlinarith only [he]
    have hheight : ((a * x + b * y + c).natAbs : ℝ) ≤ (N : ℝ) ^ (3 : ℝ) := by
      have hval : (a * x + b * y + c).natAbs ≤ N ^ 3 := by
        calc
          _ ≤ 4 * B * (A * N) + 2 * B ^ 2 :=
            canonical_height x y (s p) (t p) (s q) (t q) (A * N) B hx hy
              (hs p hp) (ht p hp) (hs q hq) (ht q hq)
          _ ≤ 4 * N * (A * N) + 2 * N ^ 2 := by gcongr
          _ = (4 * A + 2) * N ^ 2 := by ring
          _ ≤ N * N ^ 2 := Nat.mul_le_mul_right _ hbig
          _ = N ^ 3 := by ring
      rw [Real.rpow_ofNat]
      exact_mod_cast hval
    exact CoprimeDivisorCardinality.line_card_bound S g x y a b c s t (N : ℝ) τ 3
      hnR hτ hn hcop hdivs hdivt hline hlarge hheight

end PaperP1.OffsetLineDivisorCount
