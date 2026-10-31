module

public import PaperP1.Model.RegularStarts
public import PaperP1.Model.LocalRigidityConsequences

/-! # Exact affine deviations on regular and exceptional windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularAffineBounds

open MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
open PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
open WindowRelationCode RegularStarts RelativeSignIndependence Finset

local instance regularAffinePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance regularAffineMeasurableF2 : MeasurableSpace F₂ := ⊤

def affineWindowMass (x L : ℕ) (b : Fin L → F₂) : ℝ :=
  infiniteRademacherMeasure.real {ω | infiniteStartBits x L ω = b}

theorem affineWindowMass_zero_or_rank (x L : ℕ) (b : Fin L → F₂) :
    affineWindowMass x L b = 0 ∨ affineWindowMass x L b =
      (2 ^ Module.finrank F₂ (squareClassSpace x L) : ℝ)⁻¹ := by
  classical
  rw [affineWindowMass, infiniteStartBits_atom_eq_finite (M := x + L) le_rfl]
  by_cases hc : Compatible (startSystem (x + L) x L) b
  · right
    rw [compatible_mass_eq_effectiveRate _ _ hc]
    have hcard := Fintype.card_congr (squareClassEquivRow (M := x + L) (x := x)
      (L := L) le_rfl).toEquiv
    unfold effectiveRate
    rw [← hcard, card_squareClassSpace]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  · exact Or.inl (uniformSolutionMass_of_not_compatible _ _ hc)

theorem affineWindowMass_nonneg (x L : ℕ) (b : Fin L → F₂) :
    0 ≤ affineWindowMass x L b := ENNReal.toReal_nonneg

theorem affineWindowMass_abs_sub_nominal {x L : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hr : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (b : Fin L → F₂) : |affineWindowMass x L b - (2 ^ L : ℝ)⁻¹| ≤ (2 ^ L : ℝ)⁻¹ := by
  have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ := le_of_lt (inv_pos.mpr (pow_pos (by norm_num) _))
  rcases affineWindowMass_zero_or_rank x L b with hzero | hmass
  · rw [hzero, zero_sub, abs_neg, abs_of_nonneg hp]
  · rw [hmass]
    rcases LocalRigidityConsequences.effective_rank_eq_or_pred hx hr with heq | heq
    · rw [heq, sub_self, abs_zero]
      exact hp
    · rw [heq, LocalRigidityConsequences.inverse_two_pow_pred hL]
      have : 2 * (2 ^ L : ℝ)⁻¹ - (2 ^ L : ℝ)⁻¹ = (2 ^ L : ℝ)⁻¹ := by ring
      rw [this, abs_of_nonneg hp]

theorem affineWindowMass_le_twice_nominal {x L : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hr : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (b : Fin L → F₂) : affineWindowMass x L b ≤ 2 * (2 ^ L : ℝ)⁻¹ := by
  have h := (abs_le.mp (affineWindowMass_abs_sub_nominal hx hL hr b)).2
  linarith

theorem sum_affine_deviations_le {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hr : ∀ x ∈ dyadicBlock N,
      Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (A : Finset ℕ) (hA : A ⊆ dyadicBlock N) (b : ℕ → Fin L → F₂) :
    (∑ x ∈ A, |affineWindowMass x L (b x) - (2 ^ L : ℝ)⁻¹|) ≤
      (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card := by
  classical
  have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ := le_of_lt (inv_pos.mpr (pow_pos (by norm_num) _))
  calc
    _ = ∑ x ∈ A \ regularStarts N L,
        |affineWindowMass x L (b x) - (2 ^ L : ℝ)⁻¹| := by
      symm
      apply sum_subset sdiff_subset
      intro x hx hxnot
      have hreg : x ∈ regularStarts N L := by
        by_contra h
        exact hxnot (mem_sdiff.mpr ⟨hx, h⟩)
      have hxpos : 0 < x := by have := (mem_Ico.mp (hA hx)).1; omega
      rw [affineWindowMass, affine_atom_on_regular hxpos hreg, sub_self, abs_zero]
    _ ≤ ∑ _x ∈ A \ regularStarts N L, (2 ^ L : ℝ)⁻¹ := by
      apply sum_le_sum
      intro x hx
      have hxblock := hA (mem_sdiff.mp hx).1
      have hxpos : 0 < x := by have := (mem_Ico.mp hxblock).1; omega
      exact affineWindowMass_abs_sub_nominal hxpos hL (hr x hxblock) _
    _ = (2 ^ L : ℝ)⁻¹ * (A \ regularStarts N L).card := by simp [mul_comm]
    _ ≤ (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card := by
      apply mul_le_mul_of_nonneg_left _ hp
      exact_mod_cast card_le_card (sdiff_subset_sdiff hA (subset_refl _))

end PaperP1.RegularAffineBounds
