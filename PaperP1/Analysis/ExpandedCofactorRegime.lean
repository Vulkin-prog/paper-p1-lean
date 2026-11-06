module

public import PaperP1.Analysis.NarrowCofactorRegime
public import PaperP1.Analysis.ExpandedSparseGramEnvelope

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ExpandedCofactorRegime
open Finset Filter PaperP1
open scoped Classical

theorem length_regime (N₀ : ℕ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ L : ℕ,
      (X : ℝ)^(15/16 : ℝ) ≤ (L : ℝ) → L ≤ X →
      N₀ ≤ L ∧ 1 ≤ L ∧ (X : ℝ) ≤ ExpandedSparseGramEnvelope.height L ∧
        (X : ℝ)^(1/18 : ℝ) ≤ ExpandedSparseGramEnvelope.cardEnvelope L ∧ L ≤ X := by
  have hp : Tendsto (fun X : ℕ ↦ (X : ℝ)^(15/16 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 15/16)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₁,hX₁⟩ := eventually_atTop.mp (hp.eventually (eventually_ge_atTop (N₀ : ℝ)))
  refine ⟨max 1 X₁,le_max_left _ _,?_⟩
  intro X hX L hLow hLX
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hxNN : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hcut : N₀ ≤ L := by exact_mod_cast (hX₁ X (by omega)).trans hLow
  have hOne : (1 : ℝ) ≤ L := (Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 15/16)).trans hLow
  have hL1 : 1 ≤ L := by exact_mod_cast hOne
  have hheight : (X : ℝ) ≤ ExpandedSparseGramEnvelope.height L := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hxNN (15/16 : ℝ)) hLow (by norm_num : (0 : ℝ) ≤ 9/8)
    rw [← Real.rpow_mul hxNN] at hh
    have hl : (X : ℝ) ≤ (X : ℝ)^((15/16 : ℝ)*(9/8 : ℝ)) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
        (by norm_num : (1 : ℝ) ≤ (15/16 : ℝ)*(9/8 : ℝ))
    exact hl.trans hh
  have hcard : (X : ℝ)^(1/18 : ℝ) ≤ ExpandedSparseGramEnvelope.cardEnvelope L := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hxNN (15/16 : ℝ)) hLow (by norm_num : (0 : ℝ) ≤ 1/16)
    rw [← Real.rpow_mul hxNN] at hh
    have hl := Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (1/18 : ℝ) ≤ (15/16 : ℝ)*(1/16 : ℝ))
    exact hl.trans hh
  exact ⟨hcut,hL1,hheight,hcard,hLX⟩

theorem cofactor_regime (N₀ : ℕ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ H j : ℕ,
      NarrowPrimeBands.anchor H j ≤ (X : ℝ)^(1/16 : ℝ) →
      N₀ ≤ ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ∧
      1 ≤ ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ∧
      (X : ℝ) ≤ ExpandedSparseGramEnvelope.height ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ∧
      (X : ℝ)^(1/18 : ℝ) ≤ ExpandedSparseGramEnvelope.cardEnvelope ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ∧
      ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ≤ X := by
  obtain ⟨X₀,hX₀,hreg⟩ := length_regime N₀
  refine ⟨X₀,hX₀,?_⟩
  intro X hX H j hanchor
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hx : (0 : ℝ) < X := by linarith
  have hu := NarrowPrimeBands.anchor_pos H j
  have hu1 := NarrowPrimeBands.anchor_one_le H j
  have hprod : (X : ℝ)^(15/16 : ℝ)*NarrowPrimeBands.anchor H j ≤ (X : ℝ) := by
    calc
      _ ≤ (X : ℝ)^(15/16 : ℝ)*(X : ℝ)^(1/16 : ℝ) :=
        mul_le_mul_of_nonneg_left hanchor (Real.rpow_nonneg hx.le _)
      _ = (X : ℝ) := by rw [← Real.rpow_add hx]; norm_num
  have hLow : (X : ℝ)^(15/16 : ℝ) ≤ (⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ : ℝ) :=
    ((le_div_iff₀ hu).mpr hprod).trans (Nat.le_ceil _)
  have hLX : ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ≤ X :=
    Nat.ceil_le.mpr ((div_le_iff₀ hu).mpr (by nlinarith only [hx,hu1]))
  exact hreg X hX _ hLow hLX

end PaperP1.ExpandedCofactorRegime
