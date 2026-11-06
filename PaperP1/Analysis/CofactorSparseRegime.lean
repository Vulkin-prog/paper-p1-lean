module

public import PaperP1.Analysis.SparseGramEnvelope
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CofactorSparseRegime
open Finset Filter PaperP1
open scoped Classical

theorem margin_eventually : ∀ᶠ X : ℕ in atTop, 1 ≤ X ∧
    (((X : ℝ)^(7/8 : ℝ)+1)*(X : ℝ)^(1/16 : ℝ)) ≤ (X : ℝ) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/16)).comp hnat
  have h2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 15/16)).comp hnat
  filter_upwards [eventually_ge_atTop 1,h1.eventually (eventually_ge_atTop 2),h2.eventually (eventually_ge_atTop 2)] with X hX hp1 hp2
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  change 2 ≤ (X : ℝ)^(1/16 : ℝ) at hp1
  change 2 ≤ (X : ℝ)^(15/16 : ℝ) at hp2
  have he1 : (X : ℝ)^(7/8 : ℝ)*(X : ℝ)^(1/16 : ℝ)=(X : ℝ)^(15/16 : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hp1 (Real.rpow_nonneg (Nat.cast_nonneg X) (7/8 : ℝ))
  rw [he1] at hm
  have hs : (X : ℝ)^(7/8 : ℝ)+1 ≤ (X : ℝ)^(15/16 : ℝ) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (Nat.cast_nonneg X) (1/16 : ℝ))
  have he2 : (X : ℝ)^(15/16 : ℝ)*(X : ℝ)^(1/16 : ℝ)=(X : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [he2] at hh
  exact ⟨hX,hh⟩

theorem cofactor_lower_uniform : ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ p : ℕ,
    1 ≤ p → (p : ℝ) ≤ (X : ℝ)^(1/16 : ℝ) → (X : ℝ)^(7/8 : ℝ) ≤ ((X/p : ℕ) : ℝ) := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp margin_eventually
  refine ⟨max 1 X₀,le_max_left _ _,?_⟩
  intro X hX p hp hpB
  have hp0 : 0 < p := by omega
  have hmod := Nat.mod_lt X hp0
  have hdiv := Nat.mod_add_div X p
  have hInt : X < (X/p+1)*p := by nlinarith only [hmod,hdiv]
  have hReal : (X : ℝ)<(((X/p : ℕ) : ℝ)+1)*(p : ℝ) := by exact_mod_cast hInt
  have hm := (hX₀ X (by omega)).2
  by_contra hbad
  have hb : ((X/p : ℕ) : ℝ) ≤ (X : ℝ)^(7/8 : ℝ) := (lt_of_not_ge hbad).le
  have hpNN : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hprod := mul_le_mul (add_le_add hb (le_refl (1 : ℝ))) hpB hpNN
    (show 0 ≤ (X : ℝ)^(7/8 : ℝ)+1 by positivity)
  linarith only [hReal,hm,hprod]

theorem uniform_regime (N₀ : ℕ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ p : ℕ, 1 ≤ p → (p : ℝ) ≤ (X : ℝ)^(1/16 : ℝ) →
      N₀ ≤ X/p ∧ 1 ≤ X/p ∧ (X : ℝ) ≤ SparseGramEnvelope.height (X/p) ∧
      (X : ℝ)^(1/200 : ℝ) ≤ SparseGramEnvelope.cardEnvelope (X/p) ∧ X/p ≤ X := by
  obtain ⟨X₁,hX₁,hL⟩ := cofactor_lower_uniform
  have hp : Tendsto (fun X : ℕ ↦ (X : ℝ)^(7/8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/8)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp (hp.eventually (eventually_ge_atTop (N₀ : ℝ)))
  refine ⟨max X₁ X₂,by omega,?_⟩
  intro X hX p hp1 hpB
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hxNN : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hLow := hL X (by omega) p hp1 hpB
  have hNcut : N₀ ≤ X/p := by exact_mod_cast (hX₂ X (by omega)).trans hLow
  have hOne : (1 : ℝ) ≤ ((X/p : ℕ) : ℝ) := (Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 7/8)).trans hLow
  have hN1 : 1 ≤ X/p := by exact_mod_cast hOne
  have hHeight : (X : ℝ) ≤ SparseGramEnvelope.height (X/p) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hxNN (7/8 : ℝ)) hLow (by norm_num : (0 : ℝ) ≤ 5/4)
    rw [← Real.rpow_mul hxNN] at hh
    have hl : (X : ℝ) ≤ (X : ℝ)^((7/8 : ℝ)*(5/4 : ℝ)) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
        (by norm_num : (1 : ℝ) ≤ (7/8 : ℝ)*(5/4 : ℝ))
    exact hl.trans hh
  have hCard : (X : ℝ)^(1/200 : ℝ) ≤ SparseGramEnvelope.cardEnvelope (X/p) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hxNN (7/8 : ℝ)) hLow (by norm_num : (0 : ℝ) ≤ 1/100)
    rw [← Real.rpow_mul hxNN] at hh
    have hl := Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (1/200 : ℝ) ≤ (7/8 : ℝ)*(1/100 : ℝ))
    exact hl.trans hh
  exact ⟨hNcut,hN1,hHeight,hCard,Nat.div_le_self X p⟩
end PaperP1.CofactorSparseRegime
