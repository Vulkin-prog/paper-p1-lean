module

public import PaperP1.Analysis.ReducedDyadicScales
public import PaperP1.Arithmetic.IntegralSourceCoefficients

/-! # Original positive real scales and their exact normalization using integer points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InitialDyadicSourceBox

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.ReducedDyadicScales

structure Box (N : ℕ) (ρ C δ : ℝ) where
  c₁ : ℕ
  c₂ : ℕ
  D : ℝ
  E : ℝ
  U : ℝ
  V : ℝ
  c₁_pos : 0 < c₁
  c₂_pos : 0 < c₂
  D_pos : 0 < D
  E_pos : 0 < E
  U_pos : 0 < U
  V_pos : 0 < V
  first_lower : ρ * N ≤ (c₁ : ℝ) * D ^ 2 * U
  first_upper : (c₁ : ℝ) * D ^ 2 * U ≤ C * N
  second_lower : ρ * N ≤ (c₂ : ℝ) * E ^ 2 * V
  second_upper : (c₂ : ℝ) * E ^ 2 * V ≤ C * N
  first_log : δ * Real.log N ≤ Real.log (D * E)
  second_log : δ * Real.log N ≤ Real.log (U * V)

structure Population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) (S : Finset Quad) : Prop where
  d_bounds : ∀ p ∈ S, X.D ≤ p.1.1 ∧ (p.1.1 : ℝ) ≤ 2 * X.D
  e_bounds : ∀ p ∈ S, X.E ≤ p.1.2 ∧ (p.1.2 : ℝ) ≤ 2 * X.E
  u_bounds : ∀ p ∈ S, X.U ≤ p.2.1 ∧ (p.2.1 : ℝ) ≤ 2 * X.U
  v_bounds : ∀ p ∈ S, X.V ≤ p.2.2 ∧ (p.2.2 : ℝ) ≤ 2 * X.V
  equation : ∀ p ∈ S, (X.c₂ : ℝ) * (p.1.2 : ℝ) ^ 2 * p.2.2 = (X.c₁ : ℝ) * (p.1.1 : ℝ) ^ 2 * p.2.1 + h

theorem positive_point {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} {h : ℤ}
    {S : Finset Quad} (hS : Population X h S) (p : Quad) (hp : p ∈ S) :
    0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
  exact ⟨by exact_mod_cast X.D_pos.trans_le (hS.d_bounds p hp).1,
    by exact_mod_cast X.E_pos.trans_le (hS.e_bounds p hp).1,
    by exact_mod_cast X.U_pos.trans_le (hS.u_bounds p hp).1,
    by exact_mod_cast X.V_pos.trans_le (hS.v_bounds p hp).1⟩

theorem half_scales {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} {h : ℤ}
    {S : Finset Quad} (hS : Population X h S) (hne : S.Nonempty) :
    1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hd, he, hu, hv⟩ := positive_point hS p hp
  have hdR : (1 : ℝ) ≤ p.1.1 := by exact_mod_cast hd
  have heR : (1 : ℝ) ≤ p.1.2 := by exact_mod_cast he
  have huR : (1 : ℝ) ≤ p.2.1 := by exact_mod_cast hu
  have hvR : (1 : ℝ) ≤ p.2.2 := by exact_mod_cast hv
  exact ⟨by linarith [(hS.d_bounds p hp).2], by linarith [(hS.e_bounds p hp).2],
    by linarith [(hS.u_bounds p hp).2], by linarith [(hS.v_bounds p hp).2]⟩

def normalize {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hhalf : 1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V) :
    DeterminantSourceBox.Box N ρ (8 * C) δ where
  c₁ := X.c₁
  c₂ := X.c₂
  D := enlarged X.D 1
  E := enlarged X.E 1
  U := enlarged X.U 1
  V := enlarged X.V 1
  c₁_ge_one := by exact_mod_cast X.c₁_pos
  c₂_ge_one := by exact_mod_cast X.c₂_pos
  D_ge_one := enlarged_ge_one X.D 1
  E_ge_one := enlarged_ge_one X.E 1
  U_ge_one := enlarged_ge_one X.U 1
  V_ge_one := enlarged_ge_one X.V 1
  first_lower := by
    have hl := source_product_lower (X.c₁ : ℝ) X.D X.U 1 1 (Nat.cast_nonneg _) X.D_pos.le X.U_pos.le
    exact X.first_lower.trans (by simpa only [Nat.cast_one, div_one] using hl)
  first_upper := by
    have hu := source_product_upper (X.c₁ : ℝ) X.D X.U 1 1 (Nat.cast_nonneg _)
      (by simpa only [Nat.cast_one, div_one] using hhalf.1)
      (by simpa only [Nat.cast_one, div_one] using hhalf.2.2.1)
    have hb := mul_le_mul_of_nonneg_left X.first_upper (by norm_num : (0 : ℝ) ≤ 8)
    simp only [Nat.cast_one, div_one] at hu
    simpa only [mul_assoc] using hu.trans hb
  second_lower := by
    have hl := source_product_lower (X.c₂ : ℝ) X.E X.V 1 1 (Nat.cast_nonneg _) X.E_pos.le X.V_pos.le
    exact X.second_lower.trans (by simpa only [Nat.cast_one, div_one] using hl)
  second_upper := by
    have hu := source_product_upper (X.c₂ : ℝ) X.E X.V 1 1 (Nat.cast_nonneg _)
      (by simpa only [Nat.cast_one, div_one] using hhalf.2.1)
      (by simpa only [Nat.cast_one, div_one] using hhalf.2.2.2)
    have hb := mul_le_mul_of_nonneg_left X.second_upper (by norm_num : (0 : ℝ) ≤ 8)
    simp only [Nat.cast_one, div_one] at hu
    simpa only [mul_assoc] using hu.trans hb
  first_log := by
    have hl := log_product_lower X.D X.E 1 X.D_pos X.E_pos (by decide)
    exact X.first_log.trans (by simpa only [Nat.cast_one, Real.log_one, mul_zero, sub_zero] using hl)
  second_log := by
    have hl := log_product_lower X.U X.V 1 X.U_pos X.V_pos (by decide)
    exact X.second_log.trans (by simpa only [Nat.cast_one, Real.log_one, mul_zero, sub_zero] using hl)

def coefficients {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hhalf : 1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V) :
    IntegralSourceCoefficients.IntegerCoefficients (normalize X hhalf) := ⟨X.c₁, X.c₂, rfl, rfl⟩

theorem normalized_population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hhalf : 1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V)
    (h : ℤ) (S : Finset Quad) (hS : Population X h S) :
    DeterminantSignedBoxes.SignedPopulation (normalize X hhalf) h S := by
  refine { d_bounds := ?_, e_bounds := ?_, u_bounds := ?_, v_bounds := ?_, equation := hS.equation }
  all_goals intro p hp
  all_goals have hpos := positive_point hS p hp
  · have hb := integer_point_bounds X.D 1 p.1.1 hpos.1
      (by simpa only [Nat.cast_one, div_one] using (hS.d_bounds p hp).1)
      (by simpa only [Nat.cast_one, div_one] using (hS.d_bounds p hp).2)
    exact ⟨hb.1, hb.2.1⟩
  · have hb := integer_point_bounds X.E 1 p.1.2 hpos.2.1
      (by simpa only [Nat.cast_one, div_one] using (hS.e_bounds p hp).1)
      (by simpa only [Nat.cast_one, div_one] using (hS.e_bounds p hp).2)
    exact ⟨hb.1, hb.2.1⟩
  · have hb := integer_point_bounds X.U 1 p.2.1 hpos.2.2.1
      (by simpa only [Nat.cast_one, div_one] using (hS.u_bounds p hp).1)
      (by simpa only [Nat.cast_one, div_one] using (hS.u_bounds p hp).2)
    exact ⟨hb.1, hb.2.1⟩
  · have hb := integer_point_bounds X.V 1 p.2.2 hpos.2.2.2
      (by simpa only [Nat.cast_one, div_one] using (hS.v_bounds p hp).1)
      (by simpa only [Nat.cast_one, div_one] using (hS.v_bounds p hp).2)
    exact ⟨hb.1, hb.2.1⟩

theorem normalized_barrier {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hhalf : 1 / 2 ≤ X.D ∧ 1 / 2 ≤ X.E ∧ 1 / 2 ≤ X.U ∧ 1 / 2 ≤ X.V) :
    (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 ≤
      (normalize X hhalf).c₁ * (normalize X hhalf).c₂ * ((normalize X hhalf).D * (normalize X hhalf).E) ^ 2 := by
  have hd : X.D ≤ enlarged X.D 1 := by simpa only [Nat.cast_one, div_one] using raw_le_enlarged X.D 1
  have he : X.E ≤ enlarged X.E 1 := by simpa only [Nat.cast_one, div_one] using raw_le_enlarged X.E 1
  change (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 ≤ (X.c₁ : ℝ) * X.c₂ * (enlarged X.D 1 * enlarged X.E 1) ^ 2
  have hprod := mul_le_mul hd he X.E_pos.le (X.D_pos.le.trans hd)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg X.D_pos.le X.E_pos.le) hprod 2)
    (mul_nonneg (Nat.cast_nonneg X.c₁) (Nat.cast_nonneg X.c₂))

end PaperP1.InitialDyadicSourceBox
