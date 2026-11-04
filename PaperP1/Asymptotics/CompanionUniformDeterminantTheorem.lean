module

public import PaperP1.Asymptotics.WeightedInitialSourceCount

/-! # Companion T1.4: count the actual full finite solution set at the original scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompanionUniformDeterminantTheorem

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.InitialDyadicSourceBox PaperP1.DeterminantLogScale

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def admissible {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) (p : Quad) : Prop :=
  (X.D ≤ (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) ≤ 2 * X.D) ∧
  (X.E ≤ (p.1.2 : ℝ) ∧ (p.1.2 : ℝ) ≤ 2 * X.E) ∧
  (X.U ≤ (p.2.1 : ℝ) ∧ (p.2.1 : ℝ) ≤ 2 * X.U) ∧
  (X.V ≤ (p.2.2 : ℝ) ∧ (p.2.2 : ℝ) ≤ 2 * X.V) ∧
  (X.c₂ : ℝ) * (p.1.2 : ℝ) ^ 2 * p.2.2 = (X.c₁ : ℝ) * (p.1.1 : ℝ) ^ 2 * p.2.1 + h

def solutions {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) : Finset Quad :=
  (((Icc 1 ⌈2 * X.D⌉₊) ×ˢ (Icc 1 ⌈2 * X.E⌉₊)) ×ˢ
    ((Icc 1 ⌈2 * X.U⌉₊) ×ˢ (Icc 1 ⌈2 * X.V⌉₊))).filter (admissible X h)

theorem mem_solutions_iff {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) (p : Quad) :
    p ∈ solutions X h ↔ admissible X h p := by
  constructor
  · intro hp
    exact (mem_filter.mp hp).2
  · intro hp
    have hpred := hp
    obtain ⟨hd, he, hu, hv, _heq⟩ := hp
    have hd₁ : 1 ≤ p.1.1 := by exact_mod_cast X.D_pos.trans_le hd.1
    have he₁ : 1 ≤ p.1.2 := by exact_mod_cast X.E_pos.trans_le he.1
    have hu₁ : 1 ≤ p.2.1 := by exact_mod_cast X.U_pos.trans_le hu.1
    have hv₁ : 1 ≤ p.2.2 := by exact_mod_cast X.V_pos.trans_le hv.1
    have hd₂ : p.1.1 ≤ ⌈2 * X.D⌉₊ := by exact_mod_cast hd.2.trans (Nat.le_ceil (2 * X.D))
    have he₂ : p.1.2 ≤ ⌈2 * X.E⌉₊ := by exact_mod_cast he.2.trans (Nat.le_ceil (2 * X.E))
    have hu₂ : p.2.1 ≤ ⌈2 * X.U⌉₊ := by exact_mod_cast hu.2.trans (Nat.le_ceil (2 * X.U))
    have hv₂ : p.2.2 ≤ ⌈2 * X.V⌉₊ := by exact_mod_cast hv.2.trans (Nat.le_ceil (2 * X.V))
    apply mem_filter.mpr
    exact ⟨mem_product.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hd₁, hd₂⟩, mem_Icc.mpr ⟨he₁, he₂⟩⟩,
      mem_product.mpr ⟨mem_Icc.mpr ⟨hu₁, hu₂⟩, mem_Icc.mpr ⟨hv₁, hv₂⟩⟩⟩, hpred⟩

theorem population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) : Population X h (solutions X h) := by
  refine { d_bounds := ?_, e_bounds := ?_, u_bounds := ?_, v_bounds := ?_, equation := ?_ }
  · exact fun p hp ↦ ((mem_solutions_iff X h p).mp hp).1
  · exact fun p hp ↦ ((mem_solutions_iff X h p).mp hp).2.1
  · exact fun p hp ↦ ((mem_solutions_iff X h p).mp hp).2.2.1
  · exact fun p hp ↦ ((mem_solutions_iff X h p).mp hp).2.2.2.1
  · exact fun p hp ↦ ((mem_solutions_iff X h p).mp hp).2.2.2.2

theorem weakened_barrier_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ Kbar Abar K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 →
      ((solutions X h).card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  obtain ⟨N₀, hN₀⟩ := WeightedInitialSourceCount.uniform_count hHB hNG δ C ρ Kbar Abar K A ε
    hδ hC hρ hρ₁ hKbar hAbar hK hA hε
  exact ⟨N₀, fun N hN h hh hshift X Γ hΓ hΓbudget hb ↦
    hN₀ N hN h hh hshift X Γ hΓ hΓbudget hb (solutions X h) (population X h)⟩

theorem companion_T1_4 (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (A₀ δ ε ρ C : ℝ) (hA₀ : 0 < A₀) (hδ : 0 < δ) (hε : 0 < ε)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ (Real.log N) ^ A₀ →
      ∀ X : Box N ρ C δ, (N : ℝ) ≤ (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 →
      ((solutions X h).card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  obtain ⟨N₀, hN₀⟩ := weakened_barrier_count hHB hNG δ C ρ 1 0 1 A₀ ε hδ hC hρ hρ₁
    (by norm_num) (by norm_num) (by norm_num) hA₀.le hε
  refine ⟨N₀, ?_⟩
  intro N hN h hh hshift X hbarrier
  exact hN₀ N hN h hh (by simpa only [one_mul] using hshift) X 1 (by norm_num)
    (by simp only [Real.rpow_zero, one_mul, le_refl]) (by simpa only [one_mul] using hbarrier)

end PaperP1.CompanionUniformDeterminantTheorem
