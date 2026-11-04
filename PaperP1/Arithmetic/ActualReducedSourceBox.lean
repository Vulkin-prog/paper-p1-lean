module

public import PaperP1.Analysis.ReducedSourceMonomials
public import PaperP1.Analysis.ReducedSourceLogarithms

/-! # The full actual reduced source box and its literal primitive point population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualReducedSourceBox

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox
open PaperP1.IntegralSourceCoefficients PaperP1.ActualProjectivePairs PaperP1.ActualSourcePrimitiveReduction
open PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter

def transfer_coefficients {N N' : ℕ} {ρ C δ ρ' C' δ' : ℝ} {X : Box N ρ C δ} {Y : Box N' ρ' C' δ'}
    (coefs : IntegerCoefficients X) (hc₁ : Y.c₁ = X.c₁) (hc₂ : Y.c₂ = X.c₂) : IntegerCoefficients Y :=
  ⟨coefs.c₁, coefs.c₂, hc₁.trans coefs.first_eq, hc₂.trans coefs.second_eq⟩

theorem normalized_family_bounds {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ}
    {S : Finset Quad} (hS : Population X h S) (gq : ℕ × ℕ) (hg : 0 < gq.1) (hq : 0 < gq.2) :
    ∀ r ∈ family gq S,
      (enlarged X.D gq.1 ≤ (r.1.1 : ℝ) ∧ (r.1.1 : ℝ) ≤ 2 * enlarged X.D gq.1) ∧
      (enlarged X.E gq.1 ≤ (r.1.2 : ℝ) ∧ (r.1.2 : ℝ) ≤ 2 * enlarged X.E gq.1) ∧
      (enlarged X.U gq.2 ≤ (r.2.1 : ℝ) ∧ (r.2.1 : ℝ) ≤ 2 * enlarged X.U gq.2) ∧
      (enlarged X.V gq.2 ≤ (r.2.2 : ℝ) ∧ (r.2.2 : ℝ) ≤ 2 * enlarged X.V gq.2) ∧ Primitive r := by
  intro r hr
  have hp := family_primitive hS gq r hr
  have hb := family_raw_bounds hS gq hg hq r hr
  have hd := integer_point_bounds X.D gq.1 r.1.1 hp.1 hb.1.1 hb.1.2
  have he := integer_point_bounds X.E gq.1 r.1.2 hp.2.1 hb.2.1.1 hb.2.1.2
  have hu := integer_point_bounds X.U gq.2 r.2.1 hp.2.2.1 hb.2.2.1.1 hb.2.2.1.2
  have hv := integer_point_bounds X.V gq.2 r.2.2 hp.2.2.2.1 hb.2.2.2.1 hb.2.2.2.2
  exact ⟨⟨hd.1, hd.2.1⟩, ⟨he.1, he.2.1⟩, ⟨hu.1, hu.2.1⟩, ⟨hv.1, hv.2.1⟩, hp.2.2.2.2⟩

theorem nonempty_raw_scales {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ}
    {S : Finset Quad} (hS : Population X h S) (gq : ℕ × ℕ) (hg : 0 < gq.1) (hq : 0 < gq.2)
    (hne : (family gq S).Nonempty) :
    1 / 2 ≤ X.D / gq.1 ∧ 1 / 2 ≤ X.E / gq.1 ∧ 1 / 2 ≤ X.U / gq.2 ∧ 1 / 2 ≤ X.V / gq.2 := by
  obtain ⟨r, hr⟩ := hne
  have hp := family_primitive hS gq r hr
  have hb := family_raw_bounds hS gq hg hq r hr
  exact ⟨(integer_point_bounds X.D gq.1 r.1.1 hp.1 hb.1.1 hb.1.2).2.2.1,
    (integer_point_bounds X.E gq.1 r.1.2 hp.2.1 hb.2.1.1 hb.2.1.2).2.2.1,
    (integer_point_bounds X.U gq.2 r.2.1 hp.2.2.1 hb.2.2.1.1 hb.2.2.1.2).2.2.1,
    (integer_point_bounds X.V gq.2 r.2.2 hp.2.2.2.1 hb.2.2.2.1 hb.2.2.2.2).2.2.1⟩

theorem uniform_reduced_box (δ C ρ K A : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (L : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ S : Finset Quad, Population X h S → ∀ gq : ℕ × ℕ, (family gq S).Nonempty →
      let N' := parameter N (gq.1 ^ 2 * gq.2)
      ∃ Y : Box N' (ρ / 2) (8 * C) (δ / 2),
        Y.c₁ = X.c₁ ∧ Y.c₂ = X.c₂ ∧ Y.D = enlarged X.D gq.1 ∧ Y.E = enlarged X.E gq.1 ∧
        Y.U = enlarged X.U gq.2 ∧ Y.V = enlarged X.V gq.2 ∧ L ≤ N' ∧
        Population Y (h / (gq.1 ^ 2 * gq.2)) (family gq S) ∧ ∀ r ∈ family gq S, Primitive r := by
  obtain ⟨Ns, hsMargin⟩ := ReducedSourceLogarithms.uniform_shift_margin K A δ hδ
  obtain ⟨Np, hpThreshold⟩ := uniform_parameter_threshold K A L
  refine ⟨max Ns Np, ?_⟩
  intro N hN h hh hshift X coefs S hS gq hne
  obtain ⟨hN1, hroot, hlogh⟩ := hsMargin N (by omega) h hh hshift
  obtain ⟨hmem, hs, _hreduced, _hshiftLe, hscale⟩ := family_shift_bounds coefs hh hS gq hne
  have hg1 : 1 ≤ gq.1 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hmem).1).1).1
  have hq1 : 1 ≤ gq.2 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hmem).1).2).1
  have hg : 0 < gq.1 := by omega
  have hq : 0 < gq.2 := by omega
  have hparameter := hpThreshold N (by omega) (gq.1 ^ 2 * gq.2) h hs hscale hshift
  have hhalf := nonempty_raw_scales hS gq hg hq hne
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hpos := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  have heffective : 1 ≤ effective N (gq.1 ^ 2 * gq.2) :=
    hsqrt1.trans (effective_ge_sqrt N (gq.1 ^ 2 * gq.2) h hs hscale hroot)
  have hfirst := ReducedSourceMonomials.source_bounds N gq.1 gq.2 ρ C X.c₁ X.D X.U hg hq
    hρ.le hC.le (by linarith [X.c₁_ge_one]) (by linarith [X.D_ge_one]) (by linarith [X.U_ge_one])
    hhalf.1 hhalf.2.2.1 X.first_lower X.first_upper heffective
  have hsecond := ReducedSourceMonomials.source_bounds N gq.1 gq.2 ρ C X.c₂ X.E X.V hg hq
    hρ.le hC.le (by linarith [X.c₂_ge_one]) (by linarith [X.E_ge_one]) (by linarith [X.V_ge_one])
    hhalf.2.1 hhalf.2.2.2 X.second_lower X.second_upper heffective
  have hlogs := ReducedSourceLogarithms.reduced_log_bounds X hN1 hδ h gq.1 gq.2 hh hg hq hscale hlogh
  let N' := parameter N (gq.1 ^ 2 * gq.2)
  let Y : Box N' (ρ / 2) (8 * C) (δ / 2) := {
    c₁ := X.c₁
    c₂ := X.c₂
    D := enlarged X.D gq.1
    E := enlarged X.E gq.1
    U := enlarged X.U gq.2
    V := enlarged X.V gq.2
    c₁_ge_one := X.c₁_ge_one
    c₂_ge_one := X.c₂_ge_one
    D_ge_one := enlarged_ge_one _ _
    E_ge_one := enlarged_ge_one _ _
    U_ge_one := enlarged_ge_one _ _
    V_ge_one := enlarged_ge_one _ _
    first_lower := hfirst.1
    first_upper := hfirst.2
    second_lower := hsecond.1
    second_upper := hsecond.2
    first_log := hlogs.1
    second_log := hlogs.2 }
  have hnormalized := normalized_family_bounds hS gq hg hq
  have hpopulation : Population Y (h / (gq.1 ^ 2 * gq.2)) (family gq S) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact (hnormalized r hr).1
    · intro r hr
      exact (hnormalized r hr).2.1
    · intro r hr
      exact (hnormalized r hr).2.2.1
    · intro r hr
      exact (hnormalized r hr).2.2.2.1
    · intro r hr
      change X.c₂ * (r.1.2 : ℝ) ^ 2 * r.2.2 = X.c₁ * (r.1.1 : ℝ) ^ 2 * r.2.1 + (h / (gq.1 ^ 2 * gq.2) : ℕ)
      rw [coefs.first_eq, coefs.second_eq]
      exact_mod_cast (family_equation coefs hS gq r hr).symm
  exact ⟨Y, rfl, rfl, rfl, rfl, rfl, rfl, hparameter.1, hpopulation, fun r hr ↦ (hnormalized r hr).2.2.2.2⟩

end PaperP1.ActualReducedSourceBox
