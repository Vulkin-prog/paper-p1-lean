module

public import PaperP1.Arithmetic.DeterminantPrimitiveReduction
public import PaperP1.Arithmetic.ActualSourceArithmetic

/-! # Exact gcd families of the literal positive integer source population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourcePrimitiveReduction

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox
open PaperP1.IntegralSourceCoefficients PaperP1.DeterminantPrimitiveReduction PaperP1.ActualProjectivePairs

def part (gq : ℕ × ℕ) (S : Finset Quad) : Finset Quad :=
  S.filter (fun p ↦ (Nat.gcd p.1.1 p.1.2, Nat.gcd p.2.1 p.2.2) = gq)

def family (gq : ℕ × ℕ) (S : Finset Quad) : Finset Quad := (part gq S).image reduced

theorem natural_equation {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X)
    {S : Finset Quad} (hS : Population X h S) (p : Quad) (hp : p ∈ S) :
    coefs.c₁ * p.1.1 ^ 2 * p.2.1 + h = coefs.c₂ * p.1.2 ^ 2 * p.2.2 := by
  have hr := hS.equation p hp
  rw [coefs.first_eq, coefs.second_eq] at hr
  exact_mod_cast hr.symm

theorem source_positive {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ}
    {S : Finset Quad} (hS : Population X h S) (p : Quad) (hp : p ∈ S) :
    0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
  exact ⟨by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.D_ge_one.trans (hS.d_bounds p hp).1)),
    by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.E_ge_one.trans (hS.e_bounds p hp).1)),
    by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.U_ge_one.trans (hS.u_bounds p hp).1)),
    by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.V_ge_one.trans (hS.v_bounds p hp).1))⟩

theorem finite_source_cover {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ}
    (_coefs : IntegerCoefficients X) (hh : 0 < h) (S : Finset Quad) (hS : Population X h S) :
    S.card ≤ ∑ gq ∈ reductions h, (family gq S).card := by
  apply finite_primitive_cover hh S
  intro p hp
  have hpos := source_positive hS p hp
  exact ⟨hpos.1, hpos.2.2.1, natural_equation _coefs hS p hp⟩

theorem reconstruction_on_part (gq : ℕ × ℕ) (S : Finset Quad) (p : Quad) (hp : p ∈ part gq S) :
    gq.1 * (reduced p).1.1 = p.1.1 ∧ gq.1 * (reduced p).1.2 = p.1.2 ∧
      gq.2 * (reduced p).2.1 = p.2.1 ∧ gq.2 * (reduced p).2.2 = p.2.2 := by
  have hpair := (mem_filter.mp hp).2
  have hg : Nat.gcd p.1.1 p.1.2 = gq.1 := congrArg Prod.fst hpair
  have hq : Nat.gcd p.2.1 p.2.2 = gq.2 := congrArg Prod.snd hpair
  simpa only [hg, hq] using reconstruct p

theorem family_primitive {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ}
    {S : Finset Quad} (hS : Population X h S) (gq : ℕ × ℕ) :
    ∀ r ∈ family gq S, 0 < r.1.1 ∧ 0 < r.1.2 ∧ 0 < r.2.1 ∧ 0 < r.2.2 ∧ Primitive r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
  have hpos := source_positive hS p (mem_filter.mp hp).1
  obtain ⟨_, hd, he, hu, hv, hde, huv⟩ := primitive p hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2
  exact ⟨hd, he, hu, hv, hde, huv⟩

theorem family_equation {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X)
    {S : Finset Quad} (hS : Population X h S) (gq : ℕ × ℕ) :
    ∀ r ∈ family gq S, coefs.c₁ * r.1.1 ^ 2 * r.2.1 + h / (gq.1 ^ 2 * gq.2) = coefs.c₂ * r.1.2 ^ 2 * r.2.2 := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
  have hpS := (mem_filter.mp hp).1
  have hpair := (mem_filter.mp hp).2
  have hg : Nat.gcd p.1.1 p.1.2 = gq.1 := congrArg Prod.fst hpair
  have hq : Nat.gcd p.2.1 p.2.2 = gq.2 := congrArg Prod.snd hpair
  have hscale : scale p = gq.1 ^ 2 * gq.2 := by unfold scale; rw [hg, hq]
  have hpos := source_positive hS p hpS
  have hsp := (primitive p hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2).1
  simpa only [hscale] using reduced_equation hsp (natural_equation coefs hS p hpS)

theorem family_shift_bounds {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (_coefs : IntegerCoefficients X)
    (hh : 0 < h) {S : Finset Quad} (hS : Population X h S) (gq : ℕ × ℕ) (hne : (family gq S).Nonempty) :
    gq ∈ reductions h ∧ 0 < gq.1 ^ 2 * gq.2 ∧ 0 < h / (gq.1 ^ 2 * gq.2) ∧
      h / (gq.1 ^ 2 * gq.2) ≤ h ∧ gq.1 ^ 2 * gq.2 ≤ h := by
  obtain ⟨r, hr⟩ := hne
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
  have hpS := (mem_filter.mp hp).1
  have hpair := (mem_filter.mp hp).2
  have hg : Nat.gcd p.1.1 p.1.2 = gq.1 := congrArg Prod.fst hpair
  have hq : Nat.gcd p.2.1 p.2.2 = gq.2 := congrArg Prod.snd hpair
  have hscale : scale p = gq.1 ^ 2 * gq.2 := by unfold scale; rw [hg, hq]
  have hpos := source_positive hS p hpS
  have hsp := (primitive p hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2).1
  have heq := natural_equation _coefs hS p hpS
  have hm := actual_reduction_mem hpos.1 hpos.2.2.1 hh heq
  have hs := reduced_shift_bounds hsp hh heq
  exact ⟨by simpa only [hpair] using hm, by simpa only [hscale] using hsp,
    by simpa only [hscale] using hs.1, by simpa only [hscale] using hs.2.1, by simpa only [hscale] using hs.2.2⟩

theorem divide_dyadic_bounds (D : ℝ) (g m a : ℕ) (hg : 0 < g) (heq : g * m = a)
    (hlo : D ≤ (a : ℝ)) (hhi : (a : ℝ) ≤ 2 * D) : D / g ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * (D / g) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hr : (g : ℝ) * m = a := by exact_mod_cast heq
  constructor
  · apply (div_le_iff₀ hgR).mpr
    nlinarith only [hr, hlo]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hgR).mpr
    nlinarith only [hr, hhi]

theorem family_raw_bounds {N h : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ}
    {S : Finset Quad} (hS : Population X h S) (gq : ℕ × ℕ) (hg : 0 < gq.1) (hq : 0 < gq.2) :
    ∀ r ∈ family gq S,
      (X.D / gq.1 ≤ (r.1.1 : ℝ) ∧ (r.1.1 : ℝ) ≤ 2 * (X.D / gq.1)) ∧
      (X.E / gq.1 ≤ (r.1.2 : ℝ) ∧ (r.1.2 : ℝ) ≤ 2 * (X.E / gq.1)) ∧
      (X.U / gq.2 ≤ (r.2.1 : ℝ) ∧ (r.2.1 : ℝ) ≤ 2 * (X.U / gq.2)) ∧
      (X.V / gq.2 ≤ (r.2.2 : ℝ) ∧ (r.2.2 : ℝ) ≤ 2 * (X.V / gq.2)) := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
  have hpS := (mem_filter.mp hp).1
  have hrecon := reconstruction_on_part gq S p hp
  exact ⟨divide_dyadic_bounds X.D gq.1 _ _ hg hrecon.1 (hS.d_bounds p hpS).1 (hS.d_bounds p hpS).2,
    divide_dyadic_bounds X.E gq.1 _ _ hg hrecon.2.1 (hS.e_bounds p hpS).1 (hS.e_bounds p hpS).2,
    divide_dyadic_bounds X.U gq.2 _ _ hq hrecon.2.2.1 (hS.u_bounds p hpS).1 (hS.u_bounds p hpS).2,
    divide_dyadic_bounds X.V gq.2 _ _ hq hrecon.2.2.2 (hS.v_bounds p hpS).1 (hS.v_bounds p hpS).2⟩

end PaperP1.ActualSourcePrimitiveReduction
