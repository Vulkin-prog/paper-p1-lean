module

public import PaperP1.Arithmetic.FieldConicCount
public import Mathlib.Data.Nat.Find

/-! # An unconditional, slowly growing degree cap for plane sublinearity

The cap is chosen before coefficient fields and equations. Its growth is
nonquantitative, and the lower degree is two.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonlinearPlaneDegreeCap

open Polynomial Filter

theorem bounded_degree_sublinear (M : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ H₀ : ℝ, 2 < H₀ ∧ ∀ H ≥ H₀, ∀ (F : Type*) [Field F] [CharZero F],
      ∀ P : F[X][X], 2 ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ M →
        Irreducible P → ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ η * H := by
  obtain ⟨Hc, hHc, hc⟩ := FieldConicCount.uniform_sublinear η hη
  obtain ⟨Hg, _hHg, hg⟩ := BoundedDegreePlaneCounts.uniform_sublinear M η hη
  refine ⟨max Hc Hg, hHc.trans_le (le_max_left _ _), ?_⟩
  intro H hH F _hF _hchar P hD hM hP
  by_cases htwo : PlaneCurvePointCount.degree P = 2
  · exact hc H ((le_max_left _ _).trans hH) F P htwo hP
  · exact hg H ((le_max_right _ _).trans hH) F P (by omega) hM hP

def UniformSublinear (c : ℝ) (cap : ℕ → ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X], Irreducible P →
      2 ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ cap B →
        ((PlaneCurvePointCount.grid P ⌊c * (B : ℝ)⌋₊).card : ℝ) ≤ η * B

theorem exists_cap_below (c : ℝ) (hc : 0 < c) (L : ℕ → ℕ)
    (hLmono : Monotone L) (hL : Tendsto L atTop atTop) :
    ∃ cap : ℕ → ℕ, Monotone cap ∧ Tendsto cap atTop atTop ∧
      (∀ B, 2 ≤ cap B ∧ cap B ≤ L B + 2) ∧ UniformSublinear c cap := by
  classical
  choose H hH hcount using fun m : ℕ ↦ bounded_degree_sublinear
    (m + 2) (((m : ℝ) + 1)⁻¹ / c) (div_pos (inv_pos.mpr (by positivity)) hc)
  let T (m : ℕ) := ⌈H m / c⌉₊
  let stage (B : ℕ) := Nat.findGreatest (fun m ↦ T m ≤ B) (L B)
  let cap (B : ℕ) := stage B + 2
  have hmono : Monotone cap := by
    intro B C hBC
    have hh : stage B ≤ stage C := Nat.findGreatest_mono (fun m hm ↦ hm.trans hBC) (hLmono hBC)
    dsimp only [cap]
    omega
  have hstage : Tendsto stage atTop atTop := by
    apply tendsto_atTop.2
    intro m
    filter_upwards [hL.eventually (eventually_ge_atTop m), eventually_ge_atTop (T m)] with B hLB hTB
    exact Nat.le_findGreatest hLB hTB
  have hcap : Tendsto cap atTop atTop := by
    apply tendsto_atTop.2
    intro m
    filter_upwards [hstage.eventually (eventually_ge_atTop m)] with B hB
    dsimp only [cap]
    omega
  refine ⟨cap, hmono, hcap, ?_, ?_⟩
  · intro B
    have hh : stage B ≤ L B := Nat.findGreatest_le (L B)
    dsimp only [cap]
    omega
  intro η hη
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / η)
  have hηr : ((r : ℝ) + 1)⁻¹ ≤ η := by
    rw [← one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mpr
    have hh := (div_lt_iff₀ hη).mp hr
    nlinarith
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp (hstage.eventually (eventually_ge_atTop r))
  refine ⟨max 2 (max (T 0) B₁), by omega, ?_⟩
  intro B hB F _hF _hchar P hP hD hM
  have hT0 : T 0 ≤ B := by omega
  have hTstage : T (stage B) ≤ B :=
    Nat.findGreatest_spec (P := fun m ↦ T m ≤ B) (Nat.zero_le (L B)) hT0
  have hceil : H (stage B) / c ≤ (T (stage B) : ℝ) := Nat.le_ceil _
  have hTB : (T (stage B) : ℝ) ≤ B := by exact_mod_cast hTstage
  have hheight : H (stage B) ≤ c * (B : ℝ) := by
    have hh := (div_le_iff₀ hc).mp (hceil.trans hTB)
    simpa only [mul_comm] using hh
  have hb := hcount (stage B) (c * (B : ℝ)) hheight F P hD hM hP
  have hcancel : (((stage B : ℝ) + 1)⁻¹ / c) * (c * (B : ℝ)) =
      ((stage B : ℝ) + 1)⁻¹ * B := by
    calc
      _ = ((stage B : ℝ) + 1)⁻¹ * (c⁻¹ * c) * (B : ℝ) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hc.ne', mul_one]
  rw [hcancel] at hb
  have hrstage : r ≤ stage B := hB₁ B (by omega)
  have hrR : (r : ℝ) + 1 ≤ (stage B : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrstage 1
  have hinv : ((stage B : ℝ) + 1)⁻¹ ≤ ((r : ℝ) + 1)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (r : ℝ) + 1) hrR
  exact hb.trans (mul_le_mul_of_nonneg_right (hinv.trans hηr) (Nat.cast_nonneg B))

theorem exists_cap (c : ℝ) (hc : 0 < c) :
    ∃ cap : ℕ → ℕ, Monotone cap ∧ Tendsto cap atTop atTop ∧
      (∀ B, 2 ≤ cap B ∧ cap B ≤ B + 2) ∧ UniformSublinear c cap := by
  exact exists_cap_below c hc (fun B ↦ B) (fun _ _ h ↦ h) tendsto_id

end PaperP1.NonlinearPlaneDegreeCap
