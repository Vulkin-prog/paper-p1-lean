module

public import PaperP1.Arithmetic.FiniteResidualRank
public import PaperP1.Arithmetic.PrimeLogBudget
public import PaperP1.Analysis.ElementaryLogGrowth

/-! # Uniform sublinear residual rank with the component cutoff chosen first -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ResidualComponentRank

open Finset Filter PaperP1.Arithmetic PaperP1.PrimeRowComponents PaperP1.PrimeComponentCount
  PaperP1.FiniteResidualRank

theorem small_component_rate (c D M : ℝ) (hc : 0 < c) (hD : 0 < D)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ S P : Finset ℕ, ∀ U R : ℕ,
      (∀ p, (rows S P p).card ≤ 2) →
      (∀ n ∈ S, U ≤ n) → (∀ n ∈ S, n ≤ U + R) →
      1 ≤ R → 2 * R ≤ U → c * B ≤ Real.log U →
      Real.log (64 * (R : ℝ)) ≤ D * Real.log B →
      (P.card : ℝ) + 1 ≤ M * B / Real.log B →
      ((small S P K).card : ℝ) ≤ C * B / Real.log B := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  let κ : ℝ := c / (8 * K * D)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let A : ℕ := ⌈2 * M / κ⌉₊
  have hAκ : 2 * M ≤ (A : ℝ) * κ :=
    (div_le_iff₀ hκ).mp (Nat.le_ceil (2 * M / κ))
  have hsmallRatio : ∀ᶠ B : ℕ in atTop, Real.log B / B < κ / 2 :=
    (tendsto_order.1 PrimeLogBudget.log_nat_div_self_tendsto).2 _ (by positivity)
  obtain ⟨Bq, hBq⟩ := eventually_atTop.1 hsmallRatio
  refine ⟨2 * κ * (2 : ℝ) ^ (A + 1), by positivity, max Bq 2, ?_⟩
  intro B hB S P U R hrows hlower hupper hR hU hlogU hlogR hP
  have hBtwo : 2 ≤ B := (le_max_right _ _).trans hB
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let q : ℝ := κ * B / Real.log B
  let t : ℕ := ⌊q⌋₊
  have hq : 2 ≤ q := by
    have h := (div_lt_iff₀ hBpos).mp (hBq B ((le_max_left _ _).trans hB))
    apply (le_div_iff₀ hlogB).mpr
    linarith
  have htlo : q / 2 ≤ (t : ℝ) := by
    have hfloor : q < (t : ℝ) + 1 := Nat.lt_floor_add_one q
    linarith
  have hthi : (t : ℝ) ≤ q := Nat.floor_le (by dsimp [q]; positivity)
  have ht : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by linarith)
  have hbudgetR : (P.card : ℝ) + 1 ≤ (A : ℝ) * t := by
    calc
      _ ≤ M * ((B : ℝ) / Real.log B) := by simpa only [mul_div_assoc] using hP
      _ ≤ ((A : ℝ) * κ / 2) * ((B : ℝ) / Real.log B) :=
        mul_le_mul_of_nonneg_right (by linarith : M ≤ (A : ℝ) * κ / 2) (by positivity)
      _ = (A : ℝ) * (q / 2) := by dsimp [q]; ring
      _ ≤ (A : ℝ) * t := mul_le_mul_of_nonneg_left htlo (Nat.cast_nonneg (α := ℝ) A)
  have hbudget : P.card + 1 ≤ A * t := by exact_mod_cast hbudgetR
  have hlogbound : (2 * (K * t) : ℝ) * Real.log (64 * (R : ℝ)) ≤ c * B / 4 := by
    calc
      _ ≤ (2 : ℝ) * K * t * (D * Real.log B) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
          mul_le_mul_of_nonneg_left hlogR (show 0 ≤ (2 * (K * t) : ℝ) by positivity)
      _ ≤ (2 : ℝ) * K * q * (D * Real.log B) := by
        have h := mul_le_mul_of_nonneg_right hthi (show 0 ≤ 2 * (K : ℝ) * D * Real.log B by positivity)
        nlinarith
      _ = c * B / 4 := by
        dsimp [q, κ]
        field_simp
        ring
  have hlogstrict : (2 * (K * t) : ℝ) * Real.log (64 * (R : ℝ)) < Real.log U := by
    have hcB : 0 < c * B := mul_pos hc hBpos
    linarith
  have hgrowth := LocalDefectBound.endpoint_growth_of_log (t := K * t) hR (by omega : 0 < U)
    (by simpa only [Nat.cast_mul] using hlogstrict)
  have hcount := small_count_of_budget hrows hlower hupper hR hU hgrowth ht hbudget
  have hcountR : ((small S P K).card : ℝ) < 2 * (t : ℝ) * (2 : ℝ) ^ (A + 1) := by exact_mod_cast hcount
  apply hcountR.le.trans
  calc
    _ ≤ 2 * q * (2 : ℝ) ^ (A + 1) := by
      have h := mul_le_mul_of_nonneg_right hthi (show 0 ≤ 2 * (2 : ℝ) ^ (A + 1) by positivity)
      nlinarith
    _ = (2 * κ * (2 : ℝ) ^ (A + 1)) * B / Real.log B := by dsimp [q]; ring

theorem row_rank_sublinear (c D M V ε : ℝ) (hc : 0 < c) (hD : 0 < D) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ S P : Finset ℕ, ∀ U R : ℕ,
      (∀ p, (rows S P p).card ≤ 2) →
      (∀ n ∈ S, U ≤ n) → (∀ n ∈ S, n ≤ U + R) →
      1 ≤ R → 2 * R ≤ U → c * B ≤ Real.log U →
      Real.log (64 * (R : ℝ)) ≤ D * Real.log B →
      (P.card : ℝ) + 1 ≤ M * B / Real.log B → (S.card : ℝ) ≤ V * B →
      (Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows S P)) : ℝ) ≤ ε * B := by
  obtain ⟨K, hKbig⟩ := exists_nat_gt (max (1 : ℝ) (2 * V / ε))
  have hK : 1 ≤ K := by exact_mod_cast ((le_max_left _ _).trans hKbig.le)
  have hKcut : 2 * V ≤ ε * ((K + 1 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hKbig)
    push_cast
    nlinarith
  obtain ⟨C, hC, Bcore, hcore⟩ := small_component_rate c D M hc hD K hK
  obtain ⟨Blog, hBlog⟩ := ElementaryLogGrowth.log_ge_eventually (2 * C / ε)
  refine ⟨max Bcore (max Blog 2), ?_⟩
  intro B hB S P U R hrows hlower hupper hR hU hlogU hlogR hP hS
  have hBtwo : 2 ≤ B := (le_max_right Blog 2).trans ((le_max_right _ _).trans hB)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hloglo := (hBlog B ((le_max_left Blog 2).trans ((le_max_right _ _).trans hB))).1
  have hsmall := hcore B ((le_max_left _ _).trans hB) S P U R hrows hlower hupper hR hU hlogU hlogR hP
  have hCdiv : C / Real.log B ≤ ε / 2 := by
    apply (div_le_iff₀ hlogB).mpr
    have h := (div_le_iff₀ hε).mp hloglo
    nlinarith
  have hsmall' : ((small S P K).card : ℝ) ≤ (ε / 2) * B := by
    apply hsmall.trans
    calc
      _ = (C / Real.log B) * B := by ring
      _ ≤ (ε / 2) * B := mul_le_mul_of_nonneg_right hCdiv hBpos.le
  have hden : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < K + 1 by omega)
  have hVdiv : V / ((K + 1 : ℕ) : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hdivNat := Nat.div_mul_le_self S.card (K + 1)
  have hdivReal : ((S.card / (K + 1) : ℕ) : ℝ) ≤ (S.card : ℝ) / ((K + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hden).mpr
    exact_mod_cast hdivNat
  have hlarge : ((S.card / (K + 1) : ℕ) : ℝ) ≤ (ε / 2) * B := by
    calc
      _ ≤ (S.card : ℝ) / ((K + 1 : ℕ) : ℝ) := hdivReal
      _ ≤ (V * B) / ((K + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hS hden.le
      _ = (V / ((K + 1 : ℕ) : ℝ)) * B := by ring
      _ ≤ (ε / 2) * B := mul_le_mul_of_nonneg_right hVdiv hBpos.le
  have hrank : (Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows S P)) : ℝ) ≤
      ((small S P K).card : ℝ) + ((S.card / (K + 1) : ℕ) : ℝ) := by
    exact_mod_cast row_rank_le_small_add_large_budget hrows K
  linarith


theorem residual_rank_sublinear (c D M V ε : ℝ) (hc : 0 < c) (hD : 0 < D) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ S P : Finset ℕ, ∀ U R : ℕ,
      (∀ p, (rows S P p).card ≤ 2) →
      (∀ n ∈ S, U ≤ n) → (∀ n ∈ S, n ≤ U + R) →
      1 ≤ R → 2 * R ≤ U → c * B ≤ Real.log U →
      Real.log (64 * (R : ℝ)) ≤ D * Real.log B →
      (P.card : ℝ) + 1 ≤ M * B / Real.log B → (S.card : ℝ) ≤ V * B →
      (Module.finrank F₂ (valueKernel S) : ℝ) ≤ ε * B := by
  obtain ⟨Bcore, hcore⟩ := row_rank_sublinear c D M V ε hc hD hε
  refine ⟨Bcore, ?_⟩
  intro B hB S P U R hrows hlower hupper hR hU hlogU hlogR hP hS
  have hle : (Module.finrank F₂ (valueKernel S) : ℝ) ≤
      Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows S P)) := by
    exact_mod_cast Submodule.finrank_mono (kernel_le_rows S P)
  exact hle.trans (hcore B hB S P U R hrows hlower hupper hR hU hlogU hlogR hP hS)

end PaperP1.ResidualComponentRank
