module

public import PaperP1.Analysis.CurveDegreeAsymptotics
public import PaperP1.Arithmetic.IntegerGridTheorem

/-! # Actual plane-polynomial grids and the explicitly conditional BCN consequence

The property `UniformBound` records the degree-uniform plane-polynomial specialization of
arXiv:2302.04209v2, Theorem 2, equation (27). Its positive witness with exponent 17 is proved
internally by `QuadraticPlaneUniformBound.uniform_bound`. The consequences below take a
witness as an explicit argument for reuse; the complete original-field affine curve theorem
is `IntegralAffineCurvePointCount.article_13_4`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneCurvePointCount

open Polynomial Finset Filter PaperP1.CurveDegreeProfile PaperP1.CurveDegreeAsymptotics
  PaperP1.CurveIntegerFibres

def degree {R : Type*} [Semiring R] (P : R[X][X]) : ℕ :=
  P.support.sup (fun y ↦ y + (P.coeff y).natDegree)

def grid {R : Type*} [Ring R] (P : R[X][X]) (B : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((offsetBox B) ×ˢ (offsetBox B)).filter (fun p ↦ P.evalEval (p.1 : R) (p.2 : R) = 0)

theorem mem_grid {R : Type*} [Ring R] (P : R[X][X]) (B : ℕ) (p : ℤ × ℤ) :
    p ∈ grid P B ↔ |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ) ∧ P.evalEval (p.1 : R) (p.2 : R) = 0 := by
  classical
  simp only [grid, mem_filter, mem_product, mem_offsetBox, and_assoc]

theorem mem_real_grid {R : Type*} [Ring R] (P : R[X][X]) (H : ℝ) (hH : 0 ≤ H) (p : ℤ × ℤ) :
    p ∈ grid P ⌊H⌋₊ ↔ |(p.1 : ℝ)| ≤ H ∧ |(p.2 : ℝ)| ≤ H ∧ P.evalEval (p.1 : R) (p.2 : R) = 0 := by
  rw [mem_grid, ← mem_offsetBox, ← mem_offsetBox,
    IntegerGridTheorem.floor_box_iff H hH, IntegerGridTheorem.floor_box_iff H hH]

theorem degree_integer (P : ℤ[X][X]) : degree P = BivariateTotalDegree.totalDegree P := rfl

theorem integer_grid_card (P : ℤ[X][X]) (B : ℕ) : (integerGrid P B).card = (grid P B).card := by
  classical
  apply card_bij (fun p _hp ↦ (-p.1, -p.2))
  · intro p hp
    obtain ⟨hl, hr, he⟩ := (mem_integerGrid P B p).mp hp
    exact (mem_grid P B _).mpr ⟨by simpa only [abs_neg] using hl, by simpa only [abs_neg] using hr, he⟩
  · intro p _hp q _hq he
    apply Prod.ext
    · exact neg_injective (congrArg Prod.fst he)
    · exact neg_injective (congrArg Prod.snd he)
  · intro p hp
    obtain ⟨hl, hr, he⟩ := (mem_grid P B p).mp hp
    refine ⟨(-p.1, -p.2), (mem_integerGrid P B _).mpr ?_, ?_⟩
    · exact ⟨by simpa only [abs_neg] using hl, by simpa only [abs_neg] using hr,
        by simpa using he⟩
    · simp

def UniformBound (c κ : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
    0 < degree P → ∀ H : ℝ, 2 < H →
      ((grid P ⌊H⌋₊).card : ℝ) ≤ c * profile H (degree P : ℝ) * Real.log H ^ κ

theorem finite_bound (c κ : ℝ) (hc : 0 ≤ c) (hBCN : UniformBound c κ)
    (K : Type) [Field K] [CharZero K] [Algebra K ℂ] (P : K[X][X]) (hP : Irreducible P)
    (H M : ℝ) (hH : 2 < H) (hD : 2 ≤ degree P) (hDM : (degree P : ℝ) ≤ M)
    (hlog : Real.log H ≤ M) :
    ((grid P ⌊H⌋₊).card : ℝ) ≤
      c * (4 * H ^ (1 / 2 : ℝ) + Real.exp 1 * M ^ 2) * Real.log H ^ κ := by
  have hbound := hBCN K P hP (by omega) H hH
  have hp := degree_uniform_bound H (degree P : ℝ) M (by linarith) (by exact_mod_cast hD) hDM hlog
  exact hbound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc)
    (Real.rpow_nonneg (Real.log_nonneg (by linarith)) κ))

theorem uniform_sublinear_under_BCN (c κ c₀ b : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hb : 0 < b) (hb₁ : b < 1 / 2) (hBCN : UniformBound c κ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ degree P → (degree P : ℝ) ≤ (B : ℝ) ^ b →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B := by
  obtain ⟨B₁, hB₁, hprofile⟩ := uniform_sublinear c₀ b κ hc₀ hb hb₁ (ε / c) (div_pos hε hc)
  obtain ⟨B₂, hB₂, hheight⟩ := logarithmic_weights_eventually c₀ κ hc₀
  refine ⟨max B₁ B₂, by omega, ?_⟩
  intro B hB K _hK _hchar _halg P hP hD hDM
  have hH := (hheight B (by omega)).1
  have hbound := hBCN K P hP (by omega) (c₀ * B) hH
  have hsmall := hprofile B (by omega) (degree P : ℝ) (by exact_mod_cast hD) hDM
  calc
    ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ c * (profile (c₀ * B) (degree P : ℝ) * Real.log (c₀ * B) ^ κ) := by
      simpa only [mul_assoc] using hbound
    _ ≤ c * ((ε / c) * B) := mul_le_mul_of_nonneg_left hsmall hc.le
    _ = ε * B := by field_simp

def UpperPowerCap (a : ℝ) (cap : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ B₀ : ℕ, ∀ B ≥ B₀, cap B ≤ (B : ℝ) ^ (a + δ)

theorem upperPowerCap_of_log_ratio (a : ℝ) (cap : ℕ → ℝ)
    (hpos : ∀ᶠ B : ℕ in atTop, 0 < cap B)
    (hratio : Tendsto (fun B : ℕ ↦ Real.log (cap B) / Real.log B) atTop (nhds a)) :
    UpperPowerCap a cap := by
  intro δ hδ
  have hsmall := hratio.eventually (eventually_lt_nhds (by linarith : a < a + δ))
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp (hpos.and hsmall)
  refine ⟨max 2 B₀, ?_⟩
  intro B hB
  obtain ⟨hp, hs⟩ := hB₀ B (by omega)
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  exact (Real.le_rpow_iff_log_le hp hBp).mpr ((div_lt_iff₀ hlog).mp hs).le

theorem growing_degree_under_BCN (c κ c₀ a : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀)
    (ha : 0 ≤ a) (ha₁ : a < 1 / 2) (hBCN : UniformBound c κ)
    (cap : ℕ → ℝ) (hcap : UpperPowerCap a cap) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ degree P → (degree P : ℝ) ≤ cap B →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B := by
  let δ : ℝ := (1 / 2 - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨B₁, hB₁⟩ := hcap δ hδ
  obtain ⟨B₂, hB₂, hsmall⟩ := uniform_sublinear_under_BCN c κ c₀ (a + δ) hc hc₀
    (by linarith) (by dsimp [δ]; linarith) hBCN ε hε
  refine ⟨max B₁ B₂, by omega, ?_⟩
  intro B hB K _hK _hchar _halg P hP hD hDM
  exact hsmall B (by omega) K P hP hD (hDM.trans (hB₁ B (by omega)))

theorem source_uniform_bound_under_BCN (c κ c₀ : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hBCN : UniformBound c κ) :
    ∃ A : ℝ, 0 < A ∧ ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ M : ℝ,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ degree P → (degree P : ℝ) ≤ M →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ A * ((B : ℝ) ^ (1 / 2 : ℝ) + M ^ 2) * Real.log B ^ κ := by
  obtain ⟨B₁, hB₁, hweights⟩ := logarithmic_weights_eventually c₀ κ hc₀
  have hs := ((PNT.tendsto_pow_log_div_pow_atTop (1 / 2) 2 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  obtain ⟨B₂, hB₂⟩ := eventually_atTop.mp hs
  let A₀ : ℝ := 4 * c₀ ^ (1 / 2 : ℝ) + Real.exp 1
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  refine ⟨2 * c * A₀, by positivity, max B₁ B₂, by omega, ?_⟩
  intro B hB M K _hK _hchar _halg P hP hD hDM
  obtain ⟨hH, hlog, hweight⟩ := hweights B (by omega)
  have hBtwo : 2 ≤ B := by omega
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hHlog : 0 ≤ Real.log (c₀ * B) := Real.log_nonneg (by linarith)
  have hsmall : Real.log B ^ 2 / (B : ℝ) ^ (1 / 2 : ℝ) ≤ 1 / 4 := by
    simpa only [Real.rpow_two, Function.comp_def] using (hB₂ B (by omega)).le
  have hlogpow := pow_le_pow_left₀ hHlog hlog 2
  have hlogpow' : Real.log (c₀ * B) ^ 2 ≤ (B : ℝ) ^ (1 / 2 : ℝ) := by
    have hm := (div_le_iff₀ (Real.rpow_pos_of_pos hBp (1 / 2))).mp hsmall
    nlinarith
  have hdegree := degree_uniform_bound_without_cap_growth (c₀ * B) (degree P : ℝ) M
    (by linarith) (by exact_mod_cast hD) hDM
  rw [Real.mul_rpow hc₀.le hBp.le] at hdegree
  have hp : profile (c₀ * B) (degree P : ℝ) ≤ A₀ * ((B : ℝ) ^ (1 / 2 : ℝ) + M ^ 2) := by
    have he := mul_le_mul_of_nonneg_left hlogpow' (Real.exp_pos 1).le
    dsimp [A₀]
    have hm : 0 ≤ 4 * c₀ ^ (1 / 2 : ℝ) * M ^ 2 := by positivity
    nlinarith
  have hw := mul_le_mul hp hweight (Real.rpow_nonneg hHlog κ) (by positivity)
  have hbound := hBCN K P hP (by omega) (c₀ * B) hH
  calc
    ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ c * (profile (c₀ * B) (degree P : ℝ) * Real.log (c₀ * B) ^ κ) := by
      simpa only [mul_assoc] using hbound
    _ ≤ c * (A₀ * ((B : ℝ) ^ (1 / 2 : ℝ) + M ^ 2) * (2 * Real.log B ^ κ)) :=
      mul_le_mul_of_nonneg_left hw hc.le
    _ = (2 * c * A₀) * ((B : ℝ) ^ (1 / 2 : ℝ) + M ^ 2) * Real.log B ^ κ := by ring

theorem article_13_5_under_BCN (c κ c₀ a : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀)
    (ha : 0 ≤ a) (ha₁ : a < 1 / 2) (hBCN : UniformBound c κ)
    (cap : ℕ → ℝ) (hcap : UpperPowerCap a cap) :
    (∃ A : ℝ, 0 < A ∧ ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ degree P → (degree P : ℝ) ≤ cap B →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤
          A * ((B : ℝ) ^ (1 / 2 : ℝ) + cap B ^ 2) * Real.log B ^ κ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ degree P → (degree P : ℝ) ≤ cap B →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B) := by
  constructor
  · obtain ⟨A, hA, B₀, hB₀, hbound⟩ := source_uniform_bound_under_BCN c κ c₀ hc hc₀ hBCN
    exact ⟨A, hA, B₀, hB₀, fun B hB K _hK _hchar _halg P hP hD hDM ↦
      hbound B hB (cap B) K P hP hD hDM⟩
  · exact fun ε hε ↦ growing_degree_under_BCN c κ c₀ a hc hc₀ ha ha₁ hBCN cap hcap ε hε

end PaperP1.PlaneCurvePointCount
