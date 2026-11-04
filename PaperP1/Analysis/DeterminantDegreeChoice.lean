module

public import PaperP1.Analysis.DeterminantExplicitDecay

/-! # Fixed bounded auxiliary degree choices with a strict uniform logarithmic margin -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantDegreeChoice

def balancedDegree (B : ℕ) (a b : ℝ) : ℕ := ⌈(B : ℝ) * b / a⌉₊

theorem balanced_positive (B : ℕ) (hB : 0 < B) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < balancedDegree B a b := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by exact_mod_cast hB) hb) ha

theorem balanced_lower (B : ℕ) {a b : ℝ} (ha : 0 < a) :
    (B : ℝ) * b ≤ balancedDegree B a b * a := by
  exact (div_le_iff₀ ha).mp (Nat.le_ceil _)

theorem balanced_cost (B : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ((balancedDegree B a b : ℝ) * a + B * b) / 2 ≤ B * b + a / 2 := by
  have hh := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (Nat.cast_nonneg B) hb) ha.le)).le
  change (balancedDegree B a b : ℝ) ≤ (B : ℝ) * b / a + 1 at hh
  have hm := mul_le_mul_of_nonneg_right hh ha.le
  have he : ((B : ℝ) * b / a + 1) * a = (B : ℝ) * b + a := by field_simp
  rw [he] at hm
  linarith only [hm]

theorem balanced_upper (B : ℕ) {a b δ C : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : b ≤ C)
    (hb₀ : 0 ≤ b) : balancedDegree B a b ≤ ⌈(B : ℝ) * C / δ⌉₊ := by
  apply Nat.ceil_mono
  have ha₀ : 0 < a := hδ.trans_le ha
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg B)) ha₀.le).trans
    (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg B) (hb₀.trans hb)) hδ ha)

theorem leading_gain {a b η σ τ A B H : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (hB : 0 ≤ B) (hA : 0 ≤ A) (hH : A * B ≤ H)
    (hbalance : B * b ≤ A * a)
    (hproduct : (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b ≤ σ * τ) :
    (1 + η) * B * b ≤ (2 / 3 : ℝ) * Real.sqrt (2 * H * σ * τ) := by
  have hH₀ : 0 ≤ H := (mul_nonneg hA hB).trans hH
  have hHa : B ^ 2 * b ≤ H * a := by
    have h₁ := mul_le_mul_of_nonneg_left hbalance hB
    have h₂ := mul_le_mul_of_nonneg_right hH ha.le
    nlinarith only [h₁, h₂]
  have h₁ := mul_le_mul_of_nonneg_left hproduct hH₀
  have h₂ := mul_le_mul_of_nonneg_right hHa (mul_nonneg (sq_nonneg (1 + η)) hb)
  have hrad : 0 ≤ 2 * H * σ * τ := by
    have hp : 0 ≤ σ * τ := (by positivity : 0 ≤ (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b).trans hproduct
    nlinarith only [mul_nonneg hH₀ hp]
  have hs : ((1 + η) * B * b) ^ 2 ≤ ((2 / 3 : ℝ) * Real.sqrt (2 * H * σ * τ)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hrad]
    nlinarith only [h₁, h₂]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs

theorem exists_uniform_degrees (δ C W η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B Amax : ℕ, 0 < B ∧ ∀ a b σ τ : ℝ,
      δ ≤ a → a ≤ C → δ ≤ b → b ≤ C → 0 < σ → 0 < τ → σ + τ ≤ W →
      (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b ≤ σ * τ →
      ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧
        ((A : ℝ) * a + B * b) / 2 + (σ + τ) + 1 ≤
          (2 / 3 : ℝ) * Real.sqrt (2 * ((A + 1) * (B + 1) : ℕ) * σ * τ) := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max 1 ((W + C / 2 + 1) / (η * δ)))
  have hB₀ : 0 < B := by have hb : (1 : ℝ) < B := (le_max_left _ _).trans_lt hB; exact_mod_cast (by linarith only [hb] : (0 : ℝ) < B)
  have hbudget : W + C / 2 + 1 ≤ η * (B : ℝ) * δ := by
    have hh := (le_max_right _ _).trans hB.le
    have hm := (div_le_iff₀ (mul_pos hη hδ)).mp hh
    nlinarith only [hm]
  refine ⟨B, ⌈(B : ℝ) * C / δ⌉₊, hB₀, ?_⟩
  intro a b σ τ hδa haC hδb hbC hσ hτ hweights hproduct
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := hδ.trans_le hδb
  let A := balancedDegree B a b
  have hAr : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hBr : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcap : (A : ℝ) * B ≤ (((A + 1) * (B + 1) : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hAr, hBr]
  have hlead := leading_gain ha hb.le hη.le hBr hAr hcap (balanced_lower B ha) hproduct
  refine ⟨A, balanced_positive B hB₀ ha hb, balanced_upper B hδ hδa hbC hb.le, ?_⟩
  have hcost := balanced_cost B ha hb.le
  have hsurplus := mul_le_mul_of_nonneg_left hδb (mul_nonneg hη.le (Nat.cast_nonneg B))
  dsimp only [A] at hlead ⊢
  nlinarith only [hcost, hsurplus, hbudget, haC, hweights, hlead]

end PaperP1.DeterminantDegreeChoice
