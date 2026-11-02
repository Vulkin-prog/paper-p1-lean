module

public import PaperP1.Model.HeterogeneousRunConversion
public import PaperP1.Model.TripleRankGeometry

/-! # Uniform conversion with actual heterogeneous marginals and explicit pair mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousRunConversionAsymptotic

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.HeterogeneousBernoulli PaperP1.HeterogeneousPoissonCharlierConversion
  PaperP1.HeterogeneousRunConversion

theorem powerSum_succ_le {ι : Type*} (G : Finset ι) (p : ι → ℝ) {P : ℝ}
    (hp : ∀ i ∈ G, 0 ≤ p i) (hcap : ∀ i ∈ G, p i ≤ P) (r : ℕ) :
    powerSum G p (r + 1) ≤ P ^ r * mean G p := by
  rw [powerSum, mean, mul_sum]
  apply sum_le_sum
  intro i hi
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hp i hi) (hcap i hi) r) (hp i hi)

def meanCap (C : ℝ) : ℝ := 2 * (2 : ℝ) ^ C

def errorConstant (C : ℝ) : ℝ := constant (meanCap C) *
  ((meanCap C) ^ 3 + (meanCap C) ^ 4 + meanCap C + (meanCap C) ^ 2)

theorem meanCap_pos (C : ℝ) : 0 < meanCap C := by unfold meanCap; positivity

theorem errorConstant_pos (C : ℝ) : 0 < errorConstant C := by
  have h := meanCap_pos C
  have hc := constant_pos (meanCap C)
  unfold errorConstant
  positivity

theorem uniform_actual_bound (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
        QuadraticPoisson.reference (countMoment G L 1)
          (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
        errorConstant C * (1 / (N : ℝ) ^ 2 + absoluteMass G L / N) := by
  obtain ⟨N₀, hcap⟩ := TripleRankGeometry.critical_nominal_marginal_cap C
  refine ⟨max 2 N₀, by omega, ?_⟩
  intro N hN L hband G hG
  let K := meanCap C
  let P := K / N
  let p := fun x ↦ infiniteMarginal x L
  let s₂ := powerSum G p 2
  let s₃ := powerSum G p 3
  let A₂ := absoluteMass G L
  have hK : 0 < K := meanCap_pos C
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hP : 0 ≤ P := div_nonneg hK.le hNpos.le
  have hp : ∀ x ∈ G, 0 ≤ p x := fun x _ ↦ (marginal_bounds x L).1
  have hpoint : ∀ x ∈ G, p x ≤ P := by
    intro x hx
    calc
      _ ≤ 2 * (2 ^ L : ℝ)⁻¹ := hcap N (by omega) L hband x (hG hx)
      _ ≤ 2 * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hband) (by norm_num)
      _ = _ := by dsimp only [P, K, meanCap]; ring
  have hcard : (G.card : ℝ) ≤ N := by
    exact_mod_cast (card_le_card hG).trans_eq (RegularSetFinite.card_dyadicBlock N)
  have hmean : countMoment G L 1 ≤ K := by
    rw [countMoment_one hG]
    calc
      _ ≤ ∑ _x ∈ G, P := sum_le_sum hpoint
      _ = (G.card : ℝ) * P := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * P := mul_le_mul_of_nonneg_right hcard hP
      _ = K := by dsimp only [P]; field_simp
  have hmean' : mean G p ≤ K := by
    change (∑ x ∈ G, infiniteMarginal x L) ≤ K
    simpa only [countMoment_one hG] using hmean
  have hs₂ : s₂ ≤ K ^ 2 / N := by
    calc
      _ ≤ P ^ 1 * mean G p := powerSum_succ_le G p hp hpoint 1
      _ ≤ P * K := by simpa only [pow_one] using mul_le_mul_of_nonneg_left hmean' hP
      _ = _ := by dsimp only [P]; ring
  have hs₃ : s₃ ≤ K ^ 3 / (N : ℝ) ^ 2 := by
    calc
      _ ≤ P ^ 2 * mean G p := powerSum_succ_le G p hp hpoint 2
      _ ≤ P ^ 2 * K := mul_le_mul_of_nonneg_left hmean' (sq_nonneg P)
      _ = _ := by dsimp only [P]; ring
  have hs₂pos : 0 ≤ s₂ := powerSum_nonneg G p hp 2
  have hs₂square : s₂ ^ 2 ≤ K ^ 4 / (N : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hs₂pos hs₂ 2
    convert h using 1; ring
  have hsum : s₃ + s₂ ^ 2 ≤ (K ^ 3 + K ^ 4) / (N : ℝ) ^ 2 := by
    rw [add_div]; exact add_le_add hs₃ hs₂square
  have hlinear : s₂ + P ≤ (K + K ^ 2) / N := by
    calc
      _ ≤ K ^ 2 / N + K / N := add_le_add hs₂ le_rfl
      _ = _ := by ring
  have hA₂ : 0 ≤ A₂ := absoluteMass_nonneg G L
  have hc : 0 ≤ constant K := (constant_pos K).le
  have hfinite := HeterogeneousRunConversion.actual_signed_measure_conversion hG hP hpoint hmean
  have herr : constant K * (s₃ + s₂ ^ 2 + A₂ * (s₂ + P)) ≤
      constant K * ((K ^ 3 + K ^ 4) / (N : ℝ) ^ 2 + A₂ * ((K + K ^ 2) / N)) := by gcongr
  have hcross₁ : 0 ≤ constant K * ((K + K ^ 2) / (N : ℝ) ^ 2) := by positivity
  have hcross₂ : 0 ≤ constant K * (A₂ * ((K ^ 3 + K ^ 4) / N)) := by positivity
  change _ ≤ constant K * (K ^ 3 + K ^ 4 + K + K ^ 2) * (1 / (N : ℝ) ^ 2 + A₂ / N)
  change _ ≤ constant K * (s₃ + s₂ ^ 2 + A₂ * (s₂ + P)) at hfinite
  simp only [div_eq_mul_inv] at herr hcross₁ hcross₂ ⊢
  nlinarith only [hfinite, herr, hcross₁, hcross₂]

end PaperP1.HeterogeneousRunConversionAsymptotic
