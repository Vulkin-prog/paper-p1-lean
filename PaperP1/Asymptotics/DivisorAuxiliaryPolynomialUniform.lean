module

public import PaperP1.Arithmetic.DivisorAuxiliaryPolynomial
public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # The auxiliary degree is fixed before the scale and every divisor configuration

This proves the polynomial construction in companion T8.1 without a geometric
input. The later count of points on its components is not asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DivisorAuxiliaryPolynomialUniform

universe u

open Finset Polynomial PaperP1.RectangularEvaluationPolynomial PaperP1.CriticalBandScale

theorem choose_degree (τ : ℝ) (hτ : 0 < τ) :
    ∃ d : ℕ, 1 ≤ d ∧ 2 * (d : ℝ) < τ * ((Fintype.card (Index d) - 1 : ℕ) : ℝ) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (2 / τ)
  have hdτ : (2 : ℝ) < (d : ℝ) * τ := (div_lt_iff₀ hτ).mp hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hdNat : 1 ≤ d := by
    have hp : 0 < d := by exact_mod_cast hdpos
    omega
  have hcard : Fintype.card (Index d) - 1 = d * d + 2 * d := by
    simp only [Index, Fintype.card_prod, Fintype.card_fin]
    have he : (d + 1) * (d + 1) = (d * d + 2 * d) + 1 := by ring
    rw [he, Nat.add_sub_cancel]
  refine ⟨d, hdNat, ?_⟩
  rw [hcard]
  push_cast
  nlinarith only [hdτ, hdpos, hτ]

theorem uniform_height (d A K : ℕ) (C τ : ℝ)
    (hgap : 2 * (d : ℝ) < τ * ((Fintype.card (Index d) - 1 : ℕ) : ℝ)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (((Fintype.card (Index d)).factorial * (A * N) ^ (2 * d) *
        ((K * (L + 1)) ^ (2 * d)) ^ (Fintype.card (Index d) - 1) : ℕ) : ℝ) <
          ((N : ℝ) ^ τ) ^ (Fintype.card (Index d) - 1) := by
  let m := Fintype.card (Index d) - 1
  let k := 2 * d * m
  let a : ℝ := ((Fintype.card (Index d)).factorial : ℝ) * (A : ℝ) ^ (2 * d) * (K : ℝ) ^ k
  let δ := (τ * (m : ℝ) - 2 * (d : ℝ)) / 2
  have hδ : 0 < δ := by dsimp [δ, m]; linarith only [hgap]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le a k δ hδ
  obtain ⟨NS, hs⟩ := critical_band_scale C
  refine ⟨max 2 (max NP NS), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpoly := hp N (by omega) L (hs N (by omega) L hband).2
  rw [abs_of_nonneg (mul_nonneg ha (by positivity))] at hpoly
  have heq : (((Fintype.card (Index d)).factorial * (A * N) ^ (2 * d) *
        ((K * (L + 1)) ^ (2 * d)) ^ m : ℕ) : ℝ) =
      (a * (L + 1 : ℝ) ^ k) * (N : ℝ) ^ (2 * d) := by
    dsimp [a, k]
    push_cast
    simp only [mul_pow, ← pow_mul]
    ring
  change _ < ((N : ℝ) ^ τ) ^ m
  rw [heq, ← Real.rpow_mul_natCast hn.le]
  calc
    _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (2 * d) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (N : ℝ) ^ (δ + 2 * (d : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn]
      push_cast
      rfl
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt hn1 (by
      dsimp only [δ] at hδ ⊢
      linarith only [hδ])

theorem uniform_polynomial (C τ : ℝ) (hτ : 0 < τ) (A K : ℕ)
    (hA : 1 ≤ A) (hK : 1 ≤ K) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u),
      ∀ x y : ℤ, x.natAbs ≤ A * N → y.natAbs ≤ A * N →
      ∀ s t : ι → ℤ, ∀ g : ι → ℕ,
      Pairwise (fun i j ↦ (g i).Coprime (g j)) →
      (∀ i, (s i).natAbs ≤ K * (L + 1)) → (∀ i, (t i).natAbs ≤ K * (L + 1)) →
      (∀ i, (g i : ℤ) ∣ x + s i) → (∀ i, (g i : ℤ) ∣ y + t i) →
      (∀ i, (N : ℝ) ^ τ ≤ (g i : ℝ)) →
      ∃ P : ℚ[X][X], P ≠ 0 ∧ P.natDegree ≤ d ∧ (∀ b, (P.coeff b).natDegree ≤ d) ∧
        P.support.sup (fun b ↦ b + (P.coeff b).natDegree) ≤ 2 * d ∧
        ∀ i, P.evalEval (s i : ℚ) (t i : ℚ) = 0 := by
  obtain ⟨d, hd, hgap⟩ := choose_degree τ hτ
  obtain ⟨N₀, hN₀, hh⟩ := uniform_height d A K C τ hgap
  refine ⟨d, hd, N₀, hN₀, ?_⟩
  intro N hN L hband ι x y hx hy s t g hcop hs ht hdivs hdivt hlarge
  exact DivisorAuxiliaryPolynomial.finite_confinement d (K * (L + 1)) (A * N)
    (by nlinarith) (by nlinarith) x y hx hy s t g ((N : ℝ) ^ τ) (by positivity)
    hcop hs ht hdivs hdivt hlarge (hh N hN L hband)

end PaperP1.DivisorAuxiliaryPolynomialUniform
