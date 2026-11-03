module

public import PaperP1.Arithmetic.TernaryPrimeCounts
public import PaperP1.Asymptotics.TernaryGroupScales

/-! # The weak individual-prime product count at the literal critical scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeWeakCritical

open Finset PaperP1.TernaryPrimeTopProducts

theorem uniform_bound (C : ℝ) (D k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ) (T V : ℝ), 1 ≤ T → 0 ≤ V →
      (∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + D * N)) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, 0 < n ∧ n ≤ D * N ∧ ((n : ℤ) - X i).natAbs ≤ R) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) k : ℝ) ∧ (topProduct (U X) (H X) k : ℝ) ≤ V) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + V) := by
  let δ := ε / 2
  let c : ℝ := 8 * (D : ℝ) ^ 3 + 4
  obtain ⟨NW, _hNW, hw⟩ := TernaryPrimeCounts.weak_uniform k (2 * k) δ (by dsimp [δ]; positivity)
  obtain ⟨NP, _hNP, hp⟩ := TernaryGroupScales.radius_length_factor C D c (by dsimp [c]; positivity)
    (3 * k) 0 δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max D (max NW NP)), by omega, ?_⟩
  intro N hN L R hband hR F U H base T V hT hV hbox hvalues hprod
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hheight (X : Fin 3 → ℕ) (hX : X ∈ F) : topProduct (U X) (H X) k ≤ N ^ (2 * k) := by
    calc
      _ ≤ (D * N) ^ k := top_product_le_height (U X) (H X) k (D * N)
        (fun i n hn ↦ (hvalues X hX i n hn).1) (fun i n hn ↦ (hvalues X hX i n hn).2.1)
      _ ≤ (N ^ 2) ^ k := Nat.pow_le_pow_left (by nlinarith [show D ≤ N by omega]) k
      _ = _ := (pow_mul _ _ _).symm
  have hweak := hw N (by omega) F U H base (D * N) R T V hT hV hbox
    (fun X hX i n hn ↦ (hvalues X hX i n hn).2.2)
    (fun X hX ↦ ⟨(hprod X hX).1, (hprod X hX).2, hheight X hX⟩)
  have hpoly : c * (2 * R + 1 : ℕ) ^ (3 * k) ≤ (N : ℝ) ^ δ := by
    simpa only [pow_zero, mul_one] using hp N (by omega) L R hband hR
  have hbracket : 8 * (D * N : ℕ) ^ 3 * T ^ (-2 : ℝ) + 4 * V ≤
      c * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + V) := by
    dsimp [c]
    push_cast
    nlinarith [mul_nonneg (by positivity : 0 ≤ 8 * (D : ℝ) ^ 3) hV,
      mul_nonneg (by positivity : 0 ≤ (N : ℝ) ^ 3) (Real.rpow_nonneg (by linarith : 0 ≤ T) (-2))]
  calc
    _ ≤ (N : ℝ) ^ δ * (2 * R + 1 : ℕ) ^ (3 * k) *
        (c * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + V)) := hweak.trans
      (mul_le_mul_of_nonneg_left hbracket (by positivity))
    _ = (N : ℝ) ^ δ * (c * (2 * R + 1 : ℕ) ^ (3 * k)) *
        ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + V) := by ring
    _ ≤ ((N : ℝ) ^ δ * (N : ℝ) ^ δ) * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + V) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; dsimp [δ]; ring

end PaperP1.TernaryPrimeWeakCritical
