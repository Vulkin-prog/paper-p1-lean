module

public import PaperP1.Probability.PolynomialWeightTransfer
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Polynomial weights for arbitrary nonnegative sequences

The unweighted bound is needed only at epsilon/4. In particular, a finite
arithmetic input bundle can be chosen before the polynomial degree.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialWeightedSequenceRate

variable {ι : Type*}

structure MomentBounds (w a b : ι → ℝ) (r : ℕ) (P : ℝ) : Prop where
  left_nonneg : ∀ v, 0 ≤ a v
  right_nonneg : ∀ v, 0 ≤ b v
  left_summable : Summable (fun v ↦ a v * w v ^ r)
  right_summable : Summable (fun v ↦ b v * w v ^ r)
  left_bound : (∑' v, a v * w v ^ r) ≤ P
  right_bound : (∑' v, b v * w v ^ r) ≤ P

theorem uniform_bound (A B : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (hw : ∀ v, 1 ≤ w v) (C α ε : ℝ) (hε : 0 < ε)
    (hNorm : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Summable (fun v ↦ |A N L v - B N L v|) ∧
      (∑' v, |A N L v - B N L v|) ≤ (N : ℝ) ^ (-α + ε / 4))
    (hMom : ∀ r : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      MomentBounds w (A N L) (B N L) r ((N : ℝ) ^ δ)) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Summable (fun v ↦ w v ^ j * |A N L v - B N L v|) ∧
      (∑' v, w v ^ j * |A N L v - B N L v|) ≤
        (N : ℝ) ^ (-α + ε) := by
  intro j
  let δ : ℝ := ε / (4 * (j + 1 : ℕ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδj : δ * (j : ℝ) ≤ ε / 4 := by
    have he : δ * ((j + 1 : ℕ) : ℝ) = ε / 4 := by dsimp [δ]; field_simp
    have hjr : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
    exact (mul_le_mul_of_nonneg_left hjr hδ.le).trans_eq he
  obtain ⟨q, hq⟩ := exists_nat_gt ((α + 1) / δ)
  have hδq : α + 1 ≤ δ * (q : ℝ) := by
    have hh := (div_lt_iff₀ hδ).mp hq
    linarith only [hh]
  obtain ⟨NN, hn⟩ := hNorm
  obtain ⟨NM, hm⟩ := hMom (j + q) (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-α + ε / 2) (ε / 2) (by positivity)
  refine ⟨2 + NN + NM + NF, by omega, ?_⟩
  intro N hN L hband
  let a := A N L
  let b := B N L
  let R := (N : ℝ) ^ δ
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 0 < R := Real.rpow_pos_of_pos hnpos δ
  have hM := hm N (by omega) L hband
  have hsa : Summable (fun v ↦ w v ^ (j + q) * a v) := by
    simpa only [a, mul_comm] using hM.left_summable
  have hsb : Summable (fun v ↦ w v ^ (j + q) * b v) := by
    simpa only [b, mul_comm] using hM.right_summable
  have hMa : (∑' v, w v ^ (j + q) * a v) ≤ (N : ℝ) ^ (ε / 4) := by
    simpa only [a, mul_comm] using hM.left_bound
  have hMb : (∑' v, w v ^ (j + q) * b v) ≤ (N : ℝ) ^ (ε / 4) := by
    simpa only [b, mul_comm] using hM.right_bound
  have hs0 : Summable (fun v ↦ |a v - b v|) := (hn N (by omega) L hband).1
  have hnorm : (∑' v, |a v - b v|) ≤ (N : ℝ) ^ (-α + ε / 4) :=
    (hn N (by omega) L hband).2
  have hs := PolynomialWeightTransfer.summable_weighted_error w a b hw
    hM.left_nonneg hM.right_nonneg j q hsa hsb
  have hcut := PolynomialWeightTransfer.cutoff_bound w a b hw
    hM.left_nonneg hM.right_nonneg j q R hR hs0 hsa hsb
  have hsmall : R ^ j * (∑' v, |a v - b v|) ≤ (N : ℝ) ^ (-α + ε / 2) := by
    calc
      _ ≤ R ^ j * (N : ℝ) ^ (-α + ε / 4) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg hR.le j)
      _ = (N : ℝ) ^ (δ * (j : ℝ) + (-α + ε / 4)) := by
        dsimp only [R]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδj])
  have htail : (R ^ q)⁻¹ * ((∑' v, w v ^ (j + q) * a v) +
      ∑' v, w v ^ (j + q) * b v) ≤ 2 * (N : ℝ) ^ (-α + ε / 2) := by
    calc
      _ ≤ (R ^ q)⁻¹ * (2 * (N : ℝ) ^ (ε / 4)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hMa, hMb]) (by positivity)
      _ = 2 * (N : ℝ) ^ (-(δ * (q : ℝ)) + ε / 4) := by
        dsimp only [R]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_neg hnpos.le,
          mul_left_comm, ← Real.rpow_add hnpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδq, hε])) (by norm_num)
  have hfinal : (∑' v, w v ^ j * |a v - b v|) ≤ (N : ℝ) ^ (-α + ε) := by
    have hfactor : 3 * (N : ℝ) ^ (-α + ε / 2) ≤ (N : ℝ) ^ (-α + ε) := by
      convert hf N (by omega) using 1
      congr 1
      ring
    linarith only [hcut, hsmall, htail, hfactor]
  exact ⟨hs, hfinal⟩

end PaperP1.PolynomialWeightedSequenceRate
