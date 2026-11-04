module

public import PaperP1.Asymptotics.EffectiveCompressedPrimitiveCount
public import PaperP1.Asymptotics.HomogeneousChannelWeights
public import PaperP1.Asymptotics.HomogeneousLocalMarginalCap
public import PaperP1.Model.HomogeneousCompressedEffectiveFactor

/-! # Elementary compressed primitive mass for all effective dyadic targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveCompressedPrimitiveElementaryMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PairCompressedPrimitiveFamilies
  PaperP1.EffectiveCompressedPrimitivePopulation

theorem uniform_point (t a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (C η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p ∈ points N a b L t, (nullity p.1 L p.2 : ℝ) ≤ η * L →
      HomogeneousRunMass.probability L (family p.1 p.2) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) - t + η + ε) := by
  let K := (2 * (2 : ℝ) ^ C) ^ t * (2 : ℝ) ^ (η * C)
  obtain ⟨NP, _hNP, hp⟩ := HomogeneousChannelWeights.uniform_pair C (ε / 2) a b ha hab hcop (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := HomogeneousLocalMarginalCap.uniform_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K
    (-2 + 1 / (b : ℝ) - t + η + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NP (max NM NF)), by omega, ?_⟩
  intro N hN L hband p hpF hρ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdata := mem_points.mp hpF
  have hnom : (∏ i, HomogeneousRunMass.probability L {p.2 i}) ≤
      (2 * (2 : ℝ) ^ C) ^ t * (N : ℝ) ^ (-(t : ℝ)) := by
    calc
      _ ≤ ∏ _i : Fin t, (2 * (2 : ℝ) ^ C / N) :=
        prod_le_prod₀ (fun i _ ↦ (HomogeneousRunMass.probability_pos L {p.2 i}).le)
          (fun i _ ↦ hm N (by omega) L hband (p.2 i) (hdata.2.1 i))
      _ = _ := by
        rw [prod_const, card_univ, Fintype.card_fin, div_pow,
          Real.rpow_neg hn.le, Real.rpow_natCast, div_eq_mul_inv]
  have hbinary : (2 ^ nullity p.1 L p.2 : ℝ) ≤ (2 : ℝ) ^ (η * C) * (N : ℝ) ^ η := by
    calc
      _ = (2 : ℝ) ^ (nullity p.1 L p.2 : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (η * L) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ
      _ ≤ _ := WeakPairActivityAsymptotic.critical_binary_power (by omega) hband η hη
  calc
    _ = HomogeneousRunMass.probability L {p.1.1, p.1.2} * (∏ i, HomogeneousRunMass.probability L {p.2 i}) *
        (2 ^ nullity p.1 L p.2 : ℝ) := HomogeneousCompressedEffectiveFactor.factor p.1 p.2
    _ ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) *
        ((2 * (2 : ℝ) ^ C) ^ t * (N : ℝ) ^ (-(t : ℝ))) *
        ((2 : ℝ) ^ (η * C) * (N : ℝ) ^ η) :=
      mul_le_mul (mul_le_mul (hp N (by omega) L hband p.1 hdata.1) hnom
        (prod_nonneg fun i _ ↦ (HomogeneousRunMass.probability_pos L {p.2 i}).le) (by positivity)) hbinary (by positivity) (by positivity)
    _ = K * (N : ℝ) ^ (-2 + 1 / (b : ℝ) - t + η + ε / 2) := by
      conv_rhs => rw [show -2 + 1 / (b : ℝ) - t + η + ε / 2 =
        (-2 + 1 / (b : ℝ) + ε / 2) + (-(t : ℝ)) + η by ring,
        Real.rpow_add hn, Real.rpow_add hn]
      dsimp [K]
      ring
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) - t + η + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_sector (t a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset ((ℕ × ℕ) × (Fin t → ℕ)), F ⊆ points N a b L t →
      (∀ p ∈ F, (nullity p.1 L p.2 : ℝ) ≤ η * L) →
      (∑ p ∈ F, HomogeneousRunMass.probability L (family p.1 p.2)) ≤
        (N : ℝ) ^ (-3 / 2 + 1 / (b : ℝ) - (t : ℝ) / 2 + η + ε) := by
  classical
  obtain ⟨NC, _hNC, hc⟩ := EffectiveCompressedPrimitiveCount.uniform_count t a b ha hab.le hb hb4 C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := uniform_point t a b ha hab hcop C η (ε / 2) hη (by positivity)
  refine ⟨max 2 (max NC NP), by omega, ?_⟩
  intro N hN L hband F hF hρ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : (F.card : ℝ) ≤ (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε / 2) :=
    (show (F.card : ℝ) ≤ (points N a b L t).card by exact_mod_cast card_le_card hF).trans
      (hc N (by omega) L hband)
  calc
    _ ≤ ∑ _p ∈ F, (N : ℝ) ^ (-2 + 1 / (b : ℝ) - t + η + ε / 2) :=
      sum_le_sum fun p hpF ↦ hp N (by omega) L hband p (hF hpF) (hρ p hpF)
    _ = (F.card : ℝ) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) - t + η + ε / 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε / 2) *
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) - t + η + ε / 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem from_four (t a b : ℕ) (ht : 3 ≤ t) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N a b L t ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NM, hNM, hm⟩ := uniform_sector t a b ha hab hcop hb hb4 C 1 ε (by norm_num) hε
  refine ⟨NM, hNM, ?_⟩
  intro N hN L hband
  have hρ : ∀ p ∈ points N a b L t, (nullity p.1 L p.2 : ℝ) ≤ (1 : ℝ) * L := by
    intro p hp
    have hdata := mem_points.mp hp
    let i : Fin t := ⟨0, by omega⟩
    have hpos : 0 < p.2 i := by
      have hx := (mem_Ico.mp (hdata.2.1 i)).1
      omega
    simpa only [one_mul] using (show (nullity p.1 L p.2 : ℝ) ≤ L by
      exact_mod_cast primitive_nullity_le p.1 p.2 hdata.2.2.2 i hpos)
  apply (hm N hN L hband (points N a b L t) Subset.rfl hρ).trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  linarith only [htR]

end PaperP1.EffectiveCompressedPrimitiveElementaryMass
