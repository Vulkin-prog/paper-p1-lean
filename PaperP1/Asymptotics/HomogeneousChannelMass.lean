module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase

/-! # The raw principal homogeneous seed mass has the unconditional pair scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousChannelMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HomogeneousRunMass
  PaperP1.PrimitiveNominalMass PaperP1.CriticalChannelPowers

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_pair_bound {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    {e : Finset ℕ} (he : e ∈ PrivateChannelActivity.pairs N H a b L) :
    probability L e ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  rw [regular_weight (PrivateChannelRank.regular hN ha hab he), weight,
    (PrivateChannelActivity.pair_data hN hab hlarge he).2]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (PrivateChannelRank.nullity_bound hN ha hab hcop hlarge he)
  have hn : (2 ^ runRelativeNullity L e : ℝ) ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
    simpa only [Real.rpow_natCast] using hp
  exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)

theorem uniform_fixed_channel (C : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass (PrivateChannelActivity.pairs N H a b L) L ≤ K * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
  let A : ℝ := (2 * (a + b) + 1 : ℕ)
  let P : ℝ := ((2 : ℝ) ^ C) ^ 2 * (2 : ℝ) ^ ((C + 1) / b)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨2 * A * P, by dsimp only [A, P]; positivity, max 2 (max NG NL), by omega, ?_⟩
  intro N hN L H hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hlarge : (a + b) * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using h
  have hpoint (e : Finset ℕ) (he : e ∈ PrivateChannelActivity.pairs N H a b L) :
      weight L e ≤ P * (N : ℝ) ^ (-2 + 1 / (b : ℝ)) := by
    rw [← regular_weight (PrivateChannelRank.regular (by omega) ha hab he)]
    calc
      _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
        finite_pair_bound (by omega) ha hab hcop hlarge he
      _ ≤ (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) *
          ((2 : ℝ) ^ ((C + 1) / b) * (N : ℝ) ^ (1 / (b : ℝ))) :=
        mul_le_mul (nominal_square_upper (by omega) hband)
          (window_root_upper (by omega) (ha.trans hab) hband) (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hn]; dsimp only [P]; ring
  have hcard : ((PrivateChannelActivity.pairs N H a b L).card : ℝ) ≤ A * (L + 1) * N := by
    dsimp only [A]
    exact_mod_cast PrivateChannelActivity.card_bound_linear (H := H) (L := L) (b := b) (by omega : 0 < N) ha
  have hB : (L + 1 : ℝ) ≤ 2 * L := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  calc
    _ ≤ ∑ _e ∈ PrivateChannelActivity.pairs N H a b L, P * (N : ℝ) ^ (-2 + 1 / (b : ℝ)) :=
      sum_le_sum hpoint
    _ = (PrivateChannelActivity.pairs N H a b L).card * (P * (N : ℝ) ^ (-2 + 1 / (b : ℝ))) :=
      by rw [sum_const, nsmul_eq_mul]
    _ ≤ (A * (L + 1) * N) * (P * (N : ℝ) ^ (-2 + 1 / (b : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (A * (2 * L) * N) * (P * (N : ℝ) ^ (-2 + 1 / (b : ℝ))) := by
      have hm := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ A)
      have hmN := mul_le_mul_of_nonneg_right hm hn.le
      exact mul_le_mul_of_nonneg_right hmN (by positivity)
    _ = _ := by
      have he : (N : ℝ) ^ (-1 + 1 / (b : ℝ)) = N * (N : ℝ) ^ (-2 + 1 / (b : ℝ)) := by
        rw [show (-1 + 1 / (b : ℝ)) = 1 + (-2 + 1 / (b : ℝ)) by ring,
          Real.rpow_add hn, Real.rpow_one]
      rw [he]
      ring

def rawPrincipal (N H L : ℕ) : Finset (Finset ℕ) :=
  PrivateChannelActivity.pairs N H 2 3 L ∪ PrivateChannelActivity.pairs N H 3 4 L

theorem raw_principal_regular {N H L : ℕ} (hN : 2 ≤ N) {e : Finset ℕ}
    (he : e ∈ rawPrincipal N H L) : e ⊆ RegularStarts.regularStarts N L := by
  rcases mem_union.mp he with h23 | h34
  · exact PrivateChannelRank.regular hN (by decide : 0 < 2) (by decide : 2 < 3) h23
  · exact PrivateChannelRank.regular hN (by decide : 0 < 3) (by decide : 3 < 4) h34

theorem beta_le_raw_mass {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    PrincipalChannelEdges.beta N H L ≤ mass (rawPrincipal N H L) L := by
  have hsub : PrincipalChannelEdges.edges N H L ⊆ rawPrincipal N H L := by
    intro e he
    rcases mem_union.mp he with h23 | h34
    · exact mem_union_left _ (mem_filter.mp h23).1
    · exact mem_union_right _ (mem_filter.mp h34).1
  calc
    _ ≤ ∑ e ∈ PrincipalChannelEdges.edges N H L, probability L e :=
      sum_le_sum (fun e _ ↦ actual_joint_le L hL e)
    _ ≤ ∑ e ∈ rawPrincipal N H L, probability L e :=
      sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ (probability_pos L e).le)
    _ = _ := sum_congr rfl (fun e he ↦ regular_weight (raw_principal_regular hN he))

theorem uniform_principal_upper (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass (rawPrincipal N H L) L ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
  obtain ⟨K23, hK23, N23, _hN23, h23⟩ := uniform_fixed_channel C 2 3 (by decide) (by decide) (by decide)
  obtain ⟨K34, hK34, N34, _hN34, h34⟩ := uniform_fixed_channel C 3 4 (by decide) (by decide) (by decide)
  refine ⟨K23 + K34, by positivity, max 2 (max N23 N34), by omega, ?_⟩
  intro N hN L H hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm23 := h23 N (by omega) L H hband
  have hm34 := h34 N (by omega) L H hband
  norm_num only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 3 = -2 / 3 by ring] at hm23
  norm_num only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 4 = -3 / 4 by ring] at hm34
  have hpow : (N : ℝ) ^ (-3 / 4 : ℝ) ≤ (N : ℝ) ^ (-2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h34upper : mass (PrivateChannelActivity.pairs N H 3 4 L) L ≤ K34 * L * (N : ℝ) ^ (-2 / 3 : ℝ) :=
    hm34.trans (mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hpow) (by positivity))
  have hcover : mass (rawPrincipal N H L) L ≤ mass (PrivateChannelActivity.pairs N H 2 3 L) L +
      mass (PrivateChannelActivity.pairs N H 3 4 L) L := by
    have heq := sum_union_inter (s₁ := PrivateChannelActivity.pairs N H 2 3 L)
      (s₂ := PrivateChannelActivity.pairs N H 3 4 L) (f := weight L)
    have hnon : 0 ≤ ∑ e ∈ PrivateChannelActivity.pairs N H 2 3 L ∩ PrivateChannelActivity.pairs N H 3 4 L,
        weight L e := sum_nonneg (fun e _ ↦ weight_nonneg L e)
    change mass (rawPrincipal N H L) L +
      (∑ e ∈ PrivateChannelActivity.pairs N H 2 3 L ∩ PrivateChannelActivity.pairs N H 3 4 L, weight L e) =
      mass (PrivateChannelActivity.pairs N H 2 3 L) L + mass (PrivateChannelActivity.pairs N H 3 4 L) L at heq
    linarith only [heq, hnon]
  linarith only [hcover, hm23, h34upper]

theorem principal_positive_phase (C : ℝ) (D : ℕ) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      c * L * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ mass (rawPrincipal N H L) L ∧
        mass (rawPrincipal N H L) L ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
  obtain ⟨c, _k, hc, _hk, NP, _hNP, hp⟩ := PrincipalChannelEdgesPhase.positive_phase C D
  obtain ⟨K, hK, NU, _hNU, hu⟩ := uniform_principal_upper C
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨c, K, hc, hK, max 2 (max NP (max NU NG)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  exact ⟨(hp N (by omega) L H hband hcut hH).1.trans
    (beta_le_raw_mass (by omega) (hg N (by omega) L hband).1), hu N (by omega) L H hband⟩

end PaperP1.HomogeneousChannelMass
