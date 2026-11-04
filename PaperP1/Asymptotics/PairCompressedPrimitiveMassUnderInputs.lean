module

public import PaperP1.Asymptotics.PairCompressedDenseMassUnderInputs
public import PaperP1.Asymptotics.PairCompressedPrimitiveElementaryMass
public import PaperP1.Model.PairCompressedPrimitiveTransport

/-! # The stronger fixed primitive mass after pair compression

For `t >= 2` further original windows the mass is N^(-kappa_b+epsilon),
improving the companion's N^(-kappa_b+1/5+epsilon). The three-block
compressed case uses the existing finite geometry; every larger fixed
order has an unconditional elementary proof.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedPrimitiveMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.PairCompressedPrimitivePopulation

theorem three_blocks (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : DensePrimitiveTripleMassUnderInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses p →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N a b L 2 ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  classical
  obtain ⟨p, hp⟩ := PairCompressedDenseMassUnderInputs.uniform_bound a b ha hab hcop
    C (1 / 4) (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := PairCompressedPrimitiveElementaryMass.uniform_sector
    2 a b ha hab hcop hb hb4 C (1 / 4) (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2
    (-2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo
  refine ⟨max 3 (max NL (max NF ND)), by omega, ?_⟩
  intro N hN L hband
  let F := points N a b L 2
  let P := fun q : (ℕ × ℕ) × (Fin 2 → ℕ) ↦ (nullity q.1 L q.2 : ℝ) ≤ (1 / 4 : ℝ) * L
  let w := fun q : (ℕ × ℕ) × (Fin 2 → ℕ) ↦ HomogeneousRunMass.probability L (family q.1 q.2)
  have hlow : (∑ q ∈ F.filter P, w q) ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
    have hh := hl N (by omega) L hband (F.filter P) (filter_subset _ _) (fun _ hq ↦ (mem_filter.mp hq).2)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num; linarith only []))
  have hdense : (∑ q ∈ F.filter (fun q ↦ ¬ P q), w q) ≤
      (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
    apply hd N (by omega) L hband _ (filter_subset _ _)
    intro q hq
    exact le_of_lt (lt_of_not_ge (mem_filter.mp hq).2)
  have hpart := sum_filter_add_sum_filter_not F P w
  calc
    _ ≤ 2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
      change (∑ q ∈ F, w q) ≤ _
      linarith only [hpart, hlow, hdense]
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_mass (t a b : ℕ) (ht : 2 ≤ t) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : DensePrimitiveTripleMassUnderInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses p →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N a b L t ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨p, hp⟩ := three_blocks a b ha hab hcop hb hb4 C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  by_cases ht2 : t = 2
  · subst t
    exact hp hgeo
  · obtain ⟨N₀, _hN₀, hm⟩ := PairCompressedPrimitiveElementaryMass.from_four
      t a b (by omega) ha hab hcop hb hb4 C ε hε
    exact ⟨max 3 N₀, by omega, fun N hN ↦ hm N (by omega)⟩

theorem actual_joint_le_mass (N a b L t : ℕ) (hL : 0 < L) :
    (∑ q ∈ points N a b L t, infiniteJointMoment L (family q.1 q.2)) ≤ mass N a b L t :=
  sum_le_sum fun q _ ↦ HomogeneousRunMass.actual_joint_le L hL (family q.1 q.2)

theorem family_mass_le (N a b L t : ℕ) :
    (∑ I ∈ (points N a b L t).image (fun q ↦ family q.1 q.2),
      HomogeneousRunMass.probability L I) ≤ mass N a b L t :=
  sum_image_le_of_nonneg (fun I _ ↦ (HomogeneousRunMass.probability_pos L I).le)

theorem companion_T4_4 (t : ℕ) (ht : 2 ≤ t) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p34 : DensePrimitiveTripleMassUnderInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses p23 →
      DensePrimitiveTripleMassUnderInputs.Hypotheses p34 →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N 2 3 L t ≤ (N : ℝ) ^ (-5 / 3 + ε) ∧
      mass N 3 4 L t ≤ (N : ℝ) ^ (-7 / 4 + ε) ∧
      (∑ q ∈ points N 2 3 L t, infiniteJointMoment L (family q.1 q.2)) ≤ (N : ℝ) ^ (-5 / 3 + ε) ∧
      (∑ q ∈ points N 3 4 L t, infiniteJointMoment L (family q.1 q.2)) ≤ (N : ℝ) ^ (-7 / 4 + ε) := by
  obtain ⟨p23, h23⟩ := uniform_mass t 2 3 ht (by decide) (by decide) (by decide)
    (by decide) (by decide) C ε hε
  obtain ⟨p34, h34⟩ := uniform_mass t 3 4 ht (by decide) (by decide) (by decide)
    (by decide) (by decide) C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p23, p34, ?_⟩
  intro hgeo23 hgeo34
  obtain ⟨N23, _hN23, h23⟩ := h23 hgeo23
  obtain ⟨N34, _hN34, h34⟩ := h34 hgeo34
  refine ⟨max 3 (max NG (max N23 N34)), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hm23 : mass N 2 3 L t ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
    convert h23 N (by omega) L hband using 1; norm_num
  have hm34 : mass N 3 4 L t ≤ (N : ℝ) ^ (-7 / 4 + ε) := by
    convert h34 N (by omega) L hband using 1; norm_num
  exact ⟨hm23, hm34, (actual_joint_le_mass N 2 3 L t hL).trans hm23,
    (actual_joint_le_mass N 3 4 L t hL).trans hm34⟩

theorem companion_T4_4_original (t a b : ℕ) (ht : 2 ≤ t) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : DensePrimitiveTripleMassUnderInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses p →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ P : Finset ((ℕ × ℕ) × Finset ℕ),
      (∀ q ∈ P, q.1 ∈ FixedChannelSourceGeometry.unitSources N a b L ∧
        ({q.1.1, q.1.2} ∪ q.2) ⊆ RegularStarts.regularStarts N L ∧ q.2.card = t ∧
        PairPrimitiveCompression.Primitive L {q.1.1, q.1.2} q.2) →
      (∑ q ∈ P, HomogeneousRunMass.probability L ({q.1.1, q.1.2} ∪ q.2)) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) ∧
      (∑ q ∈ P, PrimitiveNominalMass.weight L ({q.1.1, q.1.2} ∪ q.2)) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) ∧
      (∑ q ∈ P, infiniteJointMoment L ({q.1.1, q.1.2} ∪ q.2)) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨p, hp⟩ := uniform_mass t a b ht ha hab hcop hb hb4 C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NM, _hNM, hm⟩ := hp hgeo
  refine ⟨max 3 (max NG NM), by omega, ?_⟩
  intro N hN L hband P hP
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hmass : (∑ q ∈ P, HomogeneousRunMass.probability L ({q.1.1, q.1.2} ∪ q.2)) ≤
      (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) :=
    (PairCompressedPrimitiveTransport.finite_mass_bound P (fun q hq ↦
      ⟨(hP q hq).1, fun x hx ↦ (hP q hq).2.1 (mem_union_right _ hx),
        (hP q hq).2.2.1, (hP q hq).2.2.2⟩)).trans (hm N (by omega) L hband)
  refine ⟨hmass, ?_, ?_⟩
  · apply le_trans (le_of_eq ?_) hmass
    apply sum_congr rfl
    intro q hq
    exact (HomogeneousRunMass.regular_weight (hP q hq).2.1).symm
  · exact (sum_le_sum fun q _ ↦ HomogeneousRunMass.actual_joint_le L hL _).trans hmass

end PaperP1.PairCompressedPrimitiveMassUnderInputs
