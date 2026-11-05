module

public import PaperP1.Asymptotics.EnlargedAlignedPairTheorem
public import PaperP1.Asymptotics.NonalignedPairActivity
public import PaperP1.Asymptotics.BoundaryAlignedActivity
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Model.AllAlignedPairs
public import PaperP1.Model.DependentPairJointActivity

/-! # The entire actual pair joint mass above half a window rank has rate1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HighNullityPairMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem aligned_cover (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ e ∈ AllAlignedPairs.families N L,
      (L : ℝ) / 2 < runRelativeNullity L e →
      e ∈ BoundaryAlignedPairs.channel N L 1 1 ∪ BoundaryAlignedPairs.channel N L 1 2 := by
  classical
  obtain ⟨NR, hr⟩ := EnlargedAlignedPairTheorem.uniform_bounds C (1 / 24) (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C 2 (by norm_num) 4
  refine ⟨10 + NR + NG + NP, by omega, ?_⟩
  intro N hN L hband e he hstrong
  have heN := (mem_filter.mp he).1
  obtain ⟨x, y, a, b, hx, hy, rfl, hxy, ha, hb, hcop, hheight, hgeom⟩ := AllAlignedPairs.data he
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hlarge : 2 * (L + 1) ^ 4 < N := by exact_mod_cast hp N (by omega) L hband
  have hsmall : (a + b) * (L + 1) < N := by
    calc
      _ ≤ (2 * (L + 1) ^ 3) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * (L + 1) ^ 4 := by ring
      _ < _ := hlarge
  have hab := AllAlignedPairs.orientation (mem_Ico.mp hx).1 hxy hgeom hsmall
  have hrank := (hr N (by omega) L a b x y hband ha hb hcop hheight hx hy hgeom).2.2
  have hrelative : runRelativeNullity L {x, y} =
      FreeComponentRank.pairIntersectionRank x y L := by
    rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ _ _ hxy.ne]
    rfl
  rw [hrelative] at hstrong
  have htwo : b ≤ 2 := by
    by_contra hnot
    have hbR : (3 : ℝ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
    have hdiv : (L : ℝ) / max a b ≤ (L : ℝ) / 3 := by
      rw [max_eq_right hab]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg L) (by norm_num) hbR
    have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    nlinarith only [hrank, hstrong, hdiv, hB, hLpos]
  have hcases : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 2) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact mem_union_left _ (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hgeom⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hgeom⟩)
  · norm_num at hcop

theorem uniform_mass (v C ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
        (∀ e ∈ F, e ⊆ dyadicBlock N ∧ e.card = 2 ∧ (L : ℝ) / 2 < runRelativeNullity L e) →
        (∑ e ∈ F, v ^ e.card * infiniteJointMoment L e) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NN, _hNN, hn⟩ := NonalignedPairActivity.uniform_activity C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := aligned_cover C
  obtain ⟨N1, _hN1, h1⟩ := BoundaryAlignedActivity.height_one C (ε / 2) (by positivity)
  obtain ⟨N2, _hN2, h2⟩ := BoundaryAlignedActivity.height_two C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (6 * v ^ 2) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NC + N1 + N2 + NG + NF + NN, by omega, ?_⟩
  intro N hN L hband F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let A := AllAlignedPairs.nonaligned N L
  let B := BoundaryAlignedPairs.channel N L 1 1
  let D := BoundaryAlignedPairs.channel N L 1 2
  let w := fun e : Finset ℕ ↦ |infiniteCenteredCoefficient L e|
  have hw (e : Finset ℕ) : 0 ≤ w e := abs_nonneg _
  have hcover : F ⊆ (A ∪ B) ∪ D := by
    intro e he
    obtain ⟨heG, hcard, hstrong⟩ := hF e he
    by_cases ha : e ∈ AllAlignedPairs.families N L
    · rcases mem_union.mp (hc N (by omega) L hband e ha hstrong) with hB | hD
      · exact mem_union_left _ (mem_union_right _ hB)
      · exact mem_union_right _ hD
    · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨heG, hcard⟩, ha⟩))
  have hactivity : (∑ e ∈ F, w e) ≤ 3 * (N : ℝ) ^ (-1 + ε / 2) := by
    have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun e _ _ ↦ hw e)
    have hAB := GraphStarWeights.sum_union_le_nonneg A B w hw
    have hABD := GraphStarWeights.sum_union_le_nonneg (A ∪ B) D w hw
    have hA := hn N (by omega) L hband
    have hB := h1 N (by omega) L hband
    have hD := (h2 N (by omega) L hband).2
    change (∑ e ∈ A, w e) ≤ _ at hA
    change (∑ e ∈ B, w e) ≤ _ at hB
    change (∑ e ∈ D, w e) ≤ _ at hD
    linarith only [h0, hAB, hABD, hA, hB, hD]
  calc
    _ ≤ ∑ e ∈ F, v ^ 2 * (2 * w e) := by
      apply sum_le_sum
      intro e he
      obtain ⟨_hsub, hcard, hstrong⟩ := hF e he
      have hdep : 0 < runRelativeNullity L e := by
        have hnonneg : (0 : ℝ) ≤ (L : ℝ) / 2 := by positivity
        have hpos : (0 : ℝ) < runRelativeNullity L e := hnonneg.trans_lt hstrong
        exact_mod_cast hpos
      rw [hcard]
      exact mul_le_mul_of_nonneg_left (DependentPairJointActivity.pointwise L hL e hcard hdep) (pow_nonneg hv 2)
    _ = (2 * v ^ 2) * ∑ e ∈ F, w e := by rw [mul_sum]; apply sum_congr rfl; intro e _; ring
    _ ≤ (2 * v ^ 2) * (3 * (N : ℝ) ^ (-1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left hactivity (by positivity)
    _ = (6 * v ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.HighNullityPairMass
