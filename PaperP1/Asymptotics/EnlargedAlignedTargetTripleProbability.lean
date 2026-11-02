module

public import PaperP1.Asymptotics.EnlargedSourceTargetResidual
public import PaperP1.Asymptotics.BinaryRankPowers
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Arithmetic.AlignedTargetCanonicalRank
public import PaperP1.Model.ThreeNormalizedFamilyRank

/-! # Sharp actual point probabilities for every interior distinct-slope target above an enlarged source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedAlignedTargetTripleProbability

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ScaledTargetValues PaperP1.PrivateNormalizedFamilies

theorem uniform_point_bound {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L c d x y z t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < c → 0 < d → c.Coprime d → d ≤ (L + 1) ^ J →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      c < 2 * (a * d) → b * d < 2 * c → c ≠ a * d → c ≠ b * d →
      EnlargedPairGeometry.Geometric a b x y L →
      ∀ i : Fin (L + 1), startCompleteVertexLabel x L i = a * t →
        ∀ h : ℤ, |h| ≤ ((L + 1) ^ J : ℕ) → (d : ℤ) * z = (c : ℤ) * t + h →
          infiniteJointMoment L {x, y, z} ≤ (N : ℝ) ^ (-71 / 30 + ε) := by
  let η := min (ε / 4) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηq : η ≤ 1 / 4 := min_le_right _ _
  have hαη : 0 ≤ (71 / 30 : ℝ) - η := by linarith only [hηq]
  have hεη : 0 < ε - η := by linarith only [hηε, hε]
  obtain ⟨NR, hr⟩ := EnlargedSourceTargetResidual.row_rank_sublinear C η hη ha hab.le J
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption
    (BinaryRankPowers.constant C ((71 / 30 : ℝ) - η) (5 + η)) (-71 / 30 + η) (ε - η) hεη
  refine ⟨max 10 (max NR (max NG NP)), by omega, ?_⟩
  intro N hN L c d x y z t hband hc hd hcd hdH hx hy hz hTop hLow hca hcb hsourceGeom i hbaseX h hh htarget
  have hb : 0 < b := ha.trans hab
  have hx2 : 2 ≤ x := by have hh := (mem_Ico.mp hx).1; omega
  have hy2 : 2 ≤ y := by have hh := (mem_Ico.mp hy).1; omega
  have hz2 : 2 ≤ z := by have hh := (mem_Ico.mp hz).1; omega
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  let S := allValues a b c d x y z L
  let X : Fin 3 → ℕ := ![x, y, z]
  let q : Fin 3 → ℕ := ![b * c, a * c, a * b * d]
  let R := Module.finrank F₂ (⨆ k, squareClassSpace (X k) L : Submodule F₂ (ℕ →₀ F₂))
  have hrow := hr N (by omega) L c d x y z t hband hc hd hdH hx hy hz hsourceGeom i hbaseX h hh htarget
  have hfull := Submodule.finrank_mono (FiniteResidualRank.kernel_le_rows S
    (TwoProgressionPrimeRows.exceptionalPrimes (6 * b * (L + 1)) c (a * b * d)))
  have hdef : (Module.finrank F₂ (FiniteResidualRank.valueKernel S) : ℝ) ≤ η * (L + 1) := by
    have hfullR : (Module.finrank F₂ (FiniteResidualRank.valueKernel S) : ℝ) ≤
        Module.finrank F₂ (CoverGraphResolution.rowSolutions
          (PrimeRowComponents.rows S (TwoProgressionPrimeRows.exceptionalPrimes (6 * b * (L + 1)) c (a * b * d)))) := by
      exact_mod_cast hfull
    exact hfullR.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hrow)
  have hq : ∀ k, 0 < q k := by
    intro k
    fin_cases k
    · exact Nat.mul_pos hb hc
    · exact Nat.mul_pos ha hc
    · exact Nat.mul_pos (Nat.mul_pos ha hb) hd
  have hX : ∀ k, 2 ≤ X k := by intro k; fin_cases k <;> assumption
  have hcard := ThreeNormalizedFamilyRank.card_le_rank_add_kernel (L := L) q X hq hX
  change (valueUnion q X L).card ≤ R + Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion q X L)) + 3 at hcard
  have hS : valueUnion q X L = S := AlignedTargetCanonicalRank.allValues_eq_family a b c d x y z L
  rw [hS] at hcard
  have hcardR : (S.card : ℝ) ≤ (R : ℝ) + Module.finrank F₂ (FiniteResidualRank.valueKernel S) + 3 := by
    exact_mod_cast hcard
  have hSpos : 1 ≤ S.card := card_pos.mpr
    ((NormalizedWindowSets.normalized_nonempty (a * b * d) z L).mono subset_union_right)
  have hcan := AlignedTargetCanonicalRank.canonical_rank (L := L) hab hb2a hcop hd hcd hTop hLow hca hcb hx2 hy2 hz2
  change (71 / 30 : ℝ) * L - 3 ≤ ((S.card - 1 : ℕ) : ℝ) at hcan
  rw [Nat.cast_sub hSpos, Nat.cast_one] at hcan
  have hR : ((71 / 30 : ℝ) - η) * L - (5 + η) ≤ (R : ℝ) := by
    nlinarith only [hcardR, hdef, hcan]
  have hbinary := BinaryRankPowers.upper (by omega : 2 ≤ N) hαη hband hR
  rw [show -((71 / 30 : ℝ) - η) = -71 / 30 + η by ring] at hbinary
  have habsorb : BinaryRankPowers.constant C ((71 / 30 : ℝ) - η) (5 + η) * (N : ℝ) ^ (-71 / 30 + η) ≤
      (N : ℝ) ^ (-71 / 30 + ε) := by
    simpa only [show (-71 / 30 + η) + (ε - η) = (-71 / 30 : ℝ) + ε by ring] using hp N (by omega)
  have hprob := NormalizedFamilyDefectRank.actual_joint_le_rank X hL
  have hsupport : FiniteFamilyEnumeration.tupleSet X = {x, y, z} := by
    have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [FiniteFamilyEnumeration.tupleSet, hu]
    simp only [image_insert, image_singleton]
    rfl
  rw [hsupport] at hprob
  exact hprob.trans (hbinary.trans habsorb)

end PaperP1.EnlargedAlignedTargetTripleProbability
