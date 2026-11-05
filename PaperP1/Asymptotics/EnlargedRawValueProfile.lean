module

public import PaperP1.Asymptotics.CriticalRawValueProfile
public import PaperP1.Arithmetic.RawWindowExtension
public import PaperP1.Asymptotics.SignedSaddleExcess

/-! # The actual full-value profile at the prescribed moving maximal width

The extra-coordinate factor is proved subpolynomial. All newly created
relations are supported on the actual raw hosts at the enlarged width.
The base full-value profile is proved internally; no geometric premise is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedRawValueProfile

open Finset PaperP1.Model PaperP1.RawPairRelationRank PaperP1.RawEvenProfileComparison
  PaperP1.CriticalRawValueProfile PaperP1.SignedSaddleExcess

theorem excess_factor_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, (2 : ℝ) ^ (2 * excess N + 2) ≤ (N : ℝ) ^ ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let η : ℝ := ε / (2 * Real.log 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : (2 * Real.log 2) * η = ε := by dsimp [η]; field_simp
  obtain ⟨N₀, h⟩ := uniform_small η hη
  refine ⟨N₀, ?_⟩
  intro N hN
  have hs := h N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  push_cast at hs ⊢
  calc
    _ = (2 * Real.log 2) * ((excess N : ℝ) + 1) := by ring
    _ ≤ (2 * Real.log 2) * (η * Real.log N) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((2 * Real.log 2) * η) * Real.log N := by ring
    _ = ε * Real.log N := by rw [hηeq]
    _ = _ := by ring

theorem separated_subset (G : Finset ℕ) {L Q : ℕ} (hLQ : L ≤ Q) :
    PairSeparation.separatedHosts G Q ⊆ PairSeparation.separatedHosts G L := by
  intro xy hxy
  obtain ⟨hx, hy, hd⟩ := (PairSeparation.mem_separatedHosts G Q xy).mp hxy
  exact (PairSeparation.mem_separatedHosts G L xy).mpr ⟨hx, hy, by omega⟩

theorem uniform_profile (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        mass N (L + excess N + 1) ≤ (N : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨NB, hB⟩ := PaperP1.CriticalRawValueProfile.uniform_profile C (ε / 4) (by positivity)
  obtain ⟨NW, hW⟩ := uniform_width C
  obtain ⟨NH, hH⟩ := PaperP1.RawEvenProfileHosts.uniform_host_bound widthConstant widthConstant_pos.le (ε / 4) (by positivity)
  obtain ⟨NP, hP⟩ := excess_factor_small (ε / 4) (by positivity)
  obtain ⟨NF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NB (max NW (max NH (max NP NF))), ?_⟩
  intro N hN L hcrit
  let Q := L + excess N + 1
  let F := PairSeparation.separatedHosts (dyadicBlock N) Q
  have hLQ : L ≤ Q := by dsimp [Q]; omega
  have hsub : F ⊆ PairSeparation.separatedHosts (dyadicBlock N) L := separated_subset _ hLQ
  have hblock : F ⊆ (dyadicBlock N) ×ˢ (dyadicBlock N) := by
    intro xy hxy
    have hh := (PairSeparation.mem_separatedHosts (dyadicBlock N) Q xy).mp hxy
    exact mem_product.mpr ⟨hh.1, hh.2.1⟩
  have hpos : ∀ xy ∈ F, 0 < xy.1 ∧ 0 < xy.2 := by
    intro xy hxy
    obtain ⟨hx, hy⟩ := mem_product.mp (hblock hxy)
    have hxl := (mem_Ico.mp hx).1
    have hyl := (mem_Ico.mp hy).1
    constructor <;> omega
  have hbaseF : (∑ xy ∈ F, ((2 ^ fullRank xy.1 xy.2 L : ℝ) - 1)) ≤ (N : ℝ) ^ (3 / 2 + ε / 4) := by
    have hh : (∑ xy ∈ F, ((2 ^ fullRank xy.1 xy.2 L : ℝ) - 1)) ≤ mass N L :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; exact sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
    exact hh.trans (hB N (by omega) L hcrit)
  have hwidth : ((Q + 1 : ℕ) : ℝ) ≤ widthConstant * Real.log N := by
    have hh := hW N (by omega) L hcrit
    simpa only [Q, Nat.add_assoc, show 1 + 1 = (2 : ℕ) by omega] using hh
  have hhosts := hH N (by omega) Q hwidth F hblock
  have hfactor := hP N (by omega)
  have hfinite := PaperP1.RawWindowExtension.finite_extension F hpos hLQ
  have hdiff : 2 * (Q - L) = 2 * excess N + 2 := by dsimp [Q]; omega
  rw [hdiff] at hfinite
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : mass N Q ≤ 2 * (N : ℝ) ^ (3 / 2 + ε / 2) := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * excess N + 2) *
          ((∑ xy ∈ F, ((2 ^ fullRank xy.1 xy.2 L : ℝ) - 1)) + (rawHosts F Q).card) := hfinite
      _ ≤ (N : ℝ) ^ (ε / 4) * (2 * (N : ℝ) ^ (3 / 2 + ε / 4)) :=
        mul_le_mul hfactor (by linarith only [hbaseF, hhosts])
          (add_nonneg (sum_nonneg (fun _ _ ↦ sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) (Nat.cast_nonneg _))
          (Real.rpow_nonneg hn.le _)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hn]
        congr 2
        ring
  simpa only [show (3 : ℝ) / 2 + ε / 2 + ε / 2 = 3 / 2 + ε by ring] using hbound.trans (hF N (by omega))

end PaperP1.EnlargedRawValueProfile
