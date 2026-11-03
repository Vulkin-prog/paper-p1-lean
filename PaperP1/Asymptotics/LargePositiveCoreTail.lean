module

public import PaperP1.Asymptotics.MultiAnchorBudgets
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Model.RelationCoreWitnesses
public import PaperP1.Model.PrimitiveRankAmplification

/-! # All sufficiently large positive-projection cores have rank and joint mass rate3/2 below η ranks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargePositiveCoreTail

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

theorem parameters (t : ℕ) (ht : 2 ≤ t) :
    ∃ A β σ : ℝ, 1 < A ∧ 0 < β ∧ β < 1 ∧ 1 / 2 < σ ∧ σ < 1 ∧
      A * (1 - σ) < 1 ∧ (t : ℝ) / A + (1 - β) * (1 - σ) < 1 ∧
      -(t : ℝ) * β + 2 * t / A = -(t : ℝ) + 1 / 2 := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith only [htR]
  let q : ℝ := 1 / (16 * t)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsmall : q ≤ 1 / 32 := by
    dsimp only [q]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith only [htR]
  have hqt : q * (t : ℝ) = 1 / 16 := by dsimp [q]; field_simp
  have hratio : (t : ℝ) / (8 * t) = 1 / 8 := by field_simp
  refine ⟨8 * t, 1 - 4 * q, 1 - q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [htR]
  · linarith only [hqsmall]
  · linarith only [hq]
  · linarith only [hqsmall]
  · linarith only [hq]
  · nlinarith only [hqt]
  · rw [hratio]
    nlinarith only [hq, hqsmall]
  · have hr : 2 * (t : ℝ) / (8 * t) = 1 / 4 := by field_simp; ring
    rw [hr]
    nlinarith only [hqt]

theorem uniform_rank (t : ℕ) (η v C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hv : 0 < v) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ Core t L I ∧
        (runRelativeNullity L I : ℝ) ≤ η * L) →
      WeightedPrimitiveMass.rankMass F L v ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨A, β, σ, hA, hβ, hβ1, hσ, hσ1, hcut, hgap, hexponent⟩ := parameters t ht
  let θ := (1 - β) * (1 - σ) / 2
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  obtain ⟨s, hs⟩ := exists_nat_gt (max 3 ((η + 2) / θ))
  have hs3 : 3 ≤ s := by
    have h : (3 : ℝ) < s := (le_max_left _ _).trans_lt hs
    have : 3 < s := by exact_mod_cast h
    omega
  have hθs : η + 2 ≤ θ * s := by
    have h := (div_lt_iff₀ hθ).mp ((le_max_right _ _).trans_lt hs)
    linarith only [h]
  let M := v * (2 * (2 : ℝ) ^ C)
  obtain ⟨NB, _hNB, hb⟩ := MultiAnchorBudgets.uniform_split_bound t C M A β σ (ε / 4)
    htEven ht (by dsimp [M]; positivity) hA hβ hβ1 hσ hσ1 hcut hgap (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.power_of_rank C η 0 (ε / 4) hη (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs3, 10 + NB + NM + NP + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let w := fun x ↦ v * infiniteMarginal x L
  have hw (x : ℕ) : 0 ≤ w x := mul_nonneg hv.le (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hcap (x : ℕ) (hx : x ∈ dyadicBlock N) : w x ≤ M / N := by
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hv.le
    simpa only [w, M, mul_div_assoc] using h
  have hi := hb N (by omega) L hband w hw hcap s F (by
    intro I hI
    obtain ⟨hIG, hsize, hcore, _hrank⟩ := hF I hI
    have hpos (x : ℕ) (hx : x ∈ I) : 0 < x := by
      have h := (mem_Ico.mp (hIG hx)).1
      omega
    exact ⟨hIG, hsize, witnesses t L htEven I hcore hpos _ _⟩)
  have htail_exp : -(1 - β) * (1 - σ) / 2 = -θ := by dsimp [θ]; ring
  rw [htail_exp] at hi
  have hamp (I : Finset ℕ) (hI : I ∈ F) :
      (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) ≤ (N : ℝ) ^ (η + ε / 4) := by
    apply hp N (by omega) L _ hband
    have hcap := (hF I hI).2.2.2
    have hεL : 0 ≤ ε * (L : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg L)
    change (runRelativeNullity L I : ℝ) ≤ _
    push_cast
    nlinarith only [hcap, hη, hε, hεL]
  have hmass := PrimitiveRankAmplification.mass_bound F L v ((N : ℝ) ^ (η + ε / 4)) hv.le hamp
  calc
    _ ≤ (N : ℝ) ^ (η + ε / 4) * ∑ I ∈ F, ∏ x ∈ I, w x := hmass
    _ ≤ (N : ℝ) ^ (η + ε / 4) *
        ((N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε / 4) +
          (N : ℝ) ^ (-θ * s + ε / 4)) :=
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (η + (-(t : ℝ) + 1 / 2) + ε / 2) +
        (N : ℝ) ^ (η - θ * s + ε / 2) := by
      rw [hexponent, mul_add, ← Real.rpow_add hn, ← Real.rpow_add hn]
      congr 2 <;> ring
    _ ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) + (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [htη]))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hθs]))
    _ = 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_joint (t : ℕ) (η v C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hv : 0 < v) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ Core t L I ∧
        (runRelativeNullity L I : ℝ) ≤ η * L) →
      (∑ I ∈ F, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨s, hs, NR, _hNR, hr⟩ := uniform_rank t η v C ε htEven ht hη htη hv hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨s, hs, 10 + NR + NG, by omega, ?_⟩
  intro N hN L hband F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  calc
    _ ≤ WeightedPrimitiveMass.rankMass F L v := sum_le_sum fun I _ ↦
      mul_le_mul_of_nonneg_left (PrimitiveWindowMass.joint_le_weight L hL I) (pow_nonneg hv.le _)
    _ ≤ _ := hr N (by omega) L hband F hF

end PaperP1.LargePositiveCoreTail
