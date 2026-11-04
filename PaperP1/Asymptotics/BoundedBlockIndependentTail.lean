module

public import PaperP1.Asymptotics.WideOneSeedTail
public import PaperP1.Model.OneBlockFullSupport
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.FullSupportIndependentTail

/-! # Independent all-cardinality full-support tails with one arbitrary bounded block

The block has its literal finite integer labels, not a prescribed source rank.
One threshold precedes every block family satisfying the physical containment.
All original heterogeneous marginals and the independent source weight vp are
retained. Geometric types may be badly normalized and may meet target windows.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedBlockIndependentTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

def mass (Q N L s : ℕ) (v : ℝ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ x ∈ Ico 2 (Q * N + 2), (v * (2 ^ L : ℝ)⁻¹) *
    ∑ I ∈ OneBlockFullSupport.families (dyadicBlock N) L (U x) s,
      ∏ y ∈ I, v * infiniteMarginal y L

theorem uniform_blocks (D Q : ℕ) (hD : 1 ≤ D) (hQ : 2 ≤ Q) (C v a ε : ℝ)
    (hv : 0 < v) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ U : ℕ → Finset ℕ,
      (∀ x ∈ Ico 2 (Q * N + 2), U x ⊆ NormalizedWindowSets.values x (D * (L + 1))) →
      mass Q N L s v U ≤ (N : ℝ) ^ (-a + ε) := by
  classical
  let M := v * (2 * (2 : ℝ) ^ C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨s, hs, NT, _hNT, ht⟩ := WideOneSeedTail.uniform_tail D Q hD hQ C M a ε hM ha hε
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  refine ⟨s, hs, max 10 (max NT NM), by omega, ?_⟩
  intro N hN L hband U hU
  let p := fun y ↦ if y ∈ dyadicBlock N then v * infiniteMarginal y L else 0
  let w := fun _ : ℕ ↦ v * (2 ^ L : ℝ)⁻¹
  have hp : ∀ y, 0 ≤ p y := by
    intro y
    dsimp [p]
    split_ifs
    · exact mul_nonneg hv.le (MissingBlockProbabilities.infiniteMarginal_nonneg y L)
    · exact le_rfl
  have hw : ∀ y, 0 ≤ w y := fun _ ↦ by dsimp [w]; positivity
  have hpcap : ∀ y ∈ Ico 2 (Q * N + 2), p y ≤ M / N := by
    intro y _hy
    dsimp only [p]
    split_ifs with hy
    · have hh := mul_le_mul_of_nonneg_left (hm N (by omega) L hband y hy) hv.le
      simpa only [M, mul_div_assoc] using hh
    · positivity
  have hwcap : ∀ y ∈ Ico 2 (Q * N + 2), w y ≤ M / N := by
    intro y _hy
    have hb := LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hband
    have hzero : (0 : ℝ) ≤ (2 : ℝ) ^ C / N := by positivity
    have hnom : (2 ^ L : ℝ)⁻¹ ≤ 2 * (2 : ℝ) ^ C / N := by
      rw [mul_div_assoc]
      linarith only [hb, hzero]
    have hh := mul_le_mul_of_nonneg_left hnom hv.le
    simpa only [w, M, mul_div_assoc, mul_assoc] using hh
  have hsource : ∀ x ∈ Ico 2 (Q * N + 2),
      FiniteEvenSquareClasses.space (U x) ≤ squareClassSpace x (D * (L + 1)) := by
    intro x hx
    exact (EvenWindowEnlargement.space_mono (hU x hx)).trans_eq (NormalizedWindowSets.space_values _ _)
  let Families := fun x ↦ OneBlockFullSupport.families (dyadicBlock N) L (U x) s
  have hfamily : ∀ x ∈ Ico 2 (Q * N + 2), ∀ I ∈ Families x,
      I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L (FiniteEvenSquareClasses.space (U x)) I := by
    intro x _hx I hI
    obtain ⟨hIG, hsize, hfull⟩ := (OneBlockFullSupport.mem_families _ _ _ _ _).mp hI
    exact ⟨hIG, hsize, OneBlockFullSupport.witnesses hfull⟩
  have htail := ht N (by omega) L hband (fun x ↦ FiniteEvenSquareClasses.space (U x)) hsource
    p w hp hw hpcap hwcap Families hfamily
  apply le_trans (le_of_eq ?_) htail
  unfold mass
  apply sum_congr rfl
  intro x _hx
  apply congrArg (fun t : ℝ ↦ w x * t)
  apply sum_congr rfl
  intro I hI
  apply prod_congr rfl
  intro y hy
  have hyG := ((OneBlockFullSupport.mem_families _ _ _ _ _).mp hI).1 hy
  exact (ite_eq_left hyG).symm

theorem mass_antitone (Q N L : ℕ) (v : ℝ) (hv : 0 ≤ v) (U : ℕ → Finset ℕ)
    {s t : ℕ} (hst : s ≤ t) : mass Q N L t v U ≤ mass Q N L s v U := by
  unfold mass
  apply sum_le_sum
  intro x _hx
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (OneBlockFullSupport.families_antitone _ _ _ hst)
    (fun I _ _ ↦ prod_nonneg fun y _ ↦ mul_nonneg hv (MissingBlockProbabilities.infiniteMarginal_nonneg y L))

end PaperP1.BoundedBlockIndependentTail
