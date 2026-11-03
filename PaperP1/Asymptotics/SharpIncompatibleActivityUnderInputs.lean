module

public import PaperP1.Model.IncompatibleHigherDeficit
public import PaperP1.Asymptotics.FixedActivityInputBundle
public import PaperP1.Asymptotics.AllPairDeficitUnderInputs
public import PaperP1.Asymptotics.UniformIndependentDeficit
public import PaperP1.Asymptotics.OriginalWindowFamilyMass

/-! # All incompatible connected fixed orders have rate three halves using only coarse higher activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpIncompatibleActivityUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

structure Parameters (R : ℕ) where
  activity : FixedMomentInputs.Parameters R
  deficitOrder : ℕ
  deficitInitial : FinitePairDeficitInputs.Parameters
  deficitEntries : Fin deficitOrder → FinitePairDeficitInputs.Parameters

structure Hypotheses {R : ℕ} (p : Parameters R) (ε : ℝ) : Prop where
  activity : FixedMomentInputs.Hypotheses p.activity ε
  deficitInitial : FinitePairDeficitInputs.Hypotheses p.deficitInitial (GeneralGraphHostCount.sizeCap (ε / 8192))
  deficitEntries : ∀ i, FinitePairDeficitInputs.Hypotheses (p.deficitEntries i)
    (GeneralGraphHostCount.sizeCap (ε / 262144))

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        F ⊆ connectedFamilies G L r → (∀ I ∈ F, infiniteJointMoment L I = 0) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨pa, ha⟩ := FixedActivityInputBundle.uniform_range R C ε hε
  obtain ⟨_Q, s, _hQ, _hs, p₀, ps, hd⟩ := AllPairDeficitUnderInputs.article_15_9 1 C (ε / 4)
    (by norm_num) (by positivity)
  obtain ⟨NE, _hNE, he⟩ := UniformIndependentDeficit.uniform_bound R 1 C (ε / 4) (by norm_num) (by positivity)
  have hind (i : Fin (R + 1)) := OriginalWindowFamilyMass.article_10_2 (max 3 i.val)
    (by omega) C (ε / 4) (by positivity)
  choose NI hi using hind
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((R : ℝ) + 3)
    (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨pa, s, p₀, ps⟩, ?_⟩
  intro hgeo
  obtain ⟨NA, _hNA, ha⟩ := ha hgeo.activity
  have hs₀ : ((ε / 4) / 16) / 128 = ε / 8192 := by ring
  have hsP : ((ε / 4) / 16) / 4096 = ε / 262144 := by ring
  obtain ⟨ND, _hND, hd⟩ := hd (by simpa only [hs₀] using hgeo.deficitInitial)
    (by simpa only [hsP] using hgeo.deficitEntries)
  refine ⟨10 + NA + NE + NF + ND + univ.sup NI, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF hq
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let i : Fin (R + 1) := ⟨r, by omega⟩
  have hNi : NI i ≤ univ.sup NI := le_sup (f := NI) (mem_univ i)
  have hmax : max 3 i.val = r := max_eq_right hthree
  have hind : FamilyIndependentMass.independentMass F L ≤ (N : ℝ) ^ (-3 / 2 + ε / 4) := by
    have hraw := (hi i N (by omega) L G hband hG).2.2.1
    rw [hmax] at hraw
    have hs : FamilyIndependentMass.independentMass F L ≤ FamilyIndependentMass.independentMass (connectedFamilies G L r) L :=
      sum_le_sum_of_subset_of_nonneg hF (fun I _ _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    apply (hs.trans hraw).trans
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by
      have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hthree
      linarith only [hrR])
  let S := IncompatibleHigherDeficit.higherSources G r
  have hsource : (∑ D ∈ S, |infiniteCenteredCoefficient L D|) ≤
      ((R + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 + ε / 4) := by
    have hsplit := sum_fiberwise_of_maps_to (s := S) (t := Icc 3 R) (g := fun D : Finset ℕ ↦ D.card)
      (by
        intro D hD
        have hd := (IncompatibleConnectedDeficit.mem_sources G D r).mp (mem_filter.mp hD).1
        exact mem_Icc.mpr ⟨(mem_filter.mp hD).2, by omega⟩) (fun D ↦ |infiniteCenteredCoefficient L D|)
    calc
      _ = ∑ s ∈ Icc 3 R, ∑ D ∈ S.filter (fun D ↦ D.card = s), |infiniteCenteredCoefficient L D| := hsplit.symm
      _ ≤ ∑ _s ∈ Icc 3 R, (N : ℝ) ^ (-1 + ε / 4) := by
        apply sum_le_sum
        intro s hs
        apply le_trans _ (ha N (by omega) L hband s (mem_Icc.mp hs).1 (mem_Icc.mp hs).2 G hG)
        apply sum_le_sum_of_subset_of_nonneg
        · intro D hD
          obtain ⟨hDS, hcard⟩ := mem_filter.mp hD
          exact mem_powersetCard.mpr ⟨((IncompatibleConnectedDeficit.mem_sources G D r).mp (mem_filter.mp hDS).1).1, hcard⟩
        · intro D _ _
          exact abs_nonneg _
      _ = ((Icc 3 R).card : ℝ) * (N : ℝ) ^ (-1 + ε / 4) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show (Icc 3 R).card ≤ R + 1 by rw [Nat.card_Icc]; omega))
        (Real.rpow_nonneg hn.le _)
  have hdef (D : Finset ℕ) (hD : D ∈ S) :
      IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L 1 ≤
        (N : ℝ) ^ (-1 / 2 + ε / 4) := by
    obtain ⟨hDG, _hDNe, hDCard⟩ := (IncompatibleConnectedDeficit.mem_sources G D r).mp (mem_filter.mp hD).1
    have hDN := hDG.trans hG
    apply he N (by omega) L hband G hG D hDN (by omega)
    exact IntersectionExceptional.span_le_raw D L (by
      intro x hx
      have h := (mem_Ico.mp (hDN hx)).1
      omega)
  have hweighted : (∑ D ∈ S, |infiniteCenteredCoefficient L D| *
      IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L 1) ≤
      ((R + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    calc
      _ ≤ ∑ D ∈ S, |infiniteCenteredCoefficient L D| * (N : ℝ) ^ (-1 / 2 + ε / 4) :=
        sum_le_sum fun D hD ↦ mul_le_mul_of_nonneg_left (hdef D hD) (abs_nonneg _)
      _ = (∑ D ∈ S, |infiniteCenteredCoefficient L D|) * (N : ℝ) ^ (-1 / 2 + ε / 4) := (sum_mul ..).symm
      _ ≤ (((R + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 + ε / 4)) * (N : ℝ) ^ (-1 / 2 + ε / 4) :=
        mul_le_mul_of_nonneg_right hsource (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hn]; congr 2; ring
  have hindWeak : FamilyIndependentMass.independentMass F L ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) :=
    hind.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))
  have hpair : AllPairExtensionDeficit.deficit G L 1 ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) :=
    ((AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L 1 (by norm_num)).trans
      (hd N (by omega) L hband)).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))
  have hfinite := IncompatibleHigherDeficit.finite_bound G L r (by omega) F hF hq
  have hraw : (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤
      ((R : ℝ) + 3) * (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    have hcast : ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 := by push_cast; rfl
    rw [hcast] at hweighted
    linarith only [hfinite, hindWeak, hpair, hweighted]
  exact hraw.trans (by convert hf N (by omega) using 1; congr 1; ring)

end PaperP1.SharpIncompatibleActivityUnderInputs
