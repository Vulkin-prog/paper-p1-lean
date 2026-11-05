module

public import PaperP1.Model.FixedPairExtensions
public import PaperP1.Model.TwoTargetPrimitiveData
public import PaperP1.Asymptotics.RelativeOriginalWindowMass
public import PaperP1.Asymptotics.SharpPairTargetDeficit
public import PaperP1.Asymptotics.CriticalActualMean

/-! # The literal fixed-order pair extension deficit without unproved inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPairExtensionDeficit

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FamilyIndependentMass PaperP1.FixedPairExtensions

theorem article_15_7 (k : ℕ) (hk : 1 ≤ k) (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        FixedPairExtensions.deficit G L k ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let M := 2 * (2 : ℝ) ^ C
  let K := (M + 1) ^ k
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : 0 ≤ K := pow_nonneg (by linarith) _
  obtain ⟨NP, _hNP, hp⟩ := SharpPairTargetDeficit.article_11_1 C δ hδ
  have hrel (h : Fin (k + 1)) := RelativeOriginalWindowMass.uniform_mass h.val 2 C δ hδ
  choose Nh hNh hh using hrel
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (K * ((k : ℝ) + 1))
    (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NP + NM + NG + NA + univ.sup Nh, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hmean (e : Finset ℕ) : (∑ x ∈ G \ e, infiniteMarginal x L) ≤ M := by
    calc
      _ ≤ ∑ x ∈ dyadicBlock N, infiniteMarginal x L :=
        sum_le_sum_of_subset_of_nonneg (fun _ hx ↦ hG (mem_sdiff.mp hx).1)
          (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 :=
        (CountObservables.countMoment_one (subset_refl _)).symm
      _ ≤ _ := (hm N (by omega) L hband).2
  have hseed (e : Finset ℕ) (he : e ∈ G.powersetCard 2) (h : ℕ) (hmem : h ∈ Icc 2 k) :
      independentMass (RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L)) L ≤
        (N : ℝ) ^ (-1 + δ) := by
    obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp he
    let i : Fin (k + 1) := ⟨h, by have hle := (mem_Icc.mp hmem).2; omega⟩
    have hNi : Nh i ≤ univ.sup Nh := le_sup (f := Nh) (mem_univ i)
    have hW : sourceSpace e L ≤
        ⨆ a, squareClassSpace (FiniteFamilyEnumeration.centres e hecard a) L :=
      (TwoTargetPrimitiveData.source_enumeration e L hecard).le
    have htarget := hh i N (by omega) L hband (FiniteFamilyEnumeration.centres e hecard)
      (fun a ↦ hG (FiniteFamilyEnumeration.centres_mem G e hecard hesub a)) (sourceSpace e L) hW
      (G \ e) (fun _ hx ↦ hG (mem_sdiff.mp hx).1)
    calc
      _ ≤ (N : ℝ) ^ (-(h : ℝ) / 2 + δ) := htarget.2
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by
        have htwo : (2 : ℝ) ≤ h := by exact_mod_cast (mem_Icc.mp hmem).1
        linarith only [htwo])
  have hfinite := FixedPairExtensions.finite_bound G L k hL hk M ((N : ℝ) ^ (-1 + δ)) hM
    (Real.rpow_nonneg hn.le _) (fun e _ ↦ hmean e) hseed
  have hpairs := hp N (by omega) L hband G hG
  have hcombined : (N : ℝ) ^ (-1 + δ) * HeterogeneousRunConversion.absoluteMass G L ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (-1 + δ) * (N : ℝ) ^ (-2 / 3 + δ) :=
        mul_le_mul_of_nonneg_left hpairs.2 (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ ((-1 + δ) + (-2 / 3 + δ)) := (Real.rpow_add hn _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε])
  have hunary : IndependentTargetDeficit.deficit G L ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) :=
    hpairs.1.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε]))
  calc
    _ ≤ K * (IndependentTargetDeficit.deficit G L +
        (k : ℝ) * ((N : ℝ) ^ (-1 + δ) * HeterogeneousRunConversion.absoluteMass G L)) := by
      convert hfinite using 1
      dsimp [K, HeterogeneousRunConversion.absoluteMass, HeterogeneousPoissonCharlierConversion.absolutePairMass]
      ring
    _ ≤ K * ((N : ℝ) ^ (-3 / 2 + ε / 2) + (k : ℝ) * (N : ℝ) ^ (-3 / 2 + ε / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hunary (mul_le_mul_of_nonneg_left hcombined (by positivity))) hK
    _ = (K * ((k : ℝ) + 1)) * (N : ℝ) ^ (-3 / 2 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FixedPairExtensionDeficit
