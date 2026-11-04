module

public import PaperP1.Model.FiniteChannelTripleMass
public import PaperP1.Asymptotics.ExceptionalSourcePalmMass

/-! # The actual finite-family triple asymptotic of companion T2.8

One threshold precedes all critical lengths and independently varying
private channel cutoffs. The leading coefficient counts every actual
ordered triple once, even when it contains several good pairs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteChannelTripleTheoremUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteChannelTripleMass
  PaperP1.FixedChannelFullPalmUnderInputs PaperP1.GoodEdgePositivePalm
  PaperP1.FiniteCompressedInteriorMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem companion_T2_8 (F : Finset (ℕ × ℕ)) (hFne : F.Nonempty)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (D : ℕ × ℕ → ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : F → Parameters, (∀ ab, Hypotheses (p ab) ab.val.2 (ε / 4)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ × ℕ → ℕ,
        (∀ ab ∈ F, 2 * ab.2 * (L + 1) ≤ H ab ∧ H ab ≤ D ab * (L + 1)) →
        0 < amplitude F N L H ∧
        |GoodPairGeneratedTriples.orderedMass N L (rawEdges F N L H) -
          3 * FiniteChannelHierarchy.nominalMean N L * amplitude F N L H| ≤
            amplitude F N L H * (N : ℝ) ^ (-nu F + ε) := by
  have hlocal (ab : F) : ∃ p : Parameters, Hypotheses p ab.val.2 (ε / 4) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 * ab.val.2 * (L + 1) ≤ H → H ≤ D ab.val * (L + 1) →
        0 < beta N H ab.val.1 ab.val.2 L ∧
        normalized N H ab.val.1 ab.val.2 L (dyadicBlock N) ≤ (N : ℝ) ^ (-eta ab.val.1 ab.val.2 + ε / 2) ∧
        |mean N H ab.val.1 ab.val.2 L - FiniteChannelHierarchy.nominalMean N L| ≤
          (N : ℝ) ^ (-min (eta ab.val.1 ab.val.2) (1 / 2) + ε / 2) := by
    obtain ⟨ha, hab, hint, hcop⟩ := hF ab.val ab.property
    have hh := FixedChannelFullPalmUnderInputs.companion_T2_7 ab.val.1 ab.val.2 (D ab.val)
      ha hab hint hcop C (ε / 2) (by positivity)
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hh
  choose p hp using hlocal
  obtain ⟨NG, _hNG, hg⟩ := FixedPrivateChannelDisjoint.uniform_geometry F
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1⟩) C
  obtain ⟨ND, _hND, hd⟩ := FixedPrivateChannelDisjoint.uniform_disjoint F
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1, (hF ab hab).2.2.2⟩) C
  obtain ⟨NB, _hNB, hb⟩ := ExceptionalSourcePalmMass.uniform_bound C 2 (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 9 (-nu F + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  choose Nc _hNc hc using fun ab ↦ hp ab (hgeo ab)
  refine ⟨max 10 (max (univ.sup Nc) (max NG (max ND (max NB NA)))), by omega, ?_⟩
  intro N hN L hband H hcut
  have hthreshold (ab : F) : Nc ab ≤ N := (le_sup (f := Nc) (mem_univ ab)).trans (by omega)
  have hchannel (ab : F) := hc ab N (hthreshold ab) L (H ab.val) hband
    (hcut ab.val ab.property).1 (hcut ab.val ab.property).2
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgeom := hg N (by omega) L hband
  have hlarge (ab : ℕ × ℕ) (hab : ab ∈ F) := (hgeom.2.2 ab hab).1
  have hdis := hd N (by omega) L hband H
  have hE := source_data (by omega : 2 ≤ N) hgeom.1
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1, (hF ab hab).2.2.2⟩) hlarge H
  have hbeta (ab : ℕ × ℕ) (hab : ab ∈ F) : 0 < beta N (H ab) ab.1 ab.2 L := (hchannel ⟨ab, hab⟩).1
  have hM : amplitude F N L H = 2 * ∑ ab ∈ F, beta N (H ab) ab.1 ab.2 L := by
    rw [amplitude_eq (by omega : 2 ≤ N) (fun ab hab ↦ (hF ab hab).2.1) hlarge H hdis,
      sum_edges F N L H hdis]
    rfl
  have hMpos : 0 < amplitude F N L H := by
    rw [hM]
    have hsum : 0 < ∑ ab ∈ F, beta N (H ab) ab.1 ab.2 L :=
      sum_pos' (fun ab hab ↦ (hbeta ab hab).le) (by obtain ⟨ab, hab⟩ := hFne; exact ⟨ab, hab, hbeta ab hab⟩)
    positivity
  have hmean (ab : ℕ × ℕ) (hab : ab ∈ F) :
      |mean N (H ab) ab.1 ab.2 L - FiniteChannelHierarchy.nominalMean N L| ≤ (N : ℝ) ^ (-nu F + ε / 2) := by
    have hnu : nu F ≤ min (eta ab.1 ab.2) (1 / 2) := le_min (nu_le_eta hab) (nu_le_half F)
    exact (hchannel ⟨ab, hab⟩).2.2.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hnu]))
  have hpalm (ab : ℕ × ℕ) (hab : ab ∈ F) :
      normalized N (H ab) ab.1 ab.2 L (dyadicBlock N) ≤ (N : ℝ) ^ (-nu F + ε / 2) :=
    (hchannel ⟨ab, hab⟩).2.1.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by have hh := nu_le_eta hab; linarith only [hh]))
  have hbad (e : Finset ℕ) (he : e ∈ edges F N L H) :
      ((GoodPairGeneratedTriples.bad N L e).card : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (N : ℝ) ^ (-nu F + ε / 2) :=
    (hb N (by omega) L hband e (hE e he).1 (by have hh := (hE e he).2.1; omega)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by have hh := nu_le_half F; linarith only [hh]))
  have hfinite := finite_approximation (by omega : 2 ≤ N) (fun ab hab ↦ (hF ab hab).2.1)
    hlarge H hdis hE ((N : ℝ) ^ (-nu F + ε / 2)) (by positivity) hbeta hmean hpalm hbad
  rw [raw_ordered_mass_eq (by omega : 2 ≤ N) (fun ab hab ↦ (hF ab hab).2.1) hlarge H]
  refine ⟨hMpos, hfinite.trans ?_⟩
  calc
    _ = amplitude F N L H * (9 * (N : ℝ) ^ (-nu F + ε / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [show (-nu F + ε / 2) + ε / 2 = -nu F + ε by ring] using ha N (by omega)) hMpos.le

end PaperP1.FiniteChannelTripleTheoremUnderInputs
