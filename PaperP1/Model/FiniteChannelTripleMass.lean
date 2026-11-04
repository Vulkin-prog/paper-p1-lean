module

public import PaperP1.Model.GoodPairGeneratedTriples
public import PaperP1.Model.FixedPrivateChannelDisjoint
public import PaperP1.Asymptotics.FixedChannelFullPalmUnderInputs

/-! # A finite channel family generates actual triples with a proved finite error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteChannelTripleMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SourceConditionalDeviations PaperP1.FixedChannelFullPalmUnderInputs
  PaperP1.GoodEdgePositivePalm PaperP1.GoodPairGeneratedTriples

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def edges (F : Finset (ℕ × ℕ)) (N L : ℕ) (H : ℕ × ℕ → ℕ) : Finset (Finset ℕ) :=
  F.biUnion fun ab ↦ CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L

def rawEdges (F : Finset (ℕ × ℕ)) (N L : ℕ) (H : ℕ × ℕ → ℕ) : Finset (Finset ℕ) :=
  F.biUnion fun ab ↦ PrivateChannelActivity.pairs N (H ab) ab.1 ab.2 L

theorem edges_eq_filter (F : Finset (ℕ × ℕ)) (N L : ℕ) (H : ℕ × ℕ → ℕ) :
    edges F N L H = (rawEdges F N L H).filter fun e ↦ 0 < infiniteJointMoment L e := by
  ext e
  constructor
  · intro he
    obtain ⟨ab, hab, he⟩ := mem_biUnion.mp he
    obtain ⟨heRaw, hq⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨ab, hab, heRaw⟩, hq⟩
  · intro he
    obtain ⟨heRaw, hq⟩ := mem_filter.mp he
    obtain ⟨ab, hab, he⟩ := mem_biUnion.mp heRaw
    exact mem_biUnion.mpr ⟨ab, hab, mem_filter.mpr ⟨he, hq⟩⟩

theorem raw_data {F : Finset (ℕ × ℕ)} {N L : ℕ} (hN : 2 ≤ N)
    (hF : ∀ ab ∈ F, ab.1 < ab.2) (hlarge : ∀ ab ∈ F, (ab.1 + ab.2) * (L + 1) < N)
    (H : ℕ × ℕ → ℕ) : ∀ e ∈ rawEdges F N L H, e ⊆ dyadicBlock N ∧ e.card = 2 := by
  intro e he
  obtain ⟨ab, hab, he⟩ := mem_biUnion.mp he
  exact PrivateChannelActivity.pair_data hN (hF ab hab) (hlarge ab hab) he

theorem raw_ordered_mass_eq {F : Finset (ℕ × ℕ)} {N L : ℕ} (hN : 2 ≤ N)
    (hF : ∀ ab ∈ F, ab.1 < ab.2) (hlarge : ∀ ab ∈ F, (ab.1 + ab.2) * (L + 1) < N)
    (H : ℕ × ℕ → ℕ) :
    orderedMass N L (rawEdges F N L H) = orderedMass N L (edges F N L H) := by
  rw [edges_eq_filter]
  exact (ordered_source_restoration N L _ (raw_data hN hF hlarge H)).symm

def amplitude (F : Finset (ℕ × ℕ)) (N L : ℕ) (H : ℕ × ℕ → ℕ) : ℝ :=
  ∑ ab ∈ F, PrivateChannelSources.channelMass N (H ab) ab.1 ab.2 L

def indices (F : Finset (ℕ × ℕ)) : Finset (Option (ℕ × ℕ)) := insert none (F.image some)

def exponent : Option (ℕ × ℕ) → ℝ
  | none => 1 / 2
  | some ab => eta ab.1 ab.2

def nu (F : Finset (ℕ × ℕ)) : ℝ :=
  (indices F).inf' ⟨none, mem_insert_self _ _⟩ exponent

theorem nu_le_half (F : Finset (ℕ × ℕ)) : nu F ≤ 1 / 2 := by
  exact Finset.inf'_le exponent (show none ∈ indices F from mem_insert_self _ _)

theorem nu_le_eta {F : Finset (ℕ × ℕ)} {ab : ℕ × ℕ} (hab : ab ∈ F) : nu F ≤ eta ab.1 ab.2 := by
  have hmem : some ab ∈ indices F := mem_insert_of_mem (mem_image.mpr ⟨ab, hab, rfl⟩)
  exact Finset.inf'_le exponent hmem

theorem le_nu_iff (F : Finset (ℕ × ℕ)) (x : ℝ) :
    x ≤ nu F ↔ x ≤ 1 / 2 ∧ ∀ ab ∈ F, x ≤ eta ab.1 ab.2 := by
  constructor
  · intro hh
    exact ⟨hh.trans (nu_le_half F), fun _ hab ↦ hh.trans (nu_le_eta hab)⟩
  · rintro ⟨hhalf, hchannels⟩
    apply Finset.le_inf'
    intro o ho
    rcases mem_insert.mp ho with rfl | ho
    · exact hhalf
    · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ho
      exact hchannels ab hab

theorem nu_ge_third (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2) :
    (1 / 3 : ℝ) ≤ nu F := by
  apply (le_nu_iff F (1 / 3)).mpr
  refine ⟨by norm_num, ?_⟩
  intro ab hab
  exact (eta_bounds (hF ab hab).1 (hF ab hab).2.1 (hF ab hab).2.2.1 (hF ab hab).2.2.2).1

theorem sum_edges (F : Finset (ℕ × ℕ)) (N L : ℕ) (H : ℕ × ℕ → ℕ)
    (hdis : ∀ ab ∈ F, ∀ cd ∈ F, ab ≠ cd →
      Disjoint (CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L)
        (CompatibleChannelEdges.edges N (H cd) cd.1 cd.2 L)) (f : Finset ℕ → ℝ) :
    (∑ e ∈ edges F N L H, f e) = ∑ ab ∈ F, ∑ e ∈ CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L, f e :=
  sum_biUnion hdis

theorem source_data {F : Finset (ℕ × ℕ)} {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2)
    (hlarge : ∀ ab ∈ F, (ab.1 + ab.2) * (L + 1) < N) (H : ℕ × ℕ → ℕ) :
    ∀ e ∈ edges F N L H, e ⊆ dyadicBlock N ∧ e.card = 2 ∧
      0 < runRelativeNullity L e ∧ 0 < infiniteJointMoment L e := by
  intro e he
  obtain ⟨ab, hab, he⟩ := mem_biUnion.mp he
  obtain ⟨hreg, hcard, hdep, _hnull, hq, _hupper⟩ := CompatibleChannelEdges.edge_data hN
    (hF ab hab).1 (hF ab hab).2.1 (hF ab hab).2.2 (hlarge ab hab) hL he
  exact ⟨hreg.trans (RegularStarts.regularStarts_subset N L), hcard, hdep, hq⟩

theorem amplitude_eq {F : Finset (ℕ × ℕ)} {N L : ℕ} (hN : 2 ≤ N)
    (hF : ∀ ab ∈ F, ab.1 < ab.2) (hlarge : ∀ ab ∈ F, (ab.1 + ab.2) * (L + 1) < N)
    (H : ℕ × ℕ → ℕ)
    (hdis : ∀ ab ∈ F, ∀ cd ∈ F, ab ≠ cd →
      Disjoint (CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L)
        (CompatibleChannelEdges.edges N (H cd) cd.1 cd.2 L)) :
    amplitude F N L H = 2 * ∑ e ∈ edges F N L H, infiniteJointMoment L e := by
  rw [sum_edges F N L H hdis, mul_sum]
  apply sum_congr rfl
  intro ab hab
  have hh := CompatibleChannelEdges.joint_mass_eq (H := H ab) hN (hF ab hab) (hlarge ab hab)
  linarith only [hh]

theorem finite_approximation {F : Finset (ℕ × ℕ)} {N L : ℕ} (hN : 2 ≤ N)
    (hF : ∀ ab ∈ F, ab.1 < ab.2) (hlarge : ∀ ab ∈ F, (ab.1 + ab.2) * (L + 1) < N)
    (H : ℕ × ℕ → ℕ)
    (hdis : ∀ ab ∈ F, ∀ cd ∈ F, ab ≠ cd →
      Disjoint (CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L)
        (CompatibleChannelEdges.edges N (H cd) cd.1 cd.2 L))
    (hE : ∀ e ∈ edges F N L H, e ⊆ dyadicBlock N ∧ e.card = 2 ∧
      0 < runRelativeNullity L e ∧ 0 < infiniteJointMoment L e)
    (t : ℝ) (_ht : 0 ≤ t)
    (hbeta : ∀ ab ∈ F, 0 < beta N (H ab) ab.1 ab.2 L)
    (hmean : ∀ ab ∈ F, |mean N (H ab) ab.1 ab.2 L - FiniteChannelHierarchy.nominalMean N L| ≤ t)
    (hpalm : ∀ ab ∈ F, normalized N (H ab) ab.1 ab.2 L (dyadicBlock N) ≤ t)
    (hbad : ∀ e ∈ edges F N L H, ((bad N L e).card : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ t) :
    |orderedMass N L (edges F N L H) - 3 * FiniteChannelHierarchy.nominalMean N L * amplitude F N L H| ≤
      9 * amplitude F N L H * t := by
  let E := edges F N L H
  let B := ∑ e ∈ E, infiniteJointMoment L e
  let D := PairGeneratedTripleWeights.designated (dyadicBlock N) E (infiniteJointMoment L)
  let A := PairGeneratedTripleWeights.mass (dyadicBlock N) E (infiniteJointMoment L)
  let X := PairGeneratedTripleWeights.exceptional (dyadicBlock N) E (bad N L) (infiniteJointMoment L)
  let ell := FiniteChannelHierarchy.nominalMean N L
  have hBsum : B = ∑ ab ∈ F, beta N (H ab) ab.1 ab.2 L := sum_edges F N L H hdis _
  have hamp : amplitude F N L H = 2 * B := amplitude_eq hN hF hlarge H hdis
  have hD : D = ∑ ab ∈ F, beta N (H ab) ab.1 ab.2 L * mean N (H ab) ab.1 ab.2 L := by
    change PairGeneratedTripleWeights.designated (dyadicBlock N) E (infiniteJointMoment L) = _
    rw [designated_eq N L E (fun e he ↦ (hE e he).2.2.2), sum_edges F N L H hdis]
    apply sum_congr rfl
    intro ab hab
    unfold mean
    field_simp [(hbeta ab hab).ne']
  have hdiff : D - ell * B = ∑ ab ∈ F,
      beta N (H ab) ab.1 ab.2 L * (mean N (H ab) ab.1 ab.2 L - ell) := by
    rw [hD, hBsum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun _ _ ↦ by ring)
  have hmeanError : |D - ell * B| ≤ B * t := by
    rw [hdiff]
    calc
      _ ≤ ∑ ab ∈ F, |beta N (H ab) ab.1 ab.2 L * (mean N (H ab) ab.1 ab.2 L - ell)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ ab ∈ F, beta N (H ab) ab.1 ab.2 L * t := by
        apply sum_le_sum
        intro ab hab
        rw [abs_mul, abs_of_nonneg (hbeta ab hab).le]
        exact mul_le_mul_of_nonneg_left (hmean ab hab) (hbeta ab hab).le
      _ = _ := by rw [← sum_mul, ← hBsum]
  have hPositive : (∑ e ∈ E, infiniteJointMoment L e * positiveDeviation N L e) ≤ B * t := by
    rw [sum_edges F N L H hdis, hBsum, sum_mul]
    apply sum_le_sum
    intro ab hab
    have hh := (div_le_iff₀ (hbeta ab hab)).mp (hpalm ab hab)
    rw [iterated_mass] at hh
    simpa only [mul_comm, positiveDeviation] using hh
  have hX : X ≤ 2 * B * t := by
    have hx := exceptional_bound N L E (fun e he ↦ (hE e he).2.2.2)
    have hb : (∑ e ∈ E, infiniteJointMoment L e * ((bad N L e).card * (2 ^ L : ℝ)⁻¹ + positiveDeviation N L e)) ≤
        B * t + ∑ e ∈ E, infiniteJointMoment L e * positiveDeviation N L e := by
      calc
        _ ≤ ∑ e ∈ E, infiniteJointMoment L e * (t + positiveDeviation N L e) :=
          sum_le_sum (fun e he ↦ mul_le_mul_of_nonneg_left (add_le_add (hbad e he) le_rfl)
            (infiniteJointMoment_nonneg L e))
        _ = _ := by simp_rw [mul_add]; rw [sum_add_distrib, ← sum_mul]
    change X ≤ _ at hx
    linarith only [hx, hb, hPositive]
  have hOver : |A - D| ≤ X := finite_overcount hN E (fun e he ↦ ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1⟩)
  have hError : |A - ell * B| ≤ 3 * B * t := by
    have hh := abs_sub_le A D (ell * B)
    linarith only [hh, hOver, hX, hmeanError]
  have hOrdered := ordered_mass_eq N L E (fun e he ↦ ⟨(hE e he).1, (hE e he).2.1⟩)
  rw [hOrdered, hamp]
  change |6 * A - 3 * ell * (2 * B)| ≤ 9 * (2 * B) * t
  rw [show 6 * A - 3 * ell * (2 * B) = 6 * (A - ell * B) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  nlinarith only [hError]

end PaperP1.FiniteChannelTripleMass
