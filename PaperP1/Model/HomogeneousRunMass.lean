module

public import PaperP1.Model.PrescribedTupleRank
public import PaperP1.Model.JointTupleSupport
public import PaperP1.Model.PrivateChannelRank
public import PaperP1.Model.PrimitiveNominalMass
public import PaperP1.Affine.CanonicalIndexTransport

/-! # Homogeneous rank weights are actual probabilities under the prime-sign law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousRunMass

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.RelativeSignIndependence PaperP1.WindowFamilyConditional
  PaperP1.FiniteFamilyEnumeration

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance : MeasurableSpace F₂ := ⊤
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def probability (L : ℕ) (I : Finset ℕ) : ℝ :=
  infiniteRademacherMeasure.real {ω | ∀ x ∈ I, infiniteStartBits x L ω = 0}

theorem bits_zero_iff_equal (x L : ℕ) (hL : 0 < L) (ω : InfiniteSample) :
    infiniteStartBits x L ω = 0 ↔
      ∀ i : Fin L, infiniteValueBit ω (x + i.val) = infiniteValueBit ω (x - 1) := by
  constructor
  · intro hh
    have hfirst : infiniteValueBit ω (x - 1) = infiniteValueBit ω x := by
      have hz := congrFun hh (⟨0, hL⟩ : Fin L)
      simpa only [infiniteStartBits, ite_true, Pi.zero_apply, add_eq_zero_iff_eq] using hz
    intro i
    by_cases hi : i.val = 0
    · simpa only [hi, Nat.add_zero] using hfirst.symm
    · have hz := congrFun hh i
      have heq : infiniteValueBit ω x = infiniteValueBit ω (x + i.val) := by
        simpa only [infiniteStartBits, hi, ite_false, Pi.zero_apply, add_eq_zero_iff_eq] using hz
      exact heq.symm.trans hfirst.symm
  · intro hh
    have hfirst : infiniteValueBit ω x = infiniteValueBit ω (x - 1) := by
      simpa only [Nat.add_zero] using hh (⟨0, hL⟩ : Fin L)
    funext i
    change infiniteStartBits x L ω i = 0
    by_cases hi : i.val = 0
    · simpa only [infiniteStartBits, hi, ite_true, add_eq_zero_iff_eq] using hfirst.symm
    · simpa only [infiniteStartBits, hi, ite_false, add_eq_zero_iff_eq] using
        hfirst.trans (hh i).symm

theorem tuple_probability {s L : ℕ} (x : Fin s → ℕ) :
    PrescribedTupleMass.joint L (fun _ ↦ 0) x = probability L (tupleSet x) := by
  unfold PrescribedTupleMass.joint probability
  congr 1
  ext ω
  change (∀ i, infiniteStartBits (x i) L ω = 0) ↔
    ∀ y ∈ tupleSet x, infiniteStartBits y L ω = 0
  simp only [tupleSet, mem_image, mem_univ, true_and, forall_exists_index]
  constructor
  · intro hh y i hi
    simpa only [← hi] using hh i
  · intro hh i
    exact hh (x i) i rfl

theorem tuple_rank {s L : ℕ} (x : Fin s → ℕ) :
    PrescribedTupleMass.joint L (fun _ ↦ 0) x =
      (2 ^ Module.finrank F₂ (⨆ i, squareClassSpace (x i) L : Submodule F₂ (ℕ →₀ F₂)) : ℝ)⁻¹ := by
  let M := (univ.sup x) + L
  have hcut : ∀ i, x i + L ≤ M := fun i ↦ Nat.add_le_add_right (le_sup (f := x) (mem_univ i)) L
  have hpos := CompatibleWindowPrescriptions.homogeneous_source_positive x hcut
  rcases PrescribedTupleRank.joint_zero_or_rank (L := L) (fun _ ↦ 0) x with hz | heq
  · change 0 < PrescribedTupleMass.joint L (fun _ ↦ 0) x at hpos
    rw [hz] at hpos
    exact False.elim (lt_irrefl 0 hpos)
  · exact heq

theorem probability_rank (L : ℕ) (I : Finset ℕ) :
    probability L I = (2 ^ SubspaceFamilyRank.rank (fun x ↦ squareClassSpace x L) I : ℝ)⁻¹ := by
  let x := centres I rfl
  have hs : tupleSet x = I := centres_tupleSet I rfl
  rw [← hs, ← tuple_probability, tuple_rank]
  rw [hs]
  congr 2
  change Module.finrank F₂ (⨆ i : Fin I.card, squareClassSpace ((enumeration I rfl i).val) L :
      Submodule F₂ (ℕ →₀ F₂)) =
    Module.finrank F₂ (⨆ i : I, squareClassSpace i.val L : Submodule F₂ (ℕ →₀ F₂))
  rw [CanonicalIndexTransport.span_reindex (fun i : I ↦ squareClassSpace i.val L) (enumeration I rfl)]

theorem probability_pos (L : ℕ) (I : Finset ℕ) : 0 < probability L I := by
  rw [probability_rank]
  positivity

theorem probability_antitone (L : ℕ) {I J : Finset ℕ} (hIJ : I ⊆ J) :
    probability L J ≤ probability L I :=
  measureReal_mono (fun _ hh x hx ↦ hh x (hIJ hx))

theorem nominal_singleton (L x : ℕ) : PrimitiveNominalMass.weight L {x} = (2 ^ L : ℝ)⁻¹ := by
  simp only [PrimitiveNominalMass.weight, card_singleton, pow_one,
    RetainedNullity.nullity_singleton, pow_zero, mul_one]

theorem nominal_empty (L : ℕ) : PrimitiveNominalMass.weight L ∅ = 1 := by
  simp only [PrimitiveNominalMass.weight, card_empty, pow_zero, relativeNullityOn_empty, one_mul]

theorem regular_weight {N L : ℕ} {I : Finset ℕ} (hI : I ⊆ RegularStarts.regularStarts N L) :
    probability L I = PrimitiveNominalMass.weight L I := by
  have hdim := rank_add_nullity_on (fun x ↦ squareClassSpace x L) I
  have hsum : (∑ x ∈ I, Module.finrank F₂ (squareClassSpace x L)) = I.card * L := by
    calc
      _ = ∑ _x ∈ I, L := sum_congr rfl (fun x hx ↦ (RegularStarts.mem_regularStarts.mp (hI hx)).2)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [hsum] at hdim
  have hscale : (((2 ^ L : ℝ)⁻¹) ^ I.card) = (2 ^ (I.card * L) : ℝ)⁻¹ := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm L I.card]
  rw [probability_rank, PrimitiveNominalMass.weight, hscale, ← hdim, pow_add]
  field_simp

theorem actual_joint_le (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    infiniteJointMoment L I ≤ probability L I := by
  let x := centres I rfl
  have hs : tupleSet x = I := centres_tupleSet I rfl
  rw [← hs, ← JointTupleSupport.prescribed_eq_support x hL, ← tuple_probability, tuple_rank]
  exact PrescribedTupleRank.joint_le_rank (fun _ ↦ startRhs L) x

theorem private_good_pair {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {xy : ℕ × ℕ}
    (hxy : xy ∈ PrivateChannelSources.goodSources N H a b L) :
    probability L {xy.1, xy.2} = ((2 ^ L : ℝ)⁻¹) ^ 2 *
      (2 ^ ((NormalizedUnitCount.units a b xy.1 xy.2 L).card - 1) : ℝ) := by
  have hpair : ({xy.1, xy.2} : Finset ℕ) ∈ PrivateChannelActivity.pairs N H a b L :=
    mem_image.mpr ⟨xy, hxy, rfl⟩
  rw [regular_weight (PrivateChannelRank.regular hN ha hab hpair), PrimitiveNominalMass.weight,
    card_pair_eq_two_iff.mpr (PrivateChannelSources.good_sources_order hN hab hlarge hxy).ne]
  have hr := PrivateChannelRank.source_nullity_eq hN ha hab hlarge hxy
  change runRelativeNullity L {xy.1, xy.2} = _ at hr
  rw [show relativeNullityOn (fun x ↦ squareClassSpace x L) {xy.1, xy.2} =
    (NormalizedUnitCount.units a b xy.1 xy.2 L).card - 1 from hr]

end PaperP1.HomogeneousRunMass
