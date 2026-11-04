module

public import PaperP1.Asymptotics.ConnectedCompressedTripleMassUnderInputs
public import PaperP1.Model.FiniteInteriorUnitEdges

/-! # One explicit finite geometric bundle controls all fixed interior channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCompressedInteriorMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure Parameters where
  sourceDegree : ℕ
  generalSize : ℕ
  ordinarySize : ℕ
  typeCap : ℕ

structure Hypotheses (p : Parameters) (b : ℕ) (ε : ℝ) : Prop where
  sourceCover : UniformSourceSurfaceCover.UniformCover p.generalSize
    (AsymmetricComponentHostCount.sizeCap (2 * b + 1) (ε / 128)) p.sourceDegree
  ordinaryCover : UniformOrdinarySurfaceCover.UniformCover p.ordinarySize (p.typeCap + 1)
  sourceCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.sourceDegree + 2).choose 2 + p.generalSize) M
  ordinaryCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.ordinarySize + 3) M

theorem uniform_channel (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b ε →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ConnectedCompressedTripleMassUnderInputs.mass N a b L ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Ds, kg, ko, K, _hDs, _hK, h⟩ :=
    ConnectedCompressedTripleMassUnderInputs.uniform_mass a b ha hab hb2a hcop C ε hε
  exact ⟨⟨Ds, kg, ko, K⟩, fun hg ↦ h hg.sourceCover hg.ordinaryCover hg.sourceCurves hg.ordinaryCurves⟩

def hosts (N L Q : ℕ) : Finset (Finset ℕ) :=
  univ.biUnion fun ab : FiniteInteriorUnitEdges.channels Q ↦
    ConnectedCompressedTripleMassUnderInputs.hosts N ab.val.1 ab.val.2 L

def mass (N L Q : ℕ) : ℝ := ∑ T ∈ hosts N L Q, infiniteJointMoment L T

theorem mem_hosts {N L Q : ℕ} {T : Finset ℕ} :
    T ∈ hosts N L Q ↔ ∃ ab ∈ FiniteInteriorUnitEdges.channels Q,
      T ∈ ConnectedCompressedTripleMassUnderInputs.hosts N ab.1 ab.2 L := by
  constructor
  · intro hT
    obtain ⟨ab, _hab, hT⟩ := mem_biUnion.mp hT
    exact ⟨ab.val, ab.property, hT⟩
  · rintro ⟨ab, hab, hT⟩
    exact mem_biUnion.mpr ⟨⟨ab, hab⟩, mem_univ _, hT⟩

theorem uniform_mass (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → Parameters,
      (∀ ab, Hypotheses (p ab) ab.val.2 (ε / 2)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L Q ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  have hch (ab : FiniteInteriorUnitEdges.channels Q) : ∃ p : Parameters, Hypotheses p ab.val.2 (ε / 2) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ConnectedCompressedTripleMassUnderInputs.mass N ab.val.1 ab.val.2 L ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) := by
    obtain ⟨ha, hab, hb2a, hcop, _haQ, _hbQ⟩ := FiniteInteriorUnitEdges.channel_data ab.property
    exact uniform_channel ab.val.1 ab.val.2 ha hab hb2a hcop C (ε / 2) (by positivity)
  choose p hp using hch
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption
    ((FiniteInteriorUnitEdges.channels Q).card : ℝ) (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  choose Nc _hNc hc using fun ab ↦ hp ab (hgeo ab)
  refine ⟨max 4 (max (univ.sup Nc) Nf), by omega, ?_⟩
  intro N hN L hcrit
  have hthreshold (ab : FiniteInteriorUnitEdges.channels Q) : Nc ab ≤ N :=
    (le_sup (f := Nc) (mem_univ ab)).trans (by omega)
  calc
    _ ≤ ∑ ab : FiniteInteriorUnitEdges.channels Q,
        ConnectedCompressedTripleMassUnderInputs.mass N ab.val.1 ab.val.2 L :=
      GraphStarWeights.sum_biUnion_le_nonneg univ _ _ (infiniteJointMoment_nonneg L)
    _ ≤ ∑ _ab : FiniteInteriorUnitEdges.channels Q, (N : ℝ) ^ (-4 / 3 + ε / 2) :=
      sum_le_sum fun ab _ ↦ hc ab N (hthreshold ab) L hcrit
    _ = ((FiniteInteriorUnitEdges.channels Q).card : ℝ) * (N : ℝ) ^ (-4 / 3 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ _ := by
      simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)

end PaperP1.FiniteCompressedInteriorMass
