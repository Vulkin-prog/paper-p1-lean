module

public import PaperP1.Asymptotics.UniformGeometricSystemsUnderInputs
public import PaperP1.Asymptotics.GeneralGraphHostCount
public import PaperP1.Asymptotics.DegreeOneGraphHostCount
public import PaperP1.Asymptotics.FixedPartnerComponentCount

/-! # Literal data and all conclusions of companion T1.7

The only hypotheses in the geometric bundle are the three previously isolated
surface/curve properties at explicit finite dimensions. No host count, root
extraction, curve-degree conclusion or target estimate is a bundle field.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountStatement

open Finset PaperP1.SplitRadicalPointHeight PaperP1.Model PaperP1.LargePrimeGraph
  PaperP1.PinnedGraphResolution PaperP1.LargePrimeGraphResolution

structure Parameters where
  systemDegree : ℕ
  systemSize : ℕ
  linearSize : ℕ
  denseDegree : ℕ
  denseSize : ℕ
  typedSize : ℕ

structure Hypotheses (p : Parameters) (K a : ℕ) (η : ℝ) : Prop where
  systemCover : UniformSourceSurfaceCover.UniformCover p.systemSize K p.systemDegree
  systemCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.systemDegree + 2).choose 2 + p.systemSize) M
  linearCover : UniformOrdinarySurfaceCover.UniformCover p.linearSize K
  linearCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.linearSize + 3) M
  denseCover : UniformSourceSurfaceCover.UniformCover p.denseSize
    (GeneralGraphHostCount.sizeCap η) p.denseDegree
  denseCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.denseDegree + 2).choose 2 + p.denseSize) M
  typedCover : UniformOrdinarySurfaceCover.UniformCover p.typedSize (a + 1)
  typedCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.typedSize + 3) M

structure System (N B n K : ℕ) (A₀ : ℝ) where
  coefficients : Fin n → ℤ
  left : Fin n → Finset ℤ
  right : Fin n → Finset ℤ
  nonzero : ∀ i, coefficients i ≠ 0
  left_disjoint : Pairwise (fun i j ↦ Disjoint (left i) (left j))
  right_disjoint : Pairwise (fun i j ↦ Disjoint (right i) (right j))
  left_nonempty : ∀ i, (left i).Nonempty
  right_nonempty : ∀ i, (right i).Nonempty
  degree_cap : ∀ i, (left i).card + (right i).card ≤ K
  left_bound : ∀ i, ∀ z ∈ left i, z.natAbs ≤ B
  right_bound : ∀ i, ∀ z ∈ right i, z.natAbs ≤ B
  coefficient_height : ∀ i, ((coefficients i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀
  sourceSet : Finset ℤ
  targetSet : Finset ℤ
  left_subset : ∀ i, left i ⊆ sourceSet
  right_subset : ∀ i, right i ⊆ targetSet
  hosts : Finset (ℤ × ℤ)
  dyadic : ∀ p ∈ hosts, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧
    p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N
  admissible : ∀ p ∈ hosts, SourceCurvePointCover.Admissible sourceSet targetSet p
  roots : ∀ p ∈ hosts, ∃ w : Fin n → ℤ,
    ∀ i, w i ^ 2 = coefficients i * integerProduct (left i) p.1 * integerProduct (right i) p.2

def SystemsBound (C A₀ ε : ℝ) (K Jexp : ℕ) (p : Parameters) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
    ∀ n : ℕ, p.systemSize + (K + 1) * p.linearSize ≤ n → ∀ s : System N B n K A₀,
      (s.hosts.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε) ∧
        ((∀ i, (s.right i).card = 1) → (s.hosts.card : ℝ) ≤ A * (N : ℝ) ^ ε)

def DenseGraphBound (C ε η : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (ℕ × ℕ),
    (∀ xy ∈ F, xy.1 ∈ dyadicBlock N ∧ xy.2 ∈ dyadicBlock N) →
    (∀ xy ∈ F, ¬ CompressedTargetAlignment.Aligned 1 xy.1 xy.2 L) →
    (∀ xy ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount xy.1 xy.2 L) →
    (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)

def TypedGraphBound (C ε : ℝ) (a k : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (ℕ × ℕ),
    (∀ xy ∈ F, xy.1 ∈ dyadicBlock N ∧ xy.2 ∈ dyadicBlock N) →
    (∀ xy ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned 1 xy.1 xy.2 L) →
    (∀ xy ∈ F, k ≤ (DegreeOneGraphHostCount.components xy.1 xy.2 L a).card ∨
      k ≤ (DegreeOneGraphHostCount.components xy.2 xy.1 L a).card) →
    (F.card : ℝ) ≤ A * (N : ℝ) ^ ε

def FixedPartnerBound (C ε : ℝ) (K : ℕ) : Prop :=
  ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
    ∀ S : Finset ℕ, (∀ y ∈ S, y ∈ dyadicBlock N) →
    (∀ y ∈ S, ∃ c : (largePrimeGraph x y L).ConnectedComponent,
      ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c ∧
      (TwoBlockComponentSquares.vertices x y L c).card ≤ K ∧
      2 ≤ (TwoBlockComponentSquares.vertices x y L c).toRight.card) →
    (S.card : ℝ) ≤ (N : ℝ) ^ ε

def OneVariableBound (K : ℕ) (ε : ℝ) : Prop :=
  ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
    (∀ A : Finset ℤ, 2 ≤ A.card → A.card ≤ K → ∀ c : ℤ, c ≠ 0 → ∀ S : Finset ℕ,
      (∀ n ∈ S, (∀ a ∈ A, 0 < (n : ℤ) + a ∧ LinearKernelFibres.value n a ≤ N ^ 2) ∧
        IsSquare (c * ∏ a ∈ A, ((n : ℤ) + a))) → (S.card : ℝ) ≤ (N : ℝ) ^ ε) ∧
    (∀ A B : Finset ℤ, A.Nonempty → B.Nonempty → Disjoint A B → A.card ≤ K → B.card ≤ K →
      ∀ c d : ℤ, c ≠ 0 → d ≠ 0 → ∀ S : Finset ℕ,
      (∀ n ∈ S, (∀ a ∈ A ∪ B, 0 < (n : ℤ) + a ∧ LinearKernelFibres.value n a ≤ N ^ 2) ∧
        IsSquare (c * ∏ a ∈ A, ((n : ℤ) + a)) ∧
        IsSquare (d * ∏ b ∈ B, ((n : ℤ) + b))) → (S.card : ℝ) ≤ (N : ℝ) ^ ε)

structure Assertions (C A₀ ε η : ℝ) (K Jexp a : ℕ) (p : Parameters) : Prop where
  systems : SystemsBound C A₀ ε K Jexp p
  denseGraph : DenseGraphBound C ε η
  typedGraph : TypedGraphBound C ε a p.typedSize
  fixedPartner : FixedPartnerBound C ε K
  oneVariable : OneVariableBound K ε

end PaperP1.UniformGeometricCountStatement
