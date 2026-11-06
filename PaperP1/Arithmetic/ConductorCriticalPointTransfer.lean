module

public import PaperP1.Arithmetic.GeneratedMonicCriticalPointCount
public import PaperP1.Algebra.ConductorPointExtension
public import PaperP1.Arithmetic.SplitRadicalCanonicalPointCount

/-! # Uniform image point bounds from literal source, conductor and monic polynomial data

The source and exceptional counts are internal proofs. The conductor, image
generation and actual polynomial identities remain explicit structural premises.
No general P3 point estimate is supplied or discharged by this assembly.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ConductorCriticalPointTransfer
open Polynomial Finset
open scoped Classical
variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]

theorem cardinality_le_source_plus [Fintype F] [Finite (A →ₐ[F] F)] (p : ℕ) [CharP F p]
    (S : Subalgebra F A) (δ : S) (hconductor : ∀ a : A, (δ : A)*a ∈ S)
    (v : Fin 2 → S) (z : S) (hgen : Algebra.adjoin F (Set.range (Fin.cons z v)) = ⊤)
    (P : (MvPolynomial (Fin 2) F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hpos : 0 < P.natDegree) (d : ℕ) (hdegree : P.natDegree ≤ d) (hlt : d < p)
    (hcoef : ∀ i, (P.coeff i).totalDegree ≤ d)
    (hequation : P.eval₂ (MvPolynomial.aeval v).toRingHom z = 0)
    (hδ : δ = P.derivative.eval₂ (MvPolynomial.aeval v).toRingHom z) :
    Nat.card (S →ₐ[F] F) ≤ Nat.card (A →ₐ[F] F) + 2*d^3*Fintype.card F := by
  let : Finite (S →ₐ[F] F) := PaperP1.GeneratedThreeCoordinatePoints.points_finite (Fin.cons z v) hgen
  let : Fintype (S →ₐ[F] F) := Fintype.ofFinite _
  let : Fintype (A →ₐ[F] F) := Fintype.ofFinite _
  have hdenom : PaperP1.ConductorPointExtension.denominator S (δ : A) hconductor = δ :=
    Subtype.ext rfl
  have ht := PaperP1.ConductorPointExtension.total_cardinality_le (Ω := F) S (δ : A) hconductor
  rw [hdenom] at ht
  have hb := PaperP1.GeneratedMonicCriticalPointCount.exceptional_cardinality p v z δ hgen
    P hmonic hP hpos d hdegree hlt hcoef hequation hδ
  have hbN : Fintype.card {φ : S →ₐ[F] F // φ δ = 0} ≤ 2*d^3*Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using hb
  have htN := ht.trans (Nat.add_le_add_left hbN (Fintype.card (A →ₐ[F] F)))
  simpa only [Nat.card_eq_fintype_card] using htN

section Split
open PaperP1.SplitRadicalCoordinateAlgebra PaperP1.SplitRadicalFiniteFieldPointCount
open PaperP1.SplitBranchPrimeCertificate PaperP1.BranchShiftReductionCertificate
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra

theorem split_cardinality_le (p : ℕ) [Fact p.Prime] (k : ℕ) (c : Fin k → ZMod p)
    (I J : Fin k → Finset ℤ)
    (S : Subalgebra (ZMod p) (CoordinateAlgebra (List.finRange k) c I J)) (δ : S)
    (hconductor : ∀ a : CoordinateAlgebra (List.finRange k) c I J, (δ : CoordinateAlgebra (List.finRange k) c I J)*a ∈ S)
    (v : Fin 2 → S) (z : S) (hgen : Algebra.adjoin (ZMod p) (Set.range (Fin.cons z v)) = ⊤)
    (P : (MvPolynomial (Fin 2) (ZMod p))[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hpos : 0 < P.natDegree) (d : ℕ) (hdegree : P.natDegree ≤ d) (hlt : d < p)
    (hcoef : ∀ i, (P.coeff i).totalDegree ≤ d)
    (hequation : P.eval₂ (MvPolynomial.aeval v).toRingHom z = 0)
    (hδ : δ = P.derivative.eval₂ (MvPolynomial.aeval v).toRingHom z) :
    Nat.card (S →ₐ[ZMod p] ZMod p) ≤ (points c I J).card + 2*d^3*p := by
  let : Finite (CoordinateAlgebra (List.finRange k) c I J →ₐ[ZMod p] ZMod p) :=
    PaperP1.BivariateQuadraticTowerPoints.points_finite (radicands (List.finRange k) c I J)
  have ht := cardinality_le_source_plus p S δ hconductor v z hgen
    P hmonic hP hpos d hdegree hlt hcoef hequation hδ
  rw [PaperP1.SplitRadicalCanonicalPointCount.cardinality k c I J, ZMod.card] at ht
  exact ht

theorem uniform_upper_bound (k D d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (c : Fin k → ZMod p) (I J : Fin k → Finset ℤ),
      (support I J).card ≤ D →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ certificate (support I J) →
      ∀ (S : Subalgebra (ZMod p) (CoordinateAlgebra (List.finRange k) c I J)) (δ : S),
      (∀ a : CoordinateAlgebra (List.finRange k) c I J, (δ : CoordinateAlgebra (List.finRange k) c I J)*a ∈ S) →
      ∀ (v : Fin 2 → S) (z : S), Algebra.adjoin (ZMod p) (Set.range (Fin.cons z v)) = ⊤ →
      ∀ P : (MvPolynomial (Fin 2) (ZMod p))[X], P.Monic → Irreducible P →
      0 < P.natDegree → P.natDegree ≤ d →
      (∀ i, (P.coeff i).totalDegree ≤ d) →
      P.eval₂ (MvPolynomial.aeval v).toRingHom z = 0 →
      δ = P.derivative.eval₂ (MvPolynomial.aeval v).toRingHom z →
        ((Nat.card (S →ₐ[ZMod p] ZMod p) : ℕ) : ℝ) ≤ (1+η)*(p : ℝ)^2 := by
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨K, hK⟩ := PaperP1.SplitRadicalUniformPointEstimate.uniform_upper_bound (ι := Fin k) D (η/2) hhalf
  obtain ⟨L, hL⟩ := exists_nat_ge (4 * (d : ℝ)^3 / η)
  refine ⟨max K (max (d+1) L), ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro c I J hD hI hJ hne hnot S δ hconductor v z hgen P hmonic hP hpos hdegree hcoef hequation hδ
  have hdp : d < p := by omega
  have ht := split_cardinality_le p k c I J S δ hconductor v z hgen
    P hmonic hP hpos d hdegree hdp hcoef hequation hδ
  have htR : ((Nat.card (S →ₐ[ZMod p] ZMod p) : ℕ) : ℝ) ≤
      ((points c I J).card : ℝ) + 2*(d : ℝ)^3*(p : ℝ) := by exact_mod_cast ht
  have hsource := hK I J hD hI hJ hne p hp (by omega) hnot c
  have hLp : (L : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show L ≤ p by omega)
  have hC : 4*(d : ℝ)^3 ≤ (p : ℝ)*η := (div_le_iff₀ hη).mp (hL.trans hLp)
  have hmul := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  nlinarith only [htR, hsource, hmul]
end Split
end PaperP1.ConductorCriticalPointTransfer
