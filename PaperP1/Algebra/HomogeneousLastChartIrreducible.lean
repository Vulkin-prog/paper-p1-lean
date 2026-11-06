module

public import PaperP1.Algebra.LastChartQuotient
public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.GradedQuotientChartMap
public import PaperP1.Algebra.GradedChartBasis
public import PaperP1.Algebra.HomogeneousLastChartNonzero
public import PaperP1.Algebra.HomogeneousMonicGenerator
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Homogeneous irreducibility survives the actual last chart; monicity gives full degree and chart nonemptiness -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.HomogeneousLastChartIrreducible
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type*} [Field F] (n : ℕ)
abbrev CoordinateRing (q : MvPolynomial (Fin (n+1)) F) := MvPolynomial (Fin (n+1)) F ⧸ Ideal.span {q}

local instance idealPrime (q : MvPolynomial (Fin (n+1)) F) [h : Fact (Irreducible q)] :
    (Ideal.span ({q} : Set (MvPolynomial (Fin (n+1)) F))).IsPrime :=
  (Ideal.span_singleton_prime h.out.ne_zero).mpr h.out.prime

def piece (q : MvPolynomial (Fin (n+1)) F) (m : ℕ) : Submodule F (CoordinateRing n q) :=
  PaperP1.HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin (n+1)) F) (Ideal.span {q}) m

theorem ideal_homogeneous (q : MvPolynomial (Fin (n+1)) F) {d : ℕ} (hq : q.IsHomogeneous d) :
    (Ideal.span ({q} : Set (MvPolynomial (Fin (n+1)) F))).IsHomogeneous
      (homogeneousSubmodule (Fin (n+1)) F) := by
  apply Ideal.homogeneous_span
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨d, hq⟩

@[instance_reducible]
def grading (q : MvPolynomial (Fin (n+1)) F) {d : ℕ} (hq : q.IsHomogeneous d) :
    GradedAlgebra (piece n q) :=
  PaperP1.HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin (n+1)) F)
    (Ideal.span {q}) (ideal_homogeneous n q hq)

def chartCoordinate (q : MvPolynomial (Fin (n+1)) F) : CoordinateRing n q :=
  Ideal.Quotient.mk (Ideal.span {q}) (X (Fin.last n))

theorem chartCoordinate_mem (q : MvPolynomial (Fin (n+1)) F) : chartCoordinate n q ∈ piece n q 1 :=
  Submodule.mem_map.mpr ⟨X (Fin.last n), isHomogeneous_X F (Fin.last n), rfl⟩

theorem chartCoordinate_ne_zero (q : MvPolynomial (Fin (n+1)) F)
    (hZ : X (Fin.last n) ∉ Ideal.span ({q} : Set (MvPolynomial (Fin (n+1)) F))) :
    chartCoordinate n q ≠ 0 := fun hz ↦ hZ (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem chartIdeal_eq (q : MvPolynomial (Fin (n+1)) F) {d : ℕ} (hq : q.IsHomogeneous d) :
    letI := grading n q hq
    (RingHom.ker (PaperP1.HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin (n+1)) F)
      (Ideal.span {q})).toRingHom).map
      ((PaperP1.LastChartQuotient.originalEquiv n).toRingHom.comp
        (PaperP1.GradedDehomogenization.map (homogeneousSubmodule (Fin (n+1)) F) (PaperP1.LastChartQuotient.variable_mem n))) =
      Ideal.span {PaperP1.LastChartPolynomial.dehomogenize q} := by
  let := grading n q hq
  have he : (PaperP1.LastChartQuotient.originalEquiv n).toRingHom.comp
      (PaperP1.GradedDehomogenization.map (homogeneousSubmodule (Fin (n+1)) F) (PaperP1.LastChartQuotient.variable_mem n)) =
      PaperP1.LastChartPolynomial.dehomogenize := by
    apply RingHom.ext
    intro P
    exact PaperP1.LastChartQuotient.originalEquiv_dehomogenization n P
  have hk : RingHom.ker (PaperP1.HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin (n+1)) F)
      (Ideal.span {q})).toRingHom = Ideal.span {q} := Ideal.mk_ker
  rw [hk, he, Ideal.map_span, Set.image_singleton]

def equiv (q : MvPolynomial (Fin (n+1)) F) {d : ℕ} (hq : q.IsHomogeneous d) :
    letI := grading n q hq
    Away (piece n q) (chartCoordinate n q) ≃+*
      MvPolynomial (Fin n) F ⧸ Ideal.span {PaperP1.LastChartPolynomial.dehomogenize q} := by
  let := PaperP1.HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin (n+1)) F)
    (Ideal.span {q}) (ideal_homogeneous n q hq)
  let := grading n q hq
  exact (PaperP1.GradedQuotientChartMap.transportEquiv
    (PaperP1.HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin (n+1)) F) (Ideal.span {q}))
    (PaperP1.HomogeneousQuotientGrading.mk_surjective _ _) (PaperP1.LastChartQuotient.variable_mem n)
    (PaperP1.LastChartQuotient.originalEquiv n)).trans (Ideal.quotEquivOfEq (chartIdeal_eq n q hq))

theorem affineQuotient_isDomain (q : MvPolynomial (Fin (n+1)) F) [Fact (Irreducible q)]
    {d : ℕ} (hq : q.IsHomogeneous d)
    (hZ : X (Fin.last n) ∉ Ideal.span ({q} : Set (MvPolynomial (Fin (n+1)) F))) :
    IsDomain (MvPolynomial (Fin n) F ⧸ Ideal.span {PaperP1.LastChartPolynomial.dehomogenize q}) := by
  let := grading n q hq
  let : IsDomain (Away (piece n q) (chartCoordinate n q)) :=
    PaperP1.GradedChartBasis.chart_isDomain (piece n q) (chartCoordinate_ne_zero n q hZ)
  exact (equiv n q hq).symm.injective.isDomain (equiv n q hq).symm.toRingHom

theorem irreducible (q : MvPolynomial (Fin (n+1)) F) (hi : Irreducible q)
    {d : ℕ} (hq : q.IsHomogeneous d)
    (hZ : X (Fin.last n) ∉ Ideal.span ({q} : Set (MvPolynomial (Fin (n+1)) F))) :
    Irreducible (PaperP1.LastChartPolynomial.dehomogenize q) := by
  let : Fact (Irreducible q) := ⟨hi⟩
  let := affineQuotient_isDomain n q hq hZ
  have hp : (Ideal.span ({PaperP1.LastChartPolynomial.dehomogenize q} : Set (MvPolynomial (Fin n) F))).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  exact ((Ideal.span_singleton_prime (PaperP1.HomogeneousLastChartNonzero.chart_ne_zero q hq hi.ne_zero)).mp hp).irreducible

theorem outer_degree (q : MvPolynomial (Fin (n+1)) F) {d : ℕ} (hq : q.IsHomogeneous d)
    (hm : (finSuccEquiv F n q).Monic) : (finSuccEquiv F n q).natDegree = d := by
  have hq0 : q ≠ 0 := fun hz ↦ hm.ne_zero (by rw [hz, map_zero])
  have hh := PaperP1.HomogeneousMonicGenerator.homogeneous q (ideal_homogeneous n q hq) hm
  exact (hh.totalDegree hq0).symm.trans (hq.totalDegree hq0)

theorem last_not_mem (q : MvPolynomial (Fin (n+2)) F) {d : ℕ} (hd : 0 < d)
    (hq : q.IsHomogeneous d) (hm : (finSuccEquiv F (n+1) q).Monic) :
    X (Fin.last (n+1)) ∉ Ideal.span ({q} : Set (MvPolynomial (Fin (n+2)) F)) := by
  intro hmem
  have hh := map_dvd (finSuccEquiv F (n+1)).toRingHom (Ideal.mem_span_singleton.mp hmem)
  change finSuccEquiv F (n+1) q ∣ finSuccEquiv F (n+1) (X (Fin.last (n+1))) at hh
  have he : finSuccEquiv F (n+1) (X (Fin.last (n+1))) = Polynomial.C (X (Fin.last n)) := by
    change finSuccEquiv F (n+1) (X (Fin.last n).succ) = _
    exact finSuccEquiv_X_succ
  rw [he] at hh
  have hle := Polynomial.natDegree_le_of_dvd hh
    (Polynomial.C_ne_zero.mpr (X_ne_zero (Fin.last n) : (X (Fin.last n) : MvPolynomial (Fin (n+1)) F) ≠ 0))
  rw [Polynomial.natDegree_C, outer_degree (n+1) q hq hm] at hle
  exact (Nat.not_le_of_lt hd) hle

theorem monic_irreducible (q : MvPolynomial (Fin (n+2)) F) (hi : Irreducible q)
    {d : ℕ} (hd : 0 < d) (hq : q.IsHomogeneous d) (hm : (finSuccEquiv F (n+1) q).Monic) :
    Irreducible (PaperP1.LastChartPolynomial.dehomogenize q) :=
  irreducible (n+1) q hi hq (last_not_mem n q hd hq hm)

end PaperP1.HomogeneousLastChartIrreducible
