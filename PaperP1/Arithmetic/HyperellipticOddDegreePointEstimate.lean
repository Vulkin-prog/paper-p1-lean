module

public import PaperP1.Algebra.HyperellipticTangentAuxiliary
public import PaperP1.Algebra.HyperellipticAuxiliaryDimensionGap
public import PaperP1.Analysis.HyperellipticAuxiliaryParameters

/-! # Unconditional uniform leading-coefficient-one counts for actual odd-degree quadratic curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticOddDegreePointEstimate

open Polynomial HyperellipticMonomialIndex HyperellipticFiniteFieldPoints
open HyperellipticAuxiliaryDimensionGap HyperellipticAuxiliaryParameters
open scoped Classical

theorem uniform_upper_bound (g : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ f : (ZMod p)[X], f.natDegree = 2 * g + 1 →
        ((points f).card : ℝ) ≤ (1 + η) * (p : ℝ) := by
  obtain ⟨m, K, hm, hK3, hKm, hKd, hKC, hsmall, herror⟩ := exists_parameters g η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro f hdegree
  have hodd : Odd f.natDegree := by
    rw [hdegree]
    exact ⟨g, by omega⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hA : p - 1 < Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have hm0 : 0 < m := by omega
  have hmp : m ≤ p := by omega
  have hdim := dimension_gap g m p hm (le_trans hKd hlarge) (le_trans hKC hlarge)
  have hdimF : (∑ r : Fin m, Fintype.card (Index f.natDegree
      ((p - 1) + (m + g) + r.val * (f.natDegree - 2)))) <
      Fintype.card (Index f.natDegree (p - 1)) * Fintype.card (Index f.natDegree (m + g)) := by
    simpa only [hdegree] using hdim
  have hb := HyperellipticTangentAuxiliary.point_bound_of_dimension p hp hchar f hodd
    (p - 1) (m + g) m hA hm0 hmp hdimF
  simp only [ZMod.card, hdegree] at hb
  exact hb.trans (point_upper_arithmetic g m p η hm0 hsmall (herror p hlarge))

theorem uniform_degree_cap (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ f : (ZMod p)[X], Odd f.natDegree → f.natDegree ≤ D →
        ((points f).card : ℝ) ≤ (1 + η) * (p : ℝ) := by
  choose K hK using (fun g : Fin (D + 1) ↦ uniform_upper_bound g.val η hη)
  refine ⟨Finset.univ.sup K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro f hodd hD
  obtain ⟨g, hg⟩ := hodd
  have hgD : g < D + 1 := by omega
  have hKg : K ⟨g, hgD⟩ ≤ p := (Finset.le_sup (Finset.mem_univ ⟨g, hgD⟩)).trans hlarge
  exact hK ⟨g, hgD⟩ p hp hKg f (by omega)

end PaperP1.HyperellipticOddDegreePointEstimate
