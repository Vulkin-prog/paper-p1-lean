module

public import PaperP1.Algebra.AffineCurveFunctionField
public import PaperP1.Algebra.OffsetCommonQuotientGraph

/-! # Identification of the actual irreducible curve equation with its reduced graph relation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineCurveGraphPresentation

open Polynomial PaperP1.AffineCurveFunctionField PaperP1.BivariateGraphSpecialization

variable {F : Type*} [Field F]

theorem relation_linear (p q : F[X]) : relation p q = C (-q) * X + C p := by
  simp only [relation, map_neg]
  ring

theorem relation_irreducible (p q : F[X]) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    Irreducible (relation p q) := by
  rw [relation_linear]
  exact irreducible_C_mul_X_add_C (neg_ne_zero.mpr hq) hcop.symm.neg_left.isRelPrime

theorem relation_degree (p q : F[X]) (hq : q ≠ 0) : (relation p q).natDegree = 1 := by
  rw [relation_linear, natDegree_linear (neg_ne_zero.mpr hq)]

theorem curve_divides_relation (C₀ : F[X][X]) [Fact (Irreducible C₀)] (p q : F[X])
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q) :
    C₀ ∣ relation p q := by
  apply (specialize_zero_iff C₀ _).mp
  rw [← coordinates_evaluation, relation_evaluation, hgraph, sub_self]

theorem associated_relation (C₀ : F[X][X]) [Fact (Irreducible C₀)] (p q : F[X])
    (hq : q ≠ 0) (hcop : IsCoprime p q)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q) :
    Associated C₀ (relation p q) :=
  (Fact.out : Irreducible C₀).associated_of_dvd (relation_irreducible p q hq hcop)
    (curve_divides_relation C₀ p q hgraph)

theorem curve_degree_one (C₀ : F[X][X]) [Fact (Irreducible C₀)] (p q : F[X])
    (hq : q ≠ 0) (hcop : IsCoprime p q)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q) :
    C₀.natDegree = 1 := by
  have hass := associated_relation C₀ p q hq hcop hgraph
  have hle := natDegree_le_of_dvd hass.dvd (relation_irreducible p q hq hcop).ne_zero
  have hge := natDegree_le_of_dvd hass.symm.dvd (Fact.out : Irreducible C₀).ne_zero
  rw [relation_degree p q hq] at hle hge
  omega

theorem point_iff_graph (C₀ : F[X][X]) [Fact (Irreducible C₀)] (p q : F[X])
    (hq : q ≠ 0) (hcop : IsCoprime p q)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q)
    (X Y : F) : Polynomial.aevalAeval X Y C₀ = 0 ↔ p.eval X = Y * q.eval X := by
  have hass := associated_relation C₀ p q hq hcop hgraph
  have hzero : Polynomial.aevalAeval X Y C₀ = 0 ↔ Polynomial.aevalAeval X Y (relation p q) = 0 := by
    exact (hass.map (Polynomial.aevalAeval X Y).toRingHom).eq_zero_iff
  rw [hzero, relation_evaluation, sub_eq_zero]
  rfl

end PaperP1.AffineCurveGraphPresentation
