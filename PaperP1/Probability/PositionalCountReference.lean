module

public import PaperP1.Probability.PositionalCountProjection
public import PaperP1.Probability.PositionalCompoundPoisson

/-! # The total count of the positive single/pair field is the Hermite reference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCountReference

open Finset PaperP1.PositionalFiniteLaw PaperP1.PositionalCountProjection
  PaperP1.PositionalCompoundPoisson

variable {ι : Type*}

theorem sum_incidence (G : Finset ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, incidence E q x) = 2 * ∑ e ∈ E, q e := by
  classical
  unfold incidence
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro e he
  have hfilter : G.filter (fun x ↦ x ∈ e) = e := by
    ext x
    simp only [mem_filter]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨(hE e he).1 hx, hx⟩⟩
  rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul, (hE e he).2]
  norm_num

theorem parameter_admissible (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2)
    (hp : ∀ x ∈ G, 0 ≤ p x - incidence E q x) :
    2 * (∑ e ∈ E, q e) ≤ ∑ x ∈ G, p x := by
  have hh := sum_nonneg hp
  rw [sum_sub_distrib, sum_incidence G E q hE] at hh
  linarith only [hh]

theorem projection_target (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    projection (target G E p q) =
      HermiteReference.reference (∑ x ∈ G, p x) (2 * ∑ e ∈ E, q e) := by
  classical
  rw [target_exponential G E p q hE, projection_exp, map_add]
  simp only [map_sum, map_smul, projection_delta]
  have he : (∑ e ∈ E, q e • projection
      (CompletedPositionalLaw.ofFinite (difference e))) =
      (∑ e ∈ E, q e) • CompletedPoisson.delta ^ 2 := by
    calc
      _ = ∑ e ∈ E, q e • CompletedPoisson.delta ^ 2 :=
        sum_congr rfl (fun e he ↦ by rw [projection_difference, (hE e he).2])
      _ = _ := sum_smul.symm
  rw [he, ← sum_smul, HermiteReference.factorization, CompletedPoisson.poisson,
    ← NormedSpace.exp_add]
  congr 1
  rw [show (2 * ∑ e ∈ E, q e) / 2 = ∑ e ∈ E, q e by ring]

end PaperP1.PositionalCountReference
