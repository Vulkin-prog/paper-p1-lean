module

public import PaperP1.Algebra.RationalMapFieldDegree
public import Mathlib.FieldTheory.Relrank

/-! # The degree tower for an actual rational graph in a field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalGraphFieldTower

open Polynomial IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def evaluation (x : E) (hx : Transcendental F x) : RatFunc F →ₐ[F] E :=
  (adjoin F {x}).val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom

theorem evaluation_polynomial (x : E) (hx : Transcendental F x) (p : F[X]) :
    evaluation x hx (algebraMap F[X] (RatFunc F) p) = aeval x p := by
  simp [evaluation, ← IntermediateField.aeval_coe]

theorem evaluation_quotient (x : E) (hx : Transcendental F x) (p q : F[X]) :
    evaluation x hx (RationalMapFieldDegree.quotient p q) = aeval x p / aeval x q := by
  simp [RationalMapFieldDegree.quotient, evaluation_polynomial]

theorem map_top (x : E) (hx : Transcendental F x) :
    (⊤ : IntermediateField F (RatFunc F)).map (evaluation x hx) = adjoin F {x} := by
  ext z
  constructor
  · rintro ⟨f, _, rfl⟩
    exact (RatFunc.algEquivOfTranscendental x hx f).property
  · intro hz
    obtain ⟨f, hf⟩ := (RatFunc.algEquivOfTranscendental x hx).surjective ⟨z, hz⟩
    exact ⟨f, Set.mem_univ f, congrArg Subtype.val hf⟩

theorem map_adjoin (x : E) (hx : Transcendental F x) (p q : F[X]) :
    (adjoin F {RationalMapFieldDegree.quotient p q}).map (evaluation x hx) =
      adjoin F {aeval x p / aeval x q} := by
  rw [IntermediateField.adjoin_map, Set.image_singleton, evaluation_quotient]

theorem graph_subfield_le (x : E) (hx : Transcendental F x) (p q : F[X]) :
    adjoin F {aeval x p / aeval x q} ≤ adjoin F {x} := by
  apply adjoin_simple_le_iff.mpr
  rw [← evaluation_quotient x hx p q]
  exact (RatFunc.algEquivOfTranscendental x hx (RationalMapFieldDegree.quotient p q)).property

theorem graph_relative_degree (x : E) (hx : Transcendental F x) (p q : F[X])
    (hq : q ≠ 0) (hcop : IsCoprime p q) :
    relfinrank (adjoin F {aeval x p / aeval x q}) (adjoin F {x}) =
      max p.natDegree q.natDegree := by
  have h := relfinrank_map_map (adjoin F {RationalMapFieldDegree.quotient p q}) ⊤
    (evaluation x hx)
  rw [map_adjoin, map_top, relfinrank_top_right, RationalMapFieldDegree.extension_rank p q hq hcop] at h
  exact h

theorem graph_tower_degree (x : E) (hx : Transcendental F x) (p q : F[X])
    (hq : q ≠ 0) (hcop : IsCoprime p q) :
    Module.finrank (adjoin F {aeval x p / aeval x q}) E =
      max p.natDegree q.natDegree * Module.finrank (adjoin F {x}) E := by
  rw [← relfinrank_mul_finrank_top (graph_subfield_le x hx p q),
    graph_relative_degree x hx p q hq hcop]

theorem exact_graph_degree (x : E) (hx : Transcendental F x) (p q : F[X])
    (hq : q ≠ 0) (hcop : IsCoprime p q) (a : ℕ)
    (hpositive : 0 < Module.finrank (adjoin F {x}) E)
    (hdegree : Module.finrank (adjoin F {aeval x p / aeval x q}) E =
      a * Module.finrank (adjoin F {x}) E) :
    max p.natDegree q.natDegree = a := by
  rw [graph_tower_degree x hx p q hq hcop] at hdegree
  exact Nat.eq_of_mul_eq_mul_right hpositive hdegree

end PaperP1.RationalGraphFieldTower
