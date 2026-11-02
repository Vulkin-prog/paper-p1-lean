module

public import PaperP1.Algebra.BinaryIncidenceShortVectors
public import PaperP1.Combinatorics.LabelledEdgeCore
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Tactic.Abel

/-! # Actual bounded incidence routes and the forest rank bound inside a ball -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortIncidenceRoutes

open Finset PaperP1.GreedyShortKernel PaperP1.LabelledEdgeCore

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {V E : Type*}
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableEq E := Classical.decEq _
local instance : AddCommGroup (E →₀ ZMod 2) := inferInstance
local instance (U : Submodule (ZMod 2) (E →₀ ZMod 2)) : AddCommGroup U := Submodule.addCommGroup U
local instance (U : Submodule (ZMod 2) (E →₀ ZMod 2)) : Module (ZMod 2) U := U.module

def point (v : V) : V → ZMod 2 := Pi.single v 1

theorem point_twice (v : V) : point v + point v = 0 := by
  funext u
  exact CharTwo.add_self_eq_zero (point v u)

def Route (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) (S : Finset E)
    (root v : V) (r : ℕ) : Prop :=
  ∃ w : E →₀ ZMod 2, w.support ⊆ S ∧ w.support.card ≤ r ∧ f w = point root + point v

theorem support_add_card_le (p q : E →₀ ZMod 2) :
    (p + q).support.card ≤ p.support.card + q.support.card :=
  (card_le_card Finsupp.support_add).trans (card_union_le _ _)

theorem support_sub_card_le (p q : E →₀ ZMod 2) :
    (p - q).support.card ≤ p.support.card + q.support.card :=
  (card_le_card Finsupp.support_sub).trans (card_union_le _ _)

theorem kernel_zero_of_no_short (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (S : Finset E) (k : ℕ) (hno : ¬ HasShortVector f S k) (w : E →₀ ZMod 2)
    (hs : w.support ⊆ S) (hk : w.support.card ≤ k) (hw : f w = 0) : w = 0 := by
  by_contra h
  apply hno
  exact ⟨⟨w, hw⟩, (fun hz ↦ h (congrArg Subtype.val hz)), hs, hk⟩

theorem route_self (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (S : Finset E) (root : V) (r : ℕ) : Route f S root root r := by
  refine ⟨0, by simp, by simp, ?_⟩
  rw [map_zero, point_twice]

theorem route_mono (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    {S T : Finset E} {root v : V} {r s : ℕ} (h : Route f S root v r)
    (hST : S ⊆ T) (hrs : r ≤ s) : Route f T root v s := by
  obtain ⟨w, hw, hk, hf⟩ := h
  exact ⟨w, hw.trans hST, hk.trans hrs, hf⟩

theorem extend_boundary (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (p : E →₀ ZMod 2) (root u v : V) (e : E)
    (hp : f p = point root + point u)
    (he : f (Finsupp.single e 1) = point u + point v) :
    f (p + Finsupp.single e 1) = point root + point v := by
  rw [map_add, hp, he]
  calc
    point root + point u + (point u + point v) = point root + (point u + point u) + point v := by abel
    _ = point root + point v := by rw [point_twice, add_zero]

theorem route_step (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) (S : Finset E)
    (root u v : V) (r : ℕ) (e : E) (heS : e ∈ S)
    (he : f (Finsupp.single e 1) = point u + point v)
    (h : Route f S root u r) : Route f S root v (r + 1) := by
  obtain ⟨p, hp, hk, hf⟩ := h
  refine ⟨p + Finsupp.single e 1, ?_, ?_, extend_boundary f p root u v e hf he⟩
  · exact Finsupp.support_add.trans (union_subset hp (by simpa using heS))
  · have hc := support_add_card_le p (Finsupp.single e 1)
    simp only [Finsupp.support_single e one_ne_zero, card_singleton] at hc
    omega

theorem route_edge_identity (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (S : Finset E) (root u v : V) (r : ℕ) (e : E) (heS : e ∈ S)
    (he : f (Finsupp.single e 1) = point u + point v)
    (hno : ¬ HasShortVector f S (2 * r + 1)) (p q : E →₀ ZMod 2)
    (hps : p.support ⊆ S) (hpr : p.support.card ≤ r) (hpf : f p = point root + point u)
    (hqs : q.support ⊆ S) (hqr : q.support.card ≤ r) (hqf : f q = point root + point v) :
    Finsupp.single e 1 = q - p := by
  have hmap : f (p + Finsupp.single e 1 - q) = 0 := by
    rw [map_sub, extend_boundary f p root u v e hpf he, hqf, sub_self]
  have hs : (p + Finsupp.single e 1 - q).support ⊆ S :=
    Finsupp.support_sub.trans (union_subset
      (Finsupp.support_add.trans (union_subset hps (by simpa using heS))) hqs)
  have hk : (p + Finsupp.single e 1 - q).support.card ≤ 2 * r + 1 := by
    have h₁ := support_add_card_le p (Finsupp.single e 1)
    have h₂ := support_sub_card_le (p + Finsupp.single e 1) q
    simp only [Finsupp.support_single e one_ne_zero, card_singleton] at h₁
    omega
  have hz := kernel_zero_of_no_short f S (2 * r + 1) hno _ hs hk hmap
  have heq : p + Finsupp.single e 1 = q := sub_eq_zero.mp hz
  rw [← heq]
  abel

theorem inside_card_le_routes (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (left right : E → V) (S : Finset E) (U : Finset V) (root : V) (r : ℕ)
    (hcol : ∀ e ∈ S, f (Finsupp.single e 1) = point (left e) + point (right e))
    (hno : ¬ HasShortVector f S (2 * r + 1))
    (hroutes : ∀ v ∈ U, Route f S root v r) : (inside left right S U).card ≤ U.card := by
  choose p hps hpr hpf using fun v : U ↦ hroutes v.val v.property
  let W := Submodule.span (ZMod 2) (Set.range p)
  let : Module.Finite (ZMod 2) W := Module.Finite.span_of_finite (ZMod 2) (Set.finite_range p)
  have he_mem (e : inside left right S U) : Finsupp.single e.val (1 : ZMod 2) ∈ W := by
    obtain ⟨heS, hel, her⟩ := (mem_inside left right S U e.val).mp e.property
    rw [route_edge_identity f S root (left e.val) (right e.val) r e.val heS
      (hcol e.val heS) hno (p ⟨left e.val, hel⟩) (p ⟨right e.val, her⟩)
      (hps _) (hpr _) (hpf _) (hps _) (hpr _) (hpf _)]
    exact W.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  let v : inside left right S U → W := fun e ↦ ⟨Finsupp.single e.val 1, he_mem e⟩
  have hli : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp W.subtype
    exact (Finsupp.linearIndependent_single_one (R := ZMod 2) (ι := E)).comp Subtype.val Subtype.val_injective
  have hcard := hli.fintype_card_le_finrank
  have hrank := finrank_range_le_card (R := ZMod 2) p
  simpa only [Fintype.card_coe] using hcard.trans hrank

end PaperP1.ShortIncidenceRoutes
