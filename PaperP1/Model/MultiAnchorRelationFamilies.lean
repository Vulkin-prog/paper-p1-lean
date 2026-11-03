module

public import PaperP1.Model.MultiAnchorFamilyMass
public import PaperP1.Arithmetic.MultiAnchorRelationCertificate
public import PaperP1.Combinatorics.MultiAnchorGraph

/-! # Block-dependent physical relation witnesses and the actual saturation cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorRelationFamilies

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.FiniteFamilyEnumeration
  PaperP1.MultiAnchorFamilyMass PaperP1.MultiAnchorGraph
open PaperP1.ModerateCertificateCount (Unmarked)
open PaperP1.WindowCertificateFamilies (vertices mem_vertices)

local instance multiAnchorFamiliesPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def Witnesses (t B : ℕ) (Y T : ℝ) (I : Finset ℕ) : Prop :=
  ∀ a : I, Unmarked B Y T a.val → ∃ w : I → Fin B → F₂,
    (∀ j, (∑ i, w j i) = 0) ∧ t ≤ (PaperP1.BinaryEvenSelections.selected (w a)).card ∧
      (∑ j : I, ∑ i, w j i • parityVec (j.val - 1 + i.val)) = 0

theorem physical_relation {r t B : ℕ} (I : Finset ℕ) (n : Fin r → ℕ)
    (hinj : Function.Injective n) (hset : tupleSet n = I) (Y T : ℝ)
    (hw : Witnesses t B Y T I) (a : Fin r) (hunmarked : Unmarked B Y T (n a)) :
    ∃ w : Fin r → Fin B → F₂, (∀ j, (∑ i, w j i) = 0) ∧
      t ≤ (PaperP1.BinaryEvenSelections.selected (w a)).card ∧
      (∑ j, ∑ i, w j i • parityVec (n j - 1 + i.val)) = 0 := by
  classical
  let f : Fin r → I := fun j ↦ ⟨n j, by
    rw [← hset]
    exact mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j heq ↦ hinj (congrArg Subtype.val heq), ?_⟩
    intro x
    have hx : x.val ∈ tupleSet n := hset.symm ▸ x.property
    obtain ⟨j, _, hj⟩ := mem_image.mp hx
    exact ⟨j, Subtype.ext hj⟩
  let e := Equiv.ofBijective f hf
  obtain ⟨u, heven, hcard, hsum⟩ := hw (e a) hunmarked
  refine ⟨fun j ↦ u (e j), fun j ↦ heven (e j), hcard, ?_⟩
  exact (Equiv.sum_comp e (fun j : I ↦ ∑ i, u j i • parityVec (j.val - 1 + i.val))).trans hsum

theorem noncertified_admissible {r t B N : ℕ} (I : Finset ℕ)
    (hI : I ⊆ dyadicBlock N) (Y T : ℝ) (hY : (B : ℝ) ≤ Y)
    (hw : Witnesses t B Y T I) (hnot : ¬ Certified t r B N Y T I) :
    PaperP1.GraphStarPartition.Admissible (graph t B N Y)
      (vertices N (PaperP1.MarkedWindowCount.marked B N Y T)) (vertices N I) := by
  classical
  unfold Certified at hnot
  push Not at hnot
  obtain ⟨n, hinj, hset, hno⟩ := hnot
  have hn (j : Fin r) : n j ∈ Ico N (2 * N) := by
    apply hI
    rw [← hset]
    exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
  intro x hx
  by_cases hm : x.val ∈ PaperP1.MarkedWindowCount.marked B N Y T
  · exact Or.inl ((mem_vertices N _ x).mpr hm)
  · have hunmarked : Unmarked B Y T x.val := by
      by_contra hnot
      exact hm ((PaperP1.MarkedWindowCount.mem_marked _ _ _ _ _).mpr ⟨x.property, hnot⟩)
    have hxI := (mem_vertices N I x).mp hx
    have hxset : x.val ∈ tupleSet n := hset.symm ▸ hxI
    obtain ⟨a, _, ha⟩ := mem_image.mp hxset
    obtain ⟨w, _heven, hcard, htotal⟩ := physical_relation I n hinj hset Y T hw a
      (ha.symm ▸ hunmarked)
    obtain hcert | ⟨j, hj⟩ := PaperP1.MultiAnchorRelationCertificate.coordinate_alternative
      n hn hinj Y T hY a w hcard htotal (ha.symm ▸ hunmarked)
    · exact False.elim (hno hcert)
    · let y : Vertex N := ⟨n j, hn j⟩
      have hyI : y.val ∈ I := by
        rw [← hset]
        exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
      refine Or.inr ⟨y, (mem_vertices N I y).mpr hyI, ?_⟩
      change PaperP1.MultiAnchorSaturation.Edge t B N Y x.val (n j) ∨
        PaperP1.MultiAnchorSaturation.Edge t B N Y (n j) x.val
      exact Or.inl (ha ▸ hj)

end PaperP1.MultiAnchorRelationFamilies
