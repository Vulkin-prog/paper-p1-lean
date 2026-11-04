module

public import PaperP1.Model.RelativeWindowFamilies
public import PaperP1.Arithmetic.PrefixParticipatingWindowCertificates
public import PaperP1.Combinatorics.AllFamilyEnumerations
public import PaperP1.Combinatorics.PrefixSaturationGraph
public import PaperP1.Combinatorics.GraphStarWeights
public import PaperP1.Asymptotics.PrefixMarkedWindowCount

/-! # Actual unordered participating families split into factorially counted certificates and marked saturation families -/

/-! The centre range in this module is the positive prefix [2,N+2),
with exactly N centres; no critical lower bound on a centre is assumed. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixWindowCertificateFamilies

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.FiniteFamilyEnumeration
  PaperP1.PrefixModerateCertificateCount PaperP1.PrefixSaturationGraph

def Certified (r B N : ℕ) (Y T : ℝ) (I : Finset ℕ) : Prop :=
  ∀ n : Fin r → ℕ, Function.Injective n → tupleSet n = I → HasCertificate r B N Y T n

def vertices (N : ℕ) (I : Finset ℕ) : Finset (Vertex N) := by
  classical
  exact univ.filter fun x ↦ x.val ∈ I

theorem mem_vertices (N : ℕ) (I : Finset ℕ) (x : Vertex N) : x ∈ vertices N I ↔ x.val ∈ I := by
  classical
  simp only [vertices, mem_filter, mem_univ, true_and]

theorem vertices_image (N : ℕ) (I : Finset ℕ) (hI : I ⊆ (Ico 2 (N + 2))) :
    (vertices N I).image Subtype.val = I := by
  classical
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact (mem_vertices N I y).mp hy
  · intro hx
    exact mem_image.mpr ⟨⟨x, hI hx⟩, (mem_vertices N I _).mpr hx, rfl⟩

theorem vertices_card (N : ℕ) (I : Finset ℕ) (hI : I ⊆ (Ico 2 (N + 2))) : (vertices N I).card = I.card := by
  classical
  have h := card_image_of_injective (vertices N I) Subtype.val_injective
  rw [vertices_image N I hI] at h
  exact h.symm

theorem covered_of_witnesses {r L : ℕ} (I : Finset ℕ) (n : Fin r → ℕ)
    (hinj : Function.Injective n) (hset : tupleSet n = I)
    (hw : RelativeWindowFamilies.Witnesses L ⊥ I) :
    RelativeBlockRelations.Covered (fun _ x ↦ NormalizedWindowSets.values x L) ∅ n := by
  classical
  let f : Fin r → I := fun j ↦ ⟨n j, by rw [← hset]; exact mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j heq ↦ hinj (congrArg Subtype.val heq), ?_⟩
    intro x
    have hx : x.val ∈ tupleSet n := hset.symm ▸ x.property
    obtain ⟨j, _, hj⟩ := mem_image.mp hx
    exact ⟨j, Subtype.ext hj⟩
  let e := Equiv.ofBijective f hf
  intro a
  obtain ⟨u, hua, hsum⟩ := hw (e a)
  refine ⟨fun j ↦ (u (e j)).val, ?_, ?_, ?_⟩
  · intro j
    rw [NormalizedWindowSets.space_values]
    exact (u (e j)).property
  · exact fun hz ↦ hua (Subtype.ext hz)
  · have hsum0 : (∑ x : I, (u x).val) = 0 := by simpa only [Submodule.mem_bot] using hsum
    have hzero : (∑ j, (u (e j)).val) = 0 :=
      (Equiv.sum_comp e (fun x : I ↦ (u x).val)).trans hsum0
    rw [hzero]
    exact Submodule.zero_mem _

theorem certified_count (r B N : ℕ) (Y T : ℝ) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ (Ico 2 (N + 2)) ∧ I.card = r)
    (hcert : ∀ I ∈ F, Certified r B N Y T I) :
    F.card * r.factorial ≤ (sourceTuples r B N Y T).card := by
  apply AllFamilyEnumerations.factorial_count_le F _ (fun I hI ↦ (hF I hI).2)
  intro I hI n hinj hset
  apply (mem_sourceTuples r B N Y T n).mpr
  refine ⟨?_, hcert I hI n hinj hset⟩
  intro i
  apply (hF I hI).1
  rw [← hset]
  exact mem_image.mpr ⟨i, mem_univ _, rfl⟩

theorem noncertified_admissible {r L N : ℕ} (I : Finset ℕ) (hI : I ⊆ (Ico 2 (N + 2)))
    (hN : 2 ≤ N) (Y T : ℝ) (hY : ((L + 1 : ℕ) : ℝ) ≤ Y)
    (hw : RelativeWindowFamilies.Witnesses L ⊥ I) (hnot : ¬ Certified r (L + 1) N Y T I) :
    GraphStarPartition.Admissible (graph (L + 1) N Y)
      (vertices N (PrefixMarkedWindowCount.marked (L + 1) N Y T)) (vertices N I) := by
  classical
  unfold Certified at hnot
  push Not at hnot
  obtain ⟨n, hinj, hset, hno⟩ := hnot
  have hn (j : Fin r) : n j ∈ Ico 2 (N + 2) := by
    apply hI
    rw [← hset]
    exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have hc := covered_of_witnesses I n hinj hset hw
  intro x hx
  by_cases hm : x.val ∈ PrefixMarkedWindowCount.marked (L + 1) N Y T
  · exact Or.inl ((mem_vertices N _ x).mpr hm)
  · have hunmarked : Unmarked (L + 1) Y T x.val := by
      by_contra hnot
      exact hm ((PrefixMarkedWindowCount.mem_marked _ _ _ _ _).mpr ⟨x.property, hnot⟩)
    have hxI := (mem_vertices N I x).mp hx
    have hxset : x.val ∈ tupleSet n := hset.symm ▸ hxI
    obtain ⟨a, _, ha⟩ := mem_image.mp hxset
    obtain hcert | ⟨j, hj⟩ := PrefixParticipatingWindowCertificates.coordinate_alternative
      n hn hinj hN Y T hY hc a (ha.symm ▸ hunmarked)
    · exact False.elim (hno hcert)
    · let y : Vertex N := ⟨n j, hn j⟩
      have hyI : y.val ∈ I := by rw [← hset]; exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
      refine Or.inr ⟨y, (mem_vertices N I y).mpr hyI, ?_⟩
      change PrefixSaturationPrimes.Edge (L + 1) N Y x.val (n j) ∨
        PrefixSaturationPrimes.Edge (L + 1) N Y (n j) x.val
      exact Or.inl (ha ▸ hj)

end PaperP1.PrefixWindowCertificateFamilies
