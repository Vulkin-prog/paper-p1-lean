module

public import PaperP1.Arithmetic.SmoothMotifCodes

/-! # Relabeling the three windows preserves actual motif products and small-prime codes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothMotifReindex

open Finset PaperP1.TransverseMotifs PaperP1.SmoothMotifCodes

def vertexMap {L : ℕ} (e : Equiv.Perm (Fin 3)) (v : Vertex L) : Vertex L := (e.symm v.1, v.2)

def reindex {L : ℕ} (e : Equiv.Perm (Fin 3)) (E : Finset (Vertex L)) : Finset (Vertex L) := E.image (vertexMap e)

theorem vertex_map_injective {L : ℕ} (e : Equiv.Perm (Fin 3)) : Function.Injective (vertexMap (L := L) e) := by
  intro u v hh
  have h0 : e.symm u.1 = e.symm v.1 := congrArg (fun w : Vertex L ↦ w.1) hh
  have h1 : u.2 = v.2 := by
    simpa only [vertexMap] using congrArg (fun w : Vertex L ↦ w.2) hh
  exact Prod.ext (e.symm.injective h0) h1

theorem reindex_card {L : ℕ} (e : Equiv.Perm (Fin 3)) (E : Finset (Vertex L)) :
    (reindex e E).card = E.card := card_image_of_injective _ (vertex_map_injective e)

theorem offsets_reindex {L : ℕ} (e : Equiv.Perm (Fin 3)) (E : Finset (Vertex L)) (i : Fin 3) :
    offsets (reindex e E) i = offsets E (e i) := by
  ext u
  rw [mem_offsets, mem_offsets]
  constructor
  · intro hu
    obtain ⟨v, hv, hpair⟩ := mem_image.mp hu
    have hv0 : v.1 = e i := by
      have hh := congrArg e (congrArg Prod.fst hpair)
      simpa only [vertexMap, e.apply_symm_apply] using hh
    have hv1 : v.2 = u := congrArg Prod.snd hpair
    have heq : v = (e i, u) := Prod.ext hv0 hv1
    rwa [heq] at hv
  · intro hu
    exact mem_image.mpr ⟨(e i, u), hu, by simp only [vertexMap, Equiv.symm_apply_apply]⟩

theorem transverse_reindex {L : ℕ} (e : Equiv.Perm (Fin 3)) {E : Finset (Vertex L)}
    (hE : Transverse E) : Transverse (reindex e E) := by
  intro i
  rw [offsets_reindex]
  exact hE (e i)

theorem pairwise_disjoint_reindex {ι : Type*} [DecidableEq ι] {L : ℕ} (I : Finset ι)
    (E : ι → Finset (Vertex L)) (hE : (↑I : Set ι).PairwiseDisjoint E) (e : Equiv.Perm (Fin 3)) :
    (↑I : Set ι).PairwiseDisjoint (fun i ↦ reindex e (E i)) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨a, ha, hav⟩ := mem_image.mp hvi
  obtain ⟨b, hb, hbv⟩ := mem_image.mp hvj
  have heq := vertex_map_injective e (hav.trans hbv.symm)
  exact disjoint_left.mp (hE hi hj hij) ha (by rw [heq]; exact hb)

theorem natural_product_reindex {L : ℕ} (e : Equiv.Perm (Fin 3)) (X : Fin 3 → ℕ)
    (E : Finset (Vertex L)) : naturalProduct (X ∘ e) (reindex e E) = naturalProduct X E := by
  rw [naturalProduct, reindex, prod_image (vertex_map_injective e).injOn]
  apply prod_congr rfl
  intro v _
  simp only [vertexMap, Function.comp_apply, Equiv.apply_symm_apply]

theorem code_reindex {L : ℕ} (e : Equiv.Perm (Fin 3)) (X : Fin 3 → ℕ) (E : Finset (Vertex L)) :
    code (X ∘ e) (reindex e E) = code X E := by rw [code, natural_product_reindex]; rfl

theorem square_outside_reindex {L H : ℕ} (e : Equiv.Perm (Fin 3)) (X : Fin 3 → ℕ)
    (E : Finset (Vertex L)) : SquareOutside H (X ∘ e) (reindex e E) ↔ SquareOutside H X E := by
  simp only [SquareOutside, code_reindex]

theorem centres_injective {α : Type*} (e : Equiv.Perm (Fin 3)) :
    Function.Injective (fun X : Fin 3 → α ↦ X ∘ e) := by
  intro X Y hh
  funext i
  have heq := congrFun hh (e.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using heq

end PaperP1.SmoothMotifReindex
