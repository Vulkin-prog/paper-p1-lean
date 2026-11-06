module

public import PaperP1.Analysis.ValuationDamping
public import PaperP1.Arithmetic.PrimeProductFibres
public import PaperP1.Analysis.PrimePowerPolynomial

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeProductDegree
open Finset PaperP1 BoundedProductFibres
open scoped Classical

def supported (P : Finset ℕ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P

theorem multiplicity_prod {ι : Type*} (P : Finset ℕ) (I : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ I, a i ≠ 0) :
    ValuationDamping.multiplicity P (∏ i ∈ I, a i)=∑ i ∈ I, ValuationDamping.multiplicity P (a i) := by
  revert ha
  induction I using Finset.induction_on with
  | empty => intro ha; simp [ValuationDamping.multiplicity_one]
  | @insert j I hj ih =>
    intro ha
    rw [prod_insert hj,sum_insert hj,ValuationDamping.multiplicity_mul P _ _ (ha j (mem_insert_self j I))
      (prod_ne_zero_iff.mpr (fun i hi ↦ ha i (mem_insert_of_mem hi))),ih (fun i hi ↦ ha i (mem_insert_of_mem hi))]

theorem supported_of_layer (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (hn : n ∈ PrimePowerPolynomial.layer k P) : supported P n := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
  intro p hp hpn
  change p ∣ ∏ i, x i at hpn
  obtain ⟨i,_hi,hpi⟩ := hp.prime.exists_mem_finset_dvd hpn
  have hxi : x i ∈ P := Fintype.mem_piFinset.mp hx i
  have he : p=x i := (Nat.prime_dvd_prime_iff_eq hp (hP _ hxi)).mp hpi
  exact he.symm ▸ hxi

theorem degree_of_layer (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (hn : n ∈ PrimePowerPolynomial.layer k P) : ValuationDamping.multiplicity P n=k := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
  rw [value,multiplicity_prod P univ x (fun i _hi ↦ (hP _ (Fintype.mem_piFinset.mp hx i)).pos.ne')]
  have he : (∑ i, ValuationDamping.multiplicity P (x i))=∑ _i : Fin k, (1 : ℕ) := by
    apply sum_congr rfl
    intro i hi
    rw [ValuationDamping.multiplicity_prime P _ (hP _ (Fintype.mem_piFinset.mp hx i)),
      ite_eq_left (Fintype.mem_piFinset.mp hx i)]
  rw [he]
  simp

theorem layer_of_supported (P : Finset ℕ) (n : ℕ) (hn : 0 < n) (hs : supported P n) :
    n ∈ PrimePowerPolynomial.layer (ValuationDamping.multiplicity P n) P := by
  revert hn hs
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hs
    by_cases hn1 : n=1
    · subst n
      rw [ValuationDamping.multiplicity_one]
      refine mem_image.mpr ⟨(fun i : Fin 0 ↦ Fin.elim0 i),?_,?_⟩
      · exact Fintype.mem_piFinset.mpr (fun i ↦ Fin.elim0 i)
      · simp [value]
    · obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hpP := hs p hp hpn
      have hm : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hmn : n/p < n := Nat.div_lt_self hn hp.one_lt
      have hsm : supported P (n/p) := by
        intro q hq hqm
        exact hs q hq (dvd_trans hqm (Nat.div_dvd_of_dvd hpn))
      obtain ⟨x,hx,hprod⟩ := mem_image.mp (ih (n/p) hmn hm hsm)
      have hmul : p*(n/p)=n := Nat.mul_div_cancel' hpn
      have hdeg := ValuationDamping.multiplicity_mul P p (n/p) hp.pos.ne' hm.ne'
      rw [hmul,ValuationDamping.multiplicity_prime P p hp,ite_eq_left hpP] at hdeg
      have hd : ValuationDamping.multiplicity P n=ValuationDamping.multiplicity P (n/p)+1 := by omega
      rw [hd]
      refine mem_image.mpr ⟨Fin.cons p x,?_,?_⟩
      · apply Fintype.mem_piFinset.mpr
        intro i
        exact Fin.cases hpP (fun j ↦ Fintype.mem_piFinset.mp hx j) i
      · change (∏ i : Fin (ValuationDamping.multiplicity P (n/p)+1), Fin.cons p x i)=n
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ]
        change p*value x=n
        rw [hprod]
        exact hmul

theorem layer_iff (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    n ∈ PrimePowerPolynomial.layer k P ↔
      0 < n ∧ supported P n ∧ ValuationDamping.multiplicity P n=k := by
  constructor
  · intro hn
    exact ⟨PrimePowerPolynomial.layer_positive k P (fun p hp ↦ (hP p hp).pos) n hn,
      supported_of_layer k P hP n hn,degree_of_layer k P hP n hn⟩
  · rintro ⟨hn,hs,hk⟩
    simpa only [hk] using layer_of_supported P n hn hs
end PaperP1.PrimeProductDegree
