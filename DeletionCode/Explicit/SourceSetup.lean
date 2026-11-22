import DeletionCode.Explicit.OperationalSource
import DeletionCode.Explicit.SourceHashChoice
import DeletionCode.Explicit.SourceHashTable
import DeletionCode.Explicit.RareAddress
import DeletionCode.Explicit.Machine.AlignedSourceHash

/-! The length-indexed setup and the concrete Stage 1 source guarantees. -/

namespace DeletionCode.Explicit.SourceSetup

open ConcreteSource UniformParameters FieldHash WeightedAddress
open SourceHashChoice OperationalSource PeelingFamilyBounds
open scoped BigOperators

variable {q b t ℓ : ℕ}

def indexedWeight (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) : ℕ :=
  MatchingWeight.weight x (windowLength q ℓ) (omittedLetters q b t ℓ) +
    CoreWeight.weight (exceptionData q b t ℓ pad) H x + coreWeightAt pad H x

def prefixMass (pad : Fin q) (H : Hash q b t ℓ) (p : QWord q) : ℕ :=
  Machine.MatchingPrefixes.mass pad b t (ℓ,p) +
    CoreWeight.prefixMass (exceptionData q b t ℓ pad) H p.get +
    CoreWeight.prefixMass (coreData q b t ℓ pad).object H p.get

theorem exact_mass (pad : Fin q) (H : Hash q b t ℓ) :
    Exact (RareAddress.liftWeight (indexedWeight pad H)) (prefixMass pad H) ℓ := by
  apply RareAddress.exact_of_prefix_sum
  intro k hk u
  unfold prefixMass
  rw [Machine.MatchingPrefixes.mass_eq]
  have he := eval_ofFn
    (fun _ u => CoreWeight.prefixMass (exceptionData q b t ℓ pad) H u) u
  have hc := eval_ofFn
    (fun _ u => CoreWeight.prefixMass (coreData q b t ℓ pad).object H u) u
  rw [he,hc,MatchingWeight.prefixMass_eq_sum hk,CoreWeight.prefixMass_eq_sum hk,CoreWeight.prefixMass_eq_sum hk]
  simp only [indexedWeight,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split
  · simp_all [coreWeightAt,coreData]
    rfl
  · simp_all [coreData]

private def wordWeights (pad : Fin q) (H : Hash q b t ℓ) (n : ℕ) : Mass q :=
  if n = ℓ then RareAddress.liftWeight (indexedWeight pad H) else fun _ => 0

private def wordMasses (pad : Fin q) (H : Hash q b t ℓ) (n : ℕ) : Mass q :=
  if n = ℓ then prefixMass pad H else fun _ => 0

private theorem wordMasses_exact (pad : Fin q) (H : Hash q b t ℓ) (n : ℕ) :
    Exact (wordWeights pad H n) (wordMasses pad H n) n := by
  by_cases h : n = ℓ
  · subst n
    simpa [wordWeights,wordMasses] using exact_mass pad H
  · simp only [wordWeights,wordMasses,h,ite_false]
    intro p k hk
    simp [extensionMass]

def rareBranch (pad : Fin q) (H : Hash q b t ℓ) : CompressorFrame.Branch q :=
  RareAddress.branch pad (minLength q b t) (wordMasses pad H)

theorem rareBranch_laws (hq : 2 ≤ q) (pad : Fin q) (H : Hash q b t ℓ) :
    (rareBranch pad H).Laws pad :=
  RareAddress.branch_laws pad hq _ (wordWeights pad H) (wordMasses pad H) (fun n _ => wordMasses_exact pad H n)

theorem rootMass_bound (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (hstart : minLength q b t ≤ ℓ) :
    prefixMass pad (choose q b t ℓ pad) [] ≤ q^(ℓ-6) := by
  let H := choose q b t ℓ pad
  have hbasic := basicBounds hq hb ht hstart
  have hℓ : 8 ≤ ℓ := (by decide : 8 ≤ 400).trans (hbasic.gram_large.trans hbasic.borrowed_length)
  have E := (exact_mass pad H) [] ℓ (by simp)
  simp only [extensionMass,List.nil_append,MatchingEnumeration.sum_words,RareAddress.liftWeight_ofFn] at E
  change prefixMass pad H [] ≤ _
  rw [E]
  have Hsum : (∑ x : Fin ℓ → Fin q, indexedWeight pad H x) =
    (∑ x : Fin ℓ → Fin q, MatchingWeight.weight x (windowLength q ℓ) (omittedLetters q b t ℓ)) +
    (∑ x : Fin ℓ → Fin q, CoreWeight.weight (exceptionData q b t ℓ pad) H x) +
    (∑ x : Fin ℓ → Fin q, CoreWeight.weight (coreData q b t ℓ pad).object H x) := by
    simp only [indexedWeight,Finset.sum_add_distrib]
    rfl
  rw [Hsum]
  obtain ⟨hm,he,hc⟩ := root_counts hq hb ht pad hstart
  change (∑ x : Fin ℓ → Fin q, CoreWeight.weight (exceptionData q b t ℓ pad) H x) ≤ _ at he
  change (∑ x : Fin ℓ → Fin q, CoreWeight.weight (coreData q b t ℓ pad).object H x) ≤ _ at hc
  have hcap : 3*q^(ℓ-8) ≤ q^(ℓ-6) := by
    rw [show ℓ-6 = (ℓ-8)+2 by omega,pow_add,mul_comm]
    exact Nat.mul_le_mul_left _ ((by decide : 3 ≤ 2^2).trans (Nat.pow_le_pow_left hq 2))
  exact (show _ ≤ 3*q^(ℓ-8) by omega).trans hcap

private theorem rareBranch_coverage (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (x : QWord q) (hstart : minLength q b t ≤ x.length)
    (h : ¬ LetterSequence.Strong x.get (windowLength q x.length) (omittedLetters q b t x.length) ∨
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm (choose q b t x.length pad)
        b t (windowLength q x.length) x.get ∨
      0 < coreWeightAt pad (choose q b t x.length pad) x.get) :
    ∃ p, (rareBranch pad (choose q b t x.length pad)).encode x = some p := by
  let l := x.length
  let H := choose q b t l pad
  have hB : BasicBounds q b t l := basicBounds hq hb ht hstart
  have h8 : 8 ≤ l := (by decide : 8 ≤ 400).trans (hB.gram_large.trans hB.borrowed_length)
  have hx : 0 < indexedWeight pad H x.get := by
    unfold indexedWeight
    rcases h with hn | he | hc
    · have h₁ : 0 < MatchingWeight.weight x.get (windowLength q l) (omittedLetters q b t l) :=
        (MatchingWeight.weight_pos_iff_not_strong x.get).mpr hn
      omega
    · have hK : windowLength q l < gram q b t l := by have hh := hB.borrowed_gram; omega
      have h₂ : 0 < CoreWeight.weight (exceptionData q b t l pad) H x.get :=
        ExceptionalWeight.catalogue_weight_pos pad finFunctionFinEquiv.symm hB.borrowed_length hK H he
      omega
    · have hc' : 0 < coreWeightAt pad H x.get := hc
      omega
  have hw : 0 < wordWeights pad H l x := by
    unfold wordWeights
    rw [ite_eq_left rfl]
    unfold RareAddress.liftWeight
    have he : x.length = l := rfl
    rw [dite_eq_left he]
    exact hx
  have hr : wordMasses pad H l [] ≤ q^(l-6) := by
    unfold wordMasses
    rw [ite_eq_left (show l = l from rfl)]
    exact rootMass_bound hq hb ht pad hstart
  have he := RareAddress.branch_encodes pad _ (wordWeights pad H) (wordMasses pad H)
    (max_le h8 hstart) (wordMasses_exact pad H l) hr hw
  exact ⟨_,he⟩

def sourceBits (q b t : ℕ) (pad : Fin q) (n : ℕ) : List Bool :=
  SourceHashTable.write q b t n (fun l => choose q b t l pad)

def inputs (q b t : ℕ) (pad : Fin q) : Inputs q b t where
  lookup := SourceHashTable.lookup q b t
  strong l x := AcceptanceWeights.strong pad b t l (List.ofFn x)
  exceptional l H x := Machine.AlignedSourceHash.exceptionalMain pad b t
    (l,Machine.CataloguePrefix.matrixRows H,List.ofFn x)
  rare _ H := rareBranch pad H

def sourceCallbacks (hq : 1 < q) (b t : ℕ) (pad : Fin q) : Machine.SourceCallbacks q :=
  callbacks hq pad (procedures hq pad (inputs q b t pad))

private theorem input_deciders (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (pad : Fin q) :
    DeciderLaws (procedures (by omega) pad (inputs q b t pad)) pad := by
  constructor
  · intro l x
    exact AcceptanceWeights.strong_iff pad b t x
  · intro l H x hl
    exact Machine.AlignedSourceHash.exceptionalMain_iff pad b t x hq hb ht hl H

private theorem lookup_hash_known (pad : Fin q) (n l : ℕ) {H : Hash q b t l}
    (h : (inputs q b t pad).lookup (sourceBits q b t pad n) l = some H) :
    H = choose q b t l pad := by
  change SourceHashTable.lookup q b t (SourceHashTable.write q b t n (fun k => choose q b t k pad)) l = some H at h
  by_cases hlen : minLength q b t ≤ l ∧ l ≤ n
  · rw [SourceHashTable.lookup_write (fun k => choose q b t k pad) hlen.1 hlen.2] at h
    exact (Option.some.inj h).symm
  · have hout : l < minLength q b t ∨ n < l := by omega
    rw [SourceHashTable.lookup_write_none (fun k => choose q b t k pad) hout] at h
    contradiction

theorem setup_laws (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (pad : Fin q) (n : ℕ) :
    SetupLaws pad (inputs q b t pad) (sourceBits q b t pad n) n := by
  constructor
  · intro l hlo hhi
    exact ⟨choose q b t l pad,SourceHashTable.lookup_write _ hlo hhi⟩
  · intro l H h
    rw [lookup_hash_known pad n l h]
    exact (choose_bounds pad).1
  · intro l H h
    exact rareBranch_laws hq pad H
  · intro x H hstart hlookup h
    have he := lookup_hash_known pad n x.length hlookup
    subst H
    exact rareBranch_coverage hq hb ht pad x hstart h

/-- Stage 1 of the explicit source, including the public setup, label,
acceptance test, and all three compression branches. -/
theorem sourceGuarantees (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (pad : Fin q) (n : ℕ) :
    Machine.SourceGuarantees (sourceCallbacks (by omega) b t pad) (sourceBits q b t pad n)
      b t n (gramMultiplier t) (hashExponent q b t) (minLength q b t) :=
  OperationalSource.sourceGuarantees hq hb ht pad _ (input_deciders hq hb ht pad) (setup_laws hq hb ht pad n)

#print axioms sourceGuarantees

end DeletionCode.Explicit.SourceSetup
