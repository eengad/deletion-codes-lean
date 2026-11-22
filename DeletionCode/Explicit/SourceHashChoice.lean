import DeletionCode.Explicit.PeelingFamilyBounds
import DeletionCode.Explicit.MatrixConditionalChooser
import DeletionCode.Explicit.ParameterMassBounds
import DeletionCode.Explicit.ExceptionalCatalogue
import DeletionCode.Explicit.CoreReplayCheck

/-! The source hash is chosen from the concrete family and weight catalogues. -/

namespace DeletionCode.Explicit.SourceHashChoice

open ConcreteSource UniformParameters FieldHash BucketBalance ConditionalChooser
open CoreWeight PeelingFamilyBounds
open scoped BigOperators

variable {q b t ℓ : ℕ}

def coreData (q b t ℓ : ℕ) (pad : Fin q) :=
  coreReplayData ℓ q (edits t*witnessLimit q b t ℓ) (gram q b t ℓ) b t
    (coreLimit t) (windowLength q ℓ) (omittedLetters q b t ℓ) pad

def exceptionEntries (q b t ℓ : ℕ) (pad : Fin q) :=
  ExceptionalWeight.family pad (finFunctionFinEquiv.symm :
    Fin (q^gram q b t ℓ) ≃ (Fin (gram q b t ℓ) → Fin q)) b t ℓ

def exceptionData (q b t ℓ : ℕ) (pad : Fin q) :=
  fun i => (exceptionEntries q b t ℓ pad i).object

def evaluators (q b t ℓ : ℕ) (pad : Fin q) : Evaluator :=
  fun i p =>
    let h := prefixHash (hashWidth q b t ℓ) (q^gram q b t ℓ) p
    ![conditionalPotential (vectors q b t ℓ pad) h,
      conditionalMass (exceptionData q b t ℓ pad) h,
      conditionalMass (coreData q b t ℓ pad).object h] i

def choose (q b t ℓ : ℕ) (pad : Fin q) : Hash q b t ℓ :=
  let E := evaluators q b t ℓ pad
  chooseHash (hashWidth q b t ℓ) (q^gram q b t ℓ) E
    (catalogueBounds (SmallCompression.familyCount q b t ℓ pad) E)

private theorem vectorTable_nonempty (pad : Fin q) (i : Fin (SmallCompression.familyCount q b t ℓ pad)) :
    (vectors q b t ℓ pad i).Nonempty := by
  let fs := tables q b t ℓ pad
  have hi : fs.get i ∈ fs := List.get_mem .. 
  change fs.get i ∈ BubbleFamilies.families q (windowLength q ℓ) b (gram q b t ℓ) (omittedLetters q b t ℓ) pad at hi
  unfold BubbleFamilies.families at hi
  obtain ⟨shape,_,hb⟩ := List.mem_filterMap.mp hi
  dsimp only at hb
  split at hb
  next h =>
    have hh := congrArg Prod.snd (Option.some.inj hb)
    change (fs.get i).2.Nonempty
    rw [← hh]
    exact h
  next => contradiction

theorem choose_bounds (pad : Fin q) :
    let H := choose q b t ℓ pad
    Balanced pad H ∧
      rootMass (exceptionData q b t ℓ pad) H ≤
        3*completionMean (freeHash (hashWidth q b t ℓ) (q^gram q b t ℓ))
          (rootMass (exceptionData q b t ℓ pad)) ∧
      rootMass (coreData q b t ℓ pad).object H ≤
        3*completionMean (freeHash (hashWidth q b t ℓ) (q^gram q b t ℓ))
          (rootMass (coreData q b t ℓ pad).object) :=
  chooseHash_three_bounds _ (vectorTable_nonempty pad) (exceptionData q b t ℓ pad)
    (coreData q b t ℓ pad).object (evaluators q b t ℓ pad) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem sum_core_indices (ℓ t r₀ : ℕ) (P : ℚ) :
    (∑ i : Fin r₀, (ℓ : ℚ)^(t*(i.val+1))/P^(i.val+1)) =
      ∑ r ∈ Finset.Icc 1 r₀, ((ℓ : ℚ)^t/P)^r := by
  apply Finset.sum_bij (fun i _ => i.val+1)
  · intro i _
    exact Finset.mem_Icc.mpr ⟨by omega,i.isLt⟩
  · intro i _ j _ h
    exact Fin.ext (by omega)
  · intro n hn
    obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp hn
    exact ⟨⟨n-1,by omega⟩,Finset.mem_univ _,by simp; omega⟩
  · intro i _
    rw [div_pow,← pow_mul]

set_option maxHeartbeats 1500000 in
/-- The chosen hash satisfies the three integer rare-address root mass bounds. -/
theorem root_counts (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (hstart : minLength q b t ≤ ℓ) :
    let H := choose q b t ℓ pad
    (∑ x : Fin ℓ → Fin q, MatchingWeight.weight x (windowLength q ℓ) (omittedLetters q b t ℓ)) ≤ q^(ℓ-8) ∧
      (∑ x : Fin ℓ → Fin q, weight (exceptionData q b t ℓ pad) H x) ≤ q^(ℓ-8) ∧
      (∑ x : Fin ℓ → Fin q, weight (coreData q b t ℓ pad).object H x) ≤ q^(ℓ-8) := by
  dsimp only
  let H := choose q b t ℓ pad
  let X := exceptionData q b t ℓ pad
  let C := (coreData q b t ℓ pad).object
  let θ := hashWidth q b t ℓ
  let L := gram q b t ℓ
  have hq' : 0 < q := by omega
  have hk : 0 < windowLength q ℓ := by unfold windowLength; omega
  have hB := basicBounds hq hb ht hstart
  have hL : 1 ≤ L := by have h := hB.gram_large; omega
  have hlen : 2*t*b+1 ≤ ℓ := hB.record_length
  have hbnds := choose_bounds (q := q) (b := b) (t := t) (ℓ := ℓ) pad
  have hm := MatchingWeight.weight_root_bound (ℓ := ℓ) (Λ := omittedLetters q b t ℓ) hk hq'
  have he := ExceptionalWeight.catalogue_uniform_mean (θ := θ) (L := L) pad finFunctionFinEquiv.symm hq hL hlen
  have he' : rootMass X H ≤
      3 * exceptionalConstant b t * (q : ℚ)^(b*edits t) * L *
        (ℓ : ℚ)^(edits t-1) / (hashCount q b t ℓ : ℚ) := by
    have hx := hbnds.2.1.trans (mul_le_mul_of_nonneg_left he (by decide : (0 : ℚ) ≤ 3))
    simpa only [exceptionalConstant,ExceptionalWeight.recordConstant,edits,hashCount,Nat.cast_pow,Nat.cast_ofNat,
      mul_div_assoc, mul_assoc, Nat.cast_mul] using hx
  have hc := (coreData q b t ℓ pad).mean_bound (θ := θ) hq'
  have hc' : rootMass C H ≤ 3 * (gamma q b t ℓ : ℚ) *
      (∑ r ∈ Finset.Icc 1 (coreLimit t), ((ℓ : ℚ)^t / (hashCount q b t ℓ : ℚ))^r) := by
    have hr := hbnds.2.2.trans (mul_le_mul_of_nonneg_left hc (by decide : (0 : ℚ) ≤ 3))
    change rootMass C H ≤ 3*((gamma q b t ℓ : ℚ)*
      ∑ r : Fin (coreLimit t), (ℓ : ℚ)^(t*(r.val+1))/((3 : ℚ)^θ)^(r.val+1)) at hr
    rw [sum_core_indices] at hr
    simpa only [hashCount,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hr
  rw [rootMass_eq_word_average hq' X H] at he'
  rw [rootMass_eq_word_average hq' C H] at hc'
  apply root_masses_bound hq hb ht hstart
  · simpa only [matchBound,Nat.cast_pow,Nat.cast_sum] using hm
  · simpa only [Nat.cast_sum] using he'
  · simpa only [Nat.cast_sum] using hc'

#print axioms choose_bounds
#print axioms root_counts

end DeletionCode.Explicit.SourceHashChoice
