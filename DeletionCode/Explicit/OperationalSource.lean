import DeletionCode.Explicit.WitnessCore
import DeletionCode.Explicit.PeelingCompression

/-! All three compression branches cover the rejections of the concrete test. -/

namespace DeletionCode.Explicit.OperationalSource

open ConcreteSource Recognizer UniformParameters LetterSequence
open LetterGraphCuts RulePatch CompressorFrame

variable {q b t ℓ : ℕ}

structure Inputs (q b t : ℕ) where
  lookup : List Bool → (n : ℕ) → Option (Hash q b t n)
  strong : (n : ℕ) → (Fin n → Fin q) → Bool
  exceptional : (n : ℕ) → Hash q b t n → (Fin n → Fin q) → Bool
  rare : (n : ℕ) → Hash q b t n → Branch q

def procedures (hq : 1 < q) (pad : Fin q) (I : Inputs q b t) : Procedures q b t where
  lookup := I.lookup
  strong := I.strong
  exceptional := I.exceptional
  branch n H := ![I.rare n H,SmallCompression.branch hq pad (I.strong n) H,
    PeelingCompression.branch hq pad (I.strong n) H]

def coreWeightAt (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) : ℕ :=
  CoreWeight.weight (CoreWeight.coreReplayData ℓ q (edits t*witnessLimit q b t ℓ) (gram q b t ℓ)
    b t (coreLimit t) (windowLength q ℓ) (omittedLetters q b t ℓ) pad).object H x

/-- The public setup supplies the chosen hash and the rare-address law at
each stored length. The decoder and the two geometric codecs share it. -/
structure SetupLaws (pad : Fin q) (I : Inputs q b t) (bits : List Bool) (n : ℕ) : Prop where
  lookup : ∀ l, minLength q b t ≤ l → l ≤ n → ∃ H, I.lookup bits l = some H
  balanced : ∀ {l H}, I.lookup bits l = some H → PeelingFamilyBounds.Balanced pad H
  rare : ∀ {l H}, I.lookup bits l = some H → (I.rare l H).Laws pad
  rare_coverage : ∀ {x : QWord q} {H}, minLength q b t ≤ x.length →
    I.lookup bits x.length = some H →
    (¬ Strong x.get (windowLength q x.length) (omittedLetters q b t x.length) ∨
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t (windowLength q x.length) x.get ∨
      0 < coreWeightAt pad H x.get) →
    ∃ payload, (I.rare x.length H).encode x = some payload

private theorem strong_procs {hq : 1 < q} {pad : Fin q} {I : Inputs q b t}
    (d : DeciderLaws (procedures hq pad I) pad) :
    ∀ {l} (x : Fin l → Fin q),
      I.strong l x = true ↔ Strong x (windowLength q l) (omittedLetters q b t l) :=
  d.strong

private theorem fixed_encodes (x : QWord q)
    (enc : (Fin x.length → Fin q) → Option (QWord q))
    (dec : QWord q → Option (Fin x.length → Fin q)) {v : QWord q} (h : enc x.get = some v) :
    (fixedBranch enc dec).encode x = some v := by
  change (if h : x.length = x.length then enc (fun i => x.get (Fin.cast h.symm i)) else none) = _
  rw [dite_eq_left rfl]
  exact h

set_option maxHeartbeats 1500000 in
private theorem coverage (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (I : Inputs q b t) (d : DeciderLaws (procedures (by omega) pad I) pad)
    {bits : List Bool} {n : ℕ} (setup : SetupLaws pad I bits n) {x : QWord q} {H : Hash q b t x.length}
    (hstart : minLength q b t ≤ x.length) (hlookup : I.lookup bits x.length = some H)
    (hno : acceptedAt (procedures (by omega) pad I) pad H x.get = false) :
    ∃ j payload, ((procedures (by omega) pad I).branch x.length H j).encode x = some payload := by
  let ℓ := x.length
  let u := x.get
  let C := procedures (show 1 < q by omega) pad I
  have toRare (h : ¬ Strong u (windowLength q ℓ) (omittedLetters q b t ℓ) ∨
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t (windowLength q ℓ) u ∨
      0 < coreWeightAt pad H u) :
      ∃ j payload, (C.branch ℓ H j).encode x = some payload := by
    obtain ⟨v,hv⟩ := setup.rare_coverage hstart hlookup h
    exact ⟨0,v,hv⟩
  by_cases hs : I.strong ℓ u = true
  · have hx := (strong_procs d u).mp hs
    by_cases he : I.exceptional ℓ H u = true
    · exact toRare (Or.inr (Or.inl ((d.exceptional H u hstart).mp he)))
    · have he' : I.exceptional ℓ H u = false := Bool.eq_false_iff.mpr he
      have good : minLength q b t ≤ ℓ ∧ I.strong ℓ u = true := ⟨hstart,hs⟩
      have hB := basicBounds hq hb ht hstart
      have hℓ : 0 < ℓ := by have h := hB.record_length; omega
      have hw := recognizer_window hB
      obtain ⟨out,hout,hv,records⟩ := recognize_verified (recognizerBounds hB) H pad u hx hw hℓ
      have hk := recognize_kernel H pad u hout
      change runAt pad H u = some out at hout
      cases out with
      | complete hist =>
        have hs' : (procedures (by omega) pad I).strong x.length x.get = true := hs
        have he'' : (procedures (by omega) pad I).exceptional x.length H x.get = false := he'
        have hr : runAt pad H x.get = some (.complete hist) := hout
        unfold acceptedAt at hno
        rw [hs',he'',hr] at hno
        contradiction
      | firstEvent hist i =>
        let p := fullProgram hist i u
        by_cases hcore : core p.incidence = ∅
        · cases hsPack : SmallCompression.packWitness (show 1 < q by omega) pad u hist i with
          | some v =>
            refine ⟨1,v,?_⟩
            change (fixedBranch (SmallCompression.pack (by omega) pad (I.strong ℓ) H)
              (SmallCompression.read q b t ℓ pad)).encode x = some v
            apply fixed_encodes
            change SmallCompression.pack (by omega) pad (I.strong ℓ) H u = some v
            unfold SmallCompression.pack
            rw [ite_eq_left good,hout]
            exact hsPack
          | none =>
            have hlarge : ∀ e ∈ PeelingFrame.trace p, SmallCompression.isSmall (b := b) (t := t) pad (p.record e) = false :=
              fun e _ => PeelingCompression.noSmall_full hq hb ht pad H u hstart hx hv records hsPack e
            obtain ⟨v,hv,_,_⟩ := PeelingCompression.packWitness_complete hq hb ht pad H
              (setup.balanced hlookup) u hstart hℓ hx hv hk records hcore hlarge
            refine ⟨2,v,?_⟩
            change (fixedBranch (PeelingCompression.pack (by omega) pad (I.strong ℓ) H)
              (PeelingCompression.read pad H)).encode x = some v
            apply fixed_encodes
            change PeelingCompression.pack (by omega) pad (I.strong ℓ) H u = some v
            unfold PeelingCompression.pack
            rw [dite_eq_left hℓ,ite_eq_left good,hout]
            exact hv
        · have hnon : (core (componentIncidence (PatchTable.incidence (gates hist)) (.inl i))).Nonempty := by
            apply Finset.nonempty_iff_ne_empty.mpr
            have hh := congrArg Prod.snd (fullProgram_peel hist i u Finset.univ)
            intro h
            exact hcore (hh.trans h)
          exact toRare (Or.inr (Or.inr (firstEvent_core_weight_pos records hx (by omega) hℓ ht H i hv hk hnon)))
  · exact toRare (Or.inl (fun hw => hs ((strong_procs d u).mpr hw)))

theorem sourceGuarantees (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) (pad : Fin q)
    (I : Inputs q b t) (d : DeciderLaws (procedures (by omega) pad I) pad)
    {bits : List Bool} {n : ℕ} (setup : SetupLaws pad I bits n) :
    Machine.SourceGuarantees (callbacks (by omega) pad (procedures (by omega) pad I)) bits
      b t n (gramMultiplier t) (hashExponent q b t) (minLength q b t) := by
  apply ConcreteSource.sourceGuarantees hq hb ht pad _ d
  refine ⟨setup.lookup,?_,?_⟩
  · intro l H hh j
    have hs (x : Fin l → Fin q) (hx : I.strong l x = true) :
        Strong x (windowLength q l) (omittedLetters q b t l) := (strong_procs d x).mp hx
    fin_cases j
    · exact setup.rare hh
    · exact SmallCompression.branch_laws hq hb ht pad _ hs H
    · exact PeelingCompression.branch_laws hq hb ht pad _ hs H (setup.balanced hh)
  · intro x H hstart hlookup hno
    exact coverage hq hb ht pad I d setup hstart hlookup hno

#print axioms sourceGuarantees

end DeletionCode.Explicit.OperationalSource
