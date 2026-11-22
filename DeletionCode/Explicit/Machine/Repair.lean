import DeletionCode.Explicit.Machine.WordEnumeration
import DeletionCode.Explicit.Repair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Uniform repair on a word and its public source data. The length guards
bound the machine on every input, including arbitrary source bits. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped Function

abbrev SourceInput (q : ℕ) := List Bool × QWord q

theorem wordLength_polyTime (q : ℕ) :
    ComputableInPolyTime (List.length (α := Fin q)) (wordEncoding q) encUnary := by
  unfold wordEncoding
  exact length_list _

/-- Joint interpreters for the unfinished source-data construction. -/
structure SourceCallbacks (q : ℕ) where
  accepted : SourceInput q → Bool
  compress : SourceInput q → QWord q
  expand : SourceInput q → Option (QWord q)
  label : SourceInput q → ℕ

namespace SourceCallbacks

variable {q : ℕ} (F : SourceCallbacks q)

structure Certified : Prop where
  accepted : ComputableInPolyTime F.accepted (inputEncoding q) encBool
  compress : ComputableInPolyTime F.compress (inputEncoding q) (wordEncoding q)
  expand : ComputableInPolyTime F.expand (inputEncoding q) (encOption (wordEncoding q))
  label : ComputableInPolyTime F.label (inputEncoding q) encNat

/-- Exactly the laws of the existing repair data at a given public source. -/
structure RepairLaws (bits : List Bool) : Prop where
  accepted_nil : F.accepted (bits, []) = true
  shortens : ∀ x, F.accepted (bits, x) = false → (F.compress (bits, x)).length + 1 = x.length
  expand_compress : ∀ x, F.accepted (bits, x) = false → F.expand (bits, F.compress (bits, x)) = some x
  expand_length : ∀ y x, F.expand (bits, y) = some x → x.length = y.length + 1

def repairData (bits : List Bool) (h : F.RepairLaws bits) : RepairData (Fin q) where
  accepted x := F.accepted (bits, x)
  compress x := F.compress (bits, x)
  expand y := F.expand (bits, y)
  accepted_nil := h.accepted_nil
  shortens := h.shortens
  expand_compress := h.expand_compress
  expand_length := h.expand_length

private def repairStep (bits : List Bool) (x : QWord q) : QWord q :=
  if F.accepted (bits, x) then x
  else
    let y := F.compress (bits, x)
    if y.length < x.length then y else x

def repair (p : SourceInput q) : QWord q :=
  (F.repairStep p.1)^[p.2.length] p.2

private theorem repairStep_polyTime (H : F.Certified) :
    ComputableInPolyTime (fun p : SourceInput q => F.repairStep p.1 p.2)
      (inputEncoding q) (wordEncoding q) := by
  have hx := snd encBits (wordEncoding q)
  have hy := H.compress
  have htest := unary_lt' ((wordLength_polyTime q).comp hy) ((wordLength_polyTime q).comp hx)
  exact H.accepted.ite hx (ite_decide htest hy hx)

theorem repair_polyTime (H : F.Certified) :
    ComputableInPolyTime F.repair (inputEncoding q) (wordEncoding q) := by
  have hword := snd encBits (wordEncoding q)
  have hfuel := (wordLength_polyTime q).comp hword
  have hsize : PolyBounded (fun p : SourceInput q => (inputEncoding q p).length)
      (fun p => (2 * q + 1) * p.2.length) := by
    unfold inputEncoding
    apply (PolyBounded.const (2 * q + 1)).mul
    simpa only [Function.comp_def, encUnary_apply, List.length_replicate] using hfuel.polyBounded_length
  exact (iterateWith_spec (fst encBits (wordEncoding q)) hfuel hword (F.repairStep_polyTime H)
    (fun p _ x => x.length ≤ p.2.length) (fun _ => le_rfl)
    (fun p i x _ hx => by
      unfold repairStep
      split
      · exact hx
      · dsimp only
        split <;> omega)
    hsize (fun p i x _ hx =>
      (encoded_word_length_le x).trans (Nat.mul_le_mul_left _ hx))).1

private theorem repairAux_eq_iterate {bits : List Bool} (h : F.RepairLaws bits)
    (fuel : ℕ) (x : QWord q) :
    (F.repairStep bits)^[fuel] x = (F.repairData bits h).repairAux fuel x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    cases ha : F.accepted (bits, x) with
    | true =>
      rw [show F.repairStep bits x = x by simp [repairStep, ha], ih]
      cases fuel <;> simp [RepairData.repairAux, repairData, ha]
    | false =>
      have hl := h.shortens x ha
      simp only [repairStep, ha, Bool.false_eq_true, ite_false]
      have hlt : (F.compress (bits, x)).length < x.length := by omega
      simp only [hlt, ite_true, ih]
      simp [RepairData.repairAux, repairData, ha]

theorem repair_eq {bits : List Bool} (h : F.RepairLaws bits) (x : QWord q) :
    F.repair (bits, x) = (F.repairData bits h).repair x :=
  F.repairAux_eq_iterate h _ _

private def checkedExpand (p : SourceInput q) : Option (QWord q) :=
  (F.expand p).elim none (fun x => if x.length = p.2.length + 1 then some x else none)

private def undoStep (bits : List Bool) (y : Option (QWord q)) : Option (QWord q) :=
  y.elim none (fun x => F.checkedExpand (bits, x))

def inverse (p : SourceInput q × ℕ) : Option (QWord q) :=
  if p.1.2.length ≤ p.2 then (F.undoStep p.1.1)^[p.2 - p.1.2.length] (some p.1.2)
  else none

private theorem checkedExpand_polyTime (H : F.Certified) :
    ComputableInPolyTime F.checkedExpand (inputEncoding q) (encOption (wordEncoding q)) := by
  apply optionElimWithInput H.expand (const none)
    (body := fun p x => if x.length = p.2.length + 1 then some x else none)
  have hx := snd (inputEncoding q) (wordEncoding q)
  have hy := (snd encBits (wordEncoding q)).comp (fst (inputEncoding q) (wordEncoding q))
  have hxLen := (wordLength_polyTime q).comp hx
  have hyLen := unary_add' ((wordLength_polyTime q).comp hy) (const 1)
  exact ite_decide (hxLen.decide_eq' hyLen) ((optionSome _).comp hx) (const none)

private theorem undoStep_polyTime (H : F.Certified) :
    ComputableInPolyTime (fun p : List Bool × Option (QWord q) => F.undoStep p.1 p.2)
      (encPair encBits (encOption (wordEncoding q))) (encOption (wordEncoding q)) := by
  apply optionElimWithInput (snd encBits (encOption (wordEncoding q))) (const none)
    (body := fun p x => F.checkedExpand (p.1, x))
  exact (F.checkedExpand_polyTime H).comp ((fst (encPair encBits (encOption (wordEncoding q))) (wordEncoding q)).fst'.prod
    (snd _ _))

private theorem undoStep_length {bits : List Bool} {y : Option (QWord q)} {x : QWord q}
    (h : F.undoStep bits y = some x) : ∃ w, y = some w ∧ x.length = w.length + 1 := by
  cases y with
  | none => simp [undoStep] at h
  | some w =>
    refine ⟨w, rfl, ?_⟩
    unfold undoStep checkedExpand at h
    cases he : F.expand (bits, w) with
    | none => simp [he] at h
    | some z =>
      by_cases hl : z.length = w.length + 1
      · have hxz : x = z := by simpa [he, hl] using h.symm
        simpa only [hxz] using hl
      · simp [he, hl] at h

theorem inverse_polyTime (H : F.Certified) :
    ComputableInPolyTime F.inverse (encPair (inputEncoding q) encUnary)
      (encOption (wordEncoding q)) := by
  let ip := encPair (inputEncoding q) encUnary
  have hk := snd (inputEncoding q) encUnary
  have hx := (snd encBits (wordEncoding q)).comp (fst (inputEncoding q) encUnary)
  have hbits := (fst encBits (wordEncoding q)).comp (fst (inputEncoding q) encUnary)
  have hlen := (wordLength_polyTime q).comp hx
  have hfuel := unary_sub' hk hlen
  have hsize : PolyBounded (fun p : SourceInput q × ℕ => (ip p).length)
      (fun p => (2 * q + 1) * (p.1.2.length + p.2) + 1) := by
    have hsum := (unary_add' hlen hk).polyBounded_length
    have hsum' : PolyBounded (fun p : SourceInput q × ℕ => (ip p).length)
        (fun p => p.1.2.length + p.2) := by simpa only [Function.comp_def, encUnary_apply, List.length_replicate] using hsum
    exact ((PolyBounded.const (2 * q + 1)).mul hsum').add (PolyBounded.const 1)
  have hloop := (iterateWith_spec hbits hfuel ((optionSome _).comp hx) (F.undoStep_polyTime H)
    (fun p i y => ∀ x, y = some x → x.length ≤ p.1.2.length + i)
    (fun _ x h => by cases h; simp)
    (fun p i y _ hy x h => by
      obtain ⟨w, hw, hl⟩ := F.undoStep_length h
      have := hy w hw
      omega)
    hsize (fun p i y hi hy => by
      cases y with
      | none => simp [encOption]
      | some x =>
        have hx' := hy x rfl
        have hi' : i ≤ p.2 := hi.trans (Nat.sub_le ..)
        have hlen' := (encoded_word_length_le x).trans
          (Nat.mul_le_mul_left (2 * q + 1) (show x.length ≤ p.1.2.length + p.2 by omega))
        simpa [encOption, Nat.add_comm] using Nat.add_le_add_right hlen' 1)).1
  exact ite_decide (unary_le' hlen hk) hloop (const none)

private theorem checkedExpand_eq {bits : List Bool} (h : F.RepairLaws bits) (x : QWord q) :
    F.checkedExpand (bits, x) = F.expand (bits, x) := by
  cases he : F.expand (bits, x) with
  | none => simp [checkedExpand, he]
  | some y => simp [checkedExpand, he, h.expand_length x y he]

private theorem undo_eq_iterate {bits : List Bool} (h : F.RepairLaws bits)
    (fuel : ℕ) (x : QWord q) :
    (F.undoStep bits)^[fuel] (some x) = (F.repairData bits h).undo fuel x := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply', ih]
    cases he : (F.repairData bits h).undo fuel x with
    | none => simp [RepairData.undo, he, undoStep]
    | some y =>
      rw [RepairData.undo, he]
      exact F.checkedExpand_eq h y

theorem inverse_eq {bits : List Bool} (h : F.RepairLaws bits) (x : QWord q) (k : ℕ) :
    F.inverse ((bits, x), k) = (F.repairData bits h).inverse k x := by
  simp only [inverse, RepairData.inverse, F.undo_eq_iterate h]

#print axioms repair_polyTime
#print axioms inverse_polyTime
#print axioms repair_eq
#print axioms inverse_eq

end SourceCallbacks
end DeletionCode.Explicit.Machine
