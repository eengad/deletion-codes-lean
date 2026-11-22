import DeletionCode.Explicit.Machine.AlignedSourceHash
import DeletionCode.Explicit.Machine.SourceLists
import DeletionCode.Explicit.SourceHashChoice

/-! The exceptional record catalogue in the source hash's gram order. -/
namespace DeletionCode.Explicit.Machine.SourceExceptionalTable

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary FieldHash GramOrder CataloguePrefix SourceLists
open ExceptionalWeight
open Qary.SignedSupport (Gram)
open _root_.DeletionCode.Explicit.UniformParameters

variable {q l L b t : ℕ}

private theorem mainDelta (pad : Fin q) (w z : QWord q) :
    delta pad (finFunctionFinEquiv.symm : Fin (q^L) ≃ Gram (Fin q) L) w z =
      delta pad (dictionary q L) w z ∘ (columns q L).symm := by
  funext i
  simp [delta, ExceptionalWeight.spectrum, Function.comp_def, columns]

private theorem permuted_nonzero {α β : Type} (e : α ≃ β) (v : α → F₃) : v ∘ e.symm ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    exact h (by simp [hv])
  · intro h hv
    apply h
    funext i
    have he := congrFun hv (e i)
    simpa [Function.comp_def] using he

private def moveEntry (e : Entry l q (q^L)) : Entry l q (q^L) :=
  ⟨e.assignment, e.changeVector ∘ (columns q L).symm,
    (permuted_nonzero (columns q L) e.changeVector).mpr e.nonzero⟩

private theorem entry_main (pad : Fin q) (edits : List (Burst.Edit (Fin q))) (S : Finset (Fin l)) (a : QWord q) :
    entry? pad (finFunctionFinEquiv.symm : Fin (q^L) ≃ Gram (Fin q) L) b edits S a =
      (entry? pad (dictionary q L) b edits S a).map moveEntry := by
  unfold entry?
  dsimp only
  cases h : validRun b (List.ofFn (representative pad S a)) edits with
  | none => rfl
  | some z =>
    simp only [Option.bind]
    let w := List.ofFn (representative pad S a)
    have he : z.length = l ∧ delta pad (finFunctionFinEquiv.symm : Fin (q^L) ≃ Gram (Fin q) L) w z ≠ 0 ↔
        z.length = l ∧ delta pad (dictionary q L) w z ≠ 0 := by
      rw [mainDelta, permuted_nonzero]
    by_cases hp : z.length = l ∧ delta pad (dictionary q L) w z ≠ 0
    · rw [dite_eq_left (he.mpr hp), dite_eq_left hp, Option.map_some]
      congr 1
      simp only [moveEntry, mainDelta]
    · rw [dite_eq_right (mt he.mp hp), dite_eq_right hp]
      rfl

private theorem catalogue_main (pad : Fin q) :
    catalogue pad (finFunctionFinEquiv.symm : Fin (q^L) ≃ Gram (Fin q) L) b t l =
      (catalogue pad (dictionary q L) b t l).map moveEntry := by
  unfold catalogue
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro es _
  unfold catalogueFor
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro a _
  exact entry_main pad es _ a

private def convert (indices : List ℕ) (entry : ExceptionalRecords.SerialEntry q) : EntryData q :=
  ([GramOrder.toMain indices entry.1], entry.2)

private theorem convert_eq {L : ℕ} (entry : Entry l q (q^L)) :
    convert (lexIndices q L) (ExceptionalRecords.serialize entry) = objectData (moveEntry entry).object := by
  unfold convert ExceptionalRecords.serialize objectData
  simp only [GramOrder.toMain_eq, matrixRows, Entry.object, List.ofFn_succ, List.ofFn_zero]
  rfl

def table (pad : Fin q) (b t l : ℕ) : List (EntryData q) :=
  (ExceptionalRecords.serialized pad b t l).map (convert (lexIndices q (gram q b t l)))

theorem table_eq (pad : Fin q) (b t l : ℕ) :
    table pad b t l = List.ofFn (fun i => objectData (SourceHashChoice.exceptionData q b t l pad i)) := by
  unfold table
  rw [ExceptionalRecords.serialized_eq, List.map_map]
  let catalogue := ExceptionalWeight.catalogue pad (finFunctionFinEquiv.symm : Fin (q^gram q b t l) ≃ _) b t l
  have h : List.ofFn (fun i => objectData (SourceHashChoice.exceptionData q b t l pad i)) =
      catalogue.map (fun e => objectData e.object) := by
    conv_rhs => rw [← List.ofFn_get catalogue, List.map_ofFn]
    rfl
  rw [h]
  unfold catalogue
  rw [catalogue_main, List.map_map]
  exact List.map_congr_left (fun e _ => convert_eq e)

theorem table_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (table pad b t) encUnary (Machine.SourceHashChoice.coreTableEncoding q) := by
  let a := ExceptionalRecords.serialEntryEncoding q
  let e := encPair encUnary a
  have hi := (GramOrder.lexIndices_polyTime q b t hq).comp (fst encUnary a)
  have hp := snd encUnary a
  have hr := GramOrder.toMain_polyTime.comp (encIn := e) (hi.prod hp.fst')
  have hrows := cons' hr (const [])
  exact mapWithInput (encIn := encUnary) (encA := a) (encB := entryEncoding q)
    (f := fun l v => convert (lexIndices q (gram q b t l)) v)
    (ExceptionalRecords.serialized_polyTime pad b t hq) (hrows.prod hp.snd')

abbrev prefixEncoding (q : ℕ) := encPair encUnary (encPair rowsEncoding (wordEncoding q))

def evaluatePrefix (pad : Fin q) (b t : ℕ) (p : ℕ × (Rows × QWord q)) : ℕ :=
  CataloguePrefix.prefixMass pad ((p.1, (q^gram q b t p.1, p.2.1), p.2.2), table pad b t p.1)

theorem prefix_eq (pad : Fin q) (H : ConcreteSource.Hash q b t l) {k : ℕ} (u : Fin k → Fin q) :
    evaluatePrefix pad b t (l, matrixRows H, List.ofFn u) =
      CoreWeight.prefixMass (SourceHashChoice.exceptionData q b t l pad) H u := by
  unfold evaluatePrefix
  rw [table_eq, CataloguePrefix.prefixMass_eq]

theorem prefix_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (evaluatePrefix pad b t) (prefixEncoding q) encNat := by
  let e := prefixEncoding q
  let w := wordEncoding q
  have hl := fst encUnary (encPair rowsEncoding w)
  have hw := snd encUnary (encPair rowsEncoding w)
  have hn := (Machine.SourceHashChoice.width_polyTime q b t hq).comp hl
  have ht := (table_polyTime pad b t hq).comp hl
  exact (CataloguePrefix.prefixMass_polyTime pad).comp (encIn := e)
    ((hl.prod ((hn.prod hw.fst').prod hw.snd')).prod ht)

#print axioms table_eq
#print axioms table_polyTime
#print axioms prefix_eq
#print axioms prefix_polyTime

end DeletionCode.Explicit.Machine.SourceExceptionalTable
