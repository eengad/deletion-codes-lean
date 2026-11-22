import DeletionCode.Explicit.RecognizerBirth

/-! A recorded exposed rule can be appended without losing the graph invariants. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash CanonicalColour RulePatch LetterSequence LetterGraphCuts ReplayEntry LiftDictionary
open Qary.SignedSupport
open scoped BigOperators

variable {ℓ q K b L Λ R s θ : ℕ}

private def added (pad : Fin q) (words : Fin s → Borrowed.BubbleWord (Fin q) K b L)
    (ws : List (PreparedBubble ℓ L (Fin q))) (hlen : ws.length = s) : Batch ℓ q L s :=
  ⟨CatalogueEnumeration.row pad words,fun j => ws.get (Fin.cast hlen.symm j)⟩

private theorem get_old (hs : History ℓ q L s) (p : Batch ℓ q L s) (i : Fin hs.length) :
    (hs ++ [p]).get ⟨i.val,by simp [i.isLt.trans_le (Nat.le_succ _)]⟩ = hs.get i := by
  exact List.getElem_append_left i.isLt

private theorem get_new (hs : History ℓ q L s) (p : Batch ℓ q L s) :
    (hs ++ [p]).get ⟨hs.length,by simp⟩ = p := by
  change (hs ++ [p])[hs.length]'(by simp) = p
  rw [List.getElem_append_right le_rfl]
  simp

/-- Transfer the exposure computed in finite row coordinates to the same
span as the frozen dictionary's grouped past-rule spectra. -/
theorem candidate_dictionary_exposure (H : TernaryMatrix θ (q^L)) (pad : Fin q)
    {x : Fin ℓ → Fin q} {hs : History ℓ q L s}
    {edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marked : Finset (Fin ℓ)}
    (hv : GraphValid pad x b Λ hs edges marked) (hx : Strong x K Λ) (hL : K+2*Λ+1 ≤ L)
    (words : Fin s → Borrowed.BubbleWord (Fin q) K b L)
    (hOK : candidateOK H pad x hs words = true) :
    Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span F₃ (Set.range (liftedRule (L := L) pad x (completed hs))))
      (gramEquiv (q := q) (L := L) (CatalogueEnumeration.row pad words)) := by
  have hbase := spectrum_isBoolean (L := L) pad x hx (by omega)
  have hparts {i j : Fin hs.length} (hne : i ≠ j) (g : Fin (q^L))
      (hg : ComponentExposure.occupies (parts hs i) g = true) :
      ComponentExposure.occupies (parts hs j) g ≠ true :=
    parts_support_disjoint pad x hs hx hv.fit (by omega) hv.vectors hne g hg
  obtain ⟨_,_,w,hw,h₁,h₂⟩ := (candidateOK_iff H pad x hs words hbase hparts).mp hOK
  refine ⟨gramEquiv (q := q) (L := L) w,?_,?_,?_⟩
  · rw [← history_span pad x hs hv.chronology hv.vectors]
    exact Submodule.mem_map_of_mem hw
  · intro g
    have hg := h₁ (finFunctionFinEquiv g)
    change fieldSpectrum (paddedLetters pad x) ℓ L g+w (finFunctionFinEquiv g) = 0 ∨
      fieldSpectrum (paddedLetters pad x) ℓ L g+w (finFunctionFinEquiv g) = 1
    simpa [spectrum] using hg
  · intro g
    have hg := h₂ (finFunctionFinEquiv g)
    change fieldSpectrum (paddedLetters pad x) ℓ L g+w (finFunctionFinEquiv g)+
        CatalogueEnumeration.row pad words (finFunctionFinEquiv g) = 0 ∨
      fieldSpectrum (paddedLetters pad x) ℓ L g+w (finFunctionFinEquiv g)+
        CatalogueEnumeration.row pad words (finFunctionFinEquiv g) = 1
    simpa [spectrum] using hg

set_option maxHeartbeats 1000000 in
theorem appendRule_correct (P : RuleAddition.Bounds K b L Λ s R)
    (pad : Fin q) {x : Fin ℓ → Fin q} (root : Fin ℓ) {hs : History ℓ q L s}
    {edges : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marked : Finset (Fin ℓ)}
    (hv : GraphValid pad x b Λ hs edges marked) (hx : Strong x K Λ)
    (hcutoff : ∀ p, (componentRules (PatchTable.incidence (gates hs)) (.inr p)).card ≤ R)
    (words : Fin s → Borrowed.BubbleWord (Fin q) K b L)
    (hcat : @Borrowed.Catalogue.ValidCatalogue _ ⟨pad⟩ K b L s 1 words (fun _ => 0))
    (hwords : words ∈ CatalogueEnumeration.rules q K b L s pad)
    (hout : CatalogueEnumeration.row pad words ∉ span (oldRows hs))
    (hexposed : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span F₃ (Set.range (liftedRule (L := L) pad x (completed hs))))
      (gramEquiv (q := q) (L := L) (CatalogueEnumeration.row pad words))) :
    ∃ p, appendRule pad x root hs words = some (hs++[p]) ∧
      RecordedBatch P pad x root hs p ∧
      ∃ edges' marked', GraphValid pad x b Λ (hs++[p]) edges' marked' := by
  have hold (i : ℕ) (out : Completed ℓ (Fin q)) (h : (completed hs)[i]? = some out) :
      ∀ side, (out.lift side).2.Follows edges := by
    obtain ⟨e,rfl⟩ := get?_completed hs h
    exact hv.follows e
  obtain ⟨ws,hlen,hw,hspec⟩ := RuleAddition.prepareRule_correct P pad x (completed hs) (gates hs)
    hv.graph hv.records (ids_injective hs hv.chronology) hv.lowWidth hv.marks hv.stock
    hcutoff hx words hcat hexposed root hs.length (rules_increasing hs hv.chronology) hold
  let batch := added pad words ws hlen
  let hs' := hs ++ [batch]
  have happ : appendRule pad x root hs words = some hs' := by
    have h : ∀ j, 0 < (words j).left.length ∧ 0 < (words j).right.length :=
      fun j => ⟨RuleAddition.left_pos P _,RuleAddition.right_pos P _⟩
    simp [appendRule,h,hw,hlen,hs',batch,added]
  have hs_old (i : Fin hs.length) : hs'.get ⟨i.val,by simp [hs']⟩ = hs.get i := get_old hs batch i
  have hs_new : hs'.get ⟨hs.length,by simp [hs']⟩ = batch := get_new hs batch
  let data' : Fin (hs.length+1) × Fin s → GateData ℓ (Fin q) :=
    fun e => (hs'.get ⟨e.1.val,by simpa [hs'] using e.1.isLt⟩ |>.bubbles e.2).data
  have hkeep (e : Fin hs.length × Fin s) : ∃ f, data' f = gates hs e := by
    refine ⟨(e.1.castSucc,e.2),?_⟩
    dsimp only [data',gates,Fin.val_castSucc]
    rw [hs_old e.1]
  have hdata (j : Fin s) :
      data' (Fin.last hs.length,j) = (ws.get (Fin.cast hlen.symm j)).data := by
    dsimp only [data',Fin.val_last]
    rw [hs_new]
    rfl
  have hnew : ∀ e, (gates hs e).id < (completed hs).size := ids_below hs hv.chronology
  obtain ⟨hgraph,hrecords⟩ := RuleAddition.installBatch P hv.graph (gates hs) data' hv.records
    hkeep ws hlen words (completed hs).size hs.length hspec hnew hdata
  let E' := installedEdges edges ws
  let marks' := installedMarks marked ws
  have hn (j : Fin s) : RuleAddition.PreparedSpec P x edges (words j)
      ((completed hs).size+j.val) hs.length (batch.bubbles j) := hspec j
  have get_cases (i : Fin hs'.length) :
      (∃ k : Fin hs.length, i.val = k.val ∧ hs'.get i = hs.get k) ∨
      (i.val = hs.length ∧ hs'.get i = batch) := by
    by_cases h : i.val < hs.length
    · exact Or.inl ⟨⟨i.val,h⟩,rfl,hs_old ⟨i.val,h⟩⟩
    · have hh : i.val = hs.length := by have hi := i.isLt; simp [hs'] at hi; omega
      exact Or.inr ⟨hh,(Fin.ext hh : i = ⟨hs.length,by simp [hs']⟩) ▸ hs_new⟩
  have hbatch_paths : ∀ p ∈ ws, p.gate.negative.Follows edges := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    exact (hspec (Fin.cast hlen i)).follows
  have hrec : PatchTable.RecordsGraph (gates hs') E' marks' := by
    have htotal : hs'.length = hs.length+1 := by simp [hs']
    refine ⟨?_,?_⟩
    · intro k hk
      obtain ⟨e,he⟩ := hrecords.1 k hk
      exact ⟨(Fin.cast htotal.symm e.1,e.2),he⟩
    · intro r k a ha
      obtain ⟨e,he⟩ := hrecords.2 r k a ha
      exact ⟨(Fin.cast htotal.symm e.1,e.2),he⟩
  have hcases (i : Fin hs'.length) (j : Fin s) :
      (∃ k : Fin hs.length, i.val = k.val ∧ (hs'.get i).bubbles j = (hs.get k).bubbles j) ∨
      (i.val = hs.length ∧ (hs'.get i).bubbles j = batch.bubbles j) := by
    rcases get_cases i with ⟨k,hk,he⟩ | ⟨hk,he⟩
    · exact Or.inl ⟨k,hk,congrArg (fun row : Batch ℓ q L s => row.bubbles j) he⟩
    · exact Or.inr ⟨hk,congrArg (fun row : Batch ℓ q L s => row.bubbles j) he⟩
  have hbatch : RecordedBatch P pad x root hs batch := by
    refine ⟨hout,words,hwords,rfl,edges,?_⟩
    intro j
    exact ⟨RuleAddition.prepareRule_readback P pad x (completed hs) words root hs.length ws hlen hw j,hn j⟩
  refine ⟨batch,happ,hbatch,E',marks',⟨?_,hgraph,hrec,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j
    rcases hcases i j with ⟨k,hi,he⟩ | ⟨hi,he⟩
    · rw [he,hi]
      exact hv.chronology k j
    · rw [he,hi]
      exact ⟨by simpa only [completed_size] using (hn j).id,(hn j).rule_id⟩
  · rintro ⟨i,j⟩ side
    change (((hs'.get i).bubbles j).completed.lift side).2.Follows E'
    rcases hcases i j with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact fun u v huv => RuleAddition.installedEdges_contains edges ws _ _ (hv.follows (k,j) side u v huv)
    · rw [he]
      exact RuleAddition.installed_paths edges ws hbatch_paths _ (List.get_mem ..) side
  · rintro ⟨i,j⟩ side
    change let u := ((hs'.get i).bubbles j).completed.lift side
      u.2.positions ⊆ Finset.Icc ((hs'.get i).bubbles j).data.interval.first.val
        ((hs'.get i).bubbles j).data.interval.last.val ∧ u.2.freshOffsets.card ≤ Λ ∧ u.2.omissions.card ≤ Λ
    rcases hcases i j with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact hv.fit (k,j) side
    · rw [he]
      have h := hn j
      have hb := P.counts
      cases side
      · exact ⟨h.negInside,h.fresh.trans (by omega),h.omitted.trans (by omega)⟩
      · exact ⟨h.posInside,h.posFresh,h.posOmitted⟩
  · rintro ⟨i,j⟩
    change L ≤ 2*(((hs'.get i).bubbles j).data.interval.last.val+1-
      ((hs'.get i).bubbles j).data.interval.first.val)
    rcases hcases i j with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact hv.lowWidth (k,j)
    · rw [he]
      exact (hn j).lowWidth
  · rintro ⟨i,j⟩
    change ((hs'.get i).bubbles j).data.interval.last.val+1-((hs'.get i).bubbles j).data.interval.first.val ≤ 3*L
    rcases hcases i j with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact hv.highWidth (k,j)
    · rw [he]
      exact (hn j).highWidth
  · rintro ⟨i,j⟩
    change ((hs'.get i).bubbles j).data.marks.card ≤ b
    rcases hcases i j with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact hv.marks (k,j)
    · rw [he]
      exact (hn j).marks
  · rintro ⟨i,j⟩
    change ((hs'.get i).bubbles j).data.inserted.card ≤ b
    rcases hcases i j with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact hv.stock (k,j)
    · rw [he]
      exact (hn j).stock
  · intro i g
    change (hs'.get i).row (finFunctionFinEquiv g) =
      ∑ j : Fin s, bubbleVector pad x ((hs'.get i).bubbles j).completed g
    rcases get_cases i with ⟨k,_,he⟩ | ⟨_,he⟩
    · rw [he]
      exact hv.vectors k g
    · rw [he]
      change (∑ j : Fin s, BubbleFamilies.vector pad (words j) (finFunctionFinEquiv g)) =
        ∑ j : Fin s, bubbleVector pad x (batch.bubbles j).completed g
      apply Finset.sum_congr rfl
      intro j _
      exact ((hn j).vector_eq (pad := pad) g).symm

#print axioms candidate_dictionary_exposure
#print axioms appendRule_correct

end DeletionCode.Explicit.Recognizer
