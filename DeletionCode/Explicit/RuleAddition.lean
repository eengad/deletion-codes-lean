import DeletionCode.Explicit.PrepareRule
import DeletionCode.Explicit.CatalogueCoordinates

/-! Correctness of the frozen preparation for an exposed rule. -/

namespace DeletionCode.Explicit.RuleAddition

open LetterSequence LetterGraphCuts ReplayEntry LiftDictionary Borrowed
open Qary.SignedSupport

variable {ℓ q d s K b L Λ R : ℕ}

private abbrev budget (s b R : ℕ) := 14*(s*b*R)

structure Bounds (K b L Λ s R : ℕ) : Prop where
  window : 3*(K+b+1) ≤ L
  room : 4*(s*b*R) ≤ L
  flank : budget s b R < L-1-K-b
  counts : budget s b R+b ≤ Λ
  lowerWidth : 2*budget s b R ≤ L
  upperWidth : b+budget s b R ≤ L
  overlap : (L+b-1)/2+(K+2*Λ) ≤ L

theorem left_pos (P : Bounds K b L Λ s R) (w : BubbleWord (Fin q) K b L) :
    0 < w.left.length := P.flank.trans_le w.left_lower |>.pos

theorem right_pos (P : Bounds K b L Λ s R) (w : BubbleWord (Fin q) K b L) :
    0 < w.right.length := P.flank.trans_le w.right_lower |>.pos

/-- All geometric facts about a newly prepared bubble that persist after installation. -/
structure PreparedSpec (P : Bounds K b L Λ s R) (x : Fin ℓ → Fin q)
    (E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop)
    (w : BubbleWord (Fin q) K b L) (current rule : ℕ)
    (p : PreparedBubble ℓ L (Fin q)) : Prop where
  left : p.left = w.left.length
  removed : p.removed = w.removed.length
  inserted : p.inserted = w.replacement.length
  right : p.right = w.right.length
  id : p.gate.entry = current
  rule_id : p.rule = rule
  spelling : List.ofFn (p.gate.negative.spelling x) = w.negativeWord
  positiveSpelling : List.ofFn (p.gate.positive.spelling x) = w.positiveWord
  follows : p.gate.negative.Follows E
  fresh : p.gate.negative.freshOffsets.card ≤ budget s b R
  omitted : p.gate.negative.omissions.card ≤ budget s b R
  lowWidth : L ≤ 2*(p.data.interval.last.val+1-p.data.interval.first.val)
  highWidth : p.data.interval.last.val+1-p.data.interval.first.val ≤ 3*L
  marks : p.data.marks.card ≤ b
  stock : p.data.inserted.card ≤ b
  negInside : p.gate.negative.positions ⊆
    Finset.Icc p.data.interval.first.val p.data.interval.last.val
  posInside : p.gate.positive.positions ⊆
    Finset.Icc p.data.interval.first.val p.data.interval.last.val
  posFresh : p.gate.positive.freshOffsets.card ≤ Λ
  posOmitted : p.gate.positive.omissions.card ≤ Λ

private theorem negative_length (w : BubbleWord (Fin q) K b L) :
    w.negativeWord.length = w.left.length+w.removed.length+w.right.length := by
  simp [BubbleWord.negativeWord,Nat.add_assoc]

private theorem negativeLetters_agree (pad : Fin q) (w : BubbleWord (Fin q) K b L)
    (a : ℕ) (ha : a+L ≤ w.left.length+w.removed.length+w.right.length) :
    gram (paddedLetters pad (negativeLetters w)) L a = gram (paddedLetters pad w.negativeWord.get) L a := by
  funext i
  have hi : a+i.val < w.left.length+w.removed.length+w.right.length := by omega
  have hj : a+i.val < w.negativeWord.length := by rw [negative_length]; exact hi
  simp [gram,paddedLetters,negativeLetters,hi,hj]

private theorem spelling_eq (x : Fin ℓ → Fin q) (w : BubbleWord (Fin q) K b L)
    (v : Lift ℓ (w.left.length+w.removed.length+w.right.length) (Fin q))
    (h : SpellsAt v x (negativeLetters w) 0) :
    List.ofFn (v.spelling x) = w.negativeWord := by
  apply List.ext_getElem
  · simp [negative_length]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    have h' := h.2 ⟨i,by simpa using hi⟩ ⟨i,by simpa using hi⟩ (Nat.zero_add i)
    simpa [negativeLetters] using h'

private theorem positive_spelling (x : Fin ℓ → Fin q) (w : BubbleWord (Fin q) K b L)
    (g : Gate ℓ w.left.length w.removed.length w.replacement.length w.right.length (Fin q))
    (hneg : List.ofFn (g.negative.spelling x) = w.negativeWord)
    (hrep : g.replacement = w.replacement.get) :
    List.ofFn (g.positive.spelling x) = w.positiveWord := by
  let negative := Fin.append (Fin.append w.left.get w.removed.get) w.right.get
  let positive := Fin.append (Fin.append w.left.get w.replacement.get) w.right.get
  have hn : g.negative.spelling x = negative := by
    apply List.ofFn_injective
    rw [hneg]
    simp [negative,List.ofFn_fin_append,BubbleWord.negativeWord,List.append_assoc]
  have hp : g.positive.spelling x = positive := by
    funext i
    have hf := g.negative.gate_flanks g.entry g.replacement x
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · have h := hf.1 k
        change g.positive.spelling x (Fin.castAdd w.right.length (Fin.castAdd w.replacement.length k)) =
          g.negative.spelling x (Fin.castAdd w.right.length (Fin.castAdd w.removed.length k)) at h
        rw [hn] at h
        simpa only [positive,negative,Fin.append_left] using h
      · have h := g.negative.gate_middle g.entry g.replacement x k
        change g.positive.spelling x (Fin.castAdd w.right.length (Fin.natAdd w.left.length k)) =
          g.replacement k at h
        rw [hrep] at h
        simpa only [positive,Fin.append_left,Fin.append_right] using h
    · have h := hf.2 j
      change g.positive.spelling x (Fin.natAdd (w.left.length+w.replacement.length) j) =
        g.negative.spelling x (Fin.natAdd (w.left.length+w.removed.length) j) at h
      rw [hn] at h
      simpa only [positive,negative,Fin.append_right] using h
  rw [hp]
  simp [positive,List.ofFn_fin_append,BubbleWord.positiveWord,List.append_assoc]

/-- The dictionary theorem applies to each negative word in a valid rule,
using its actual signed spectrum coefficient. -/
theorem prepareBubble_correct (P : Bounds K b L Λ s R)
    (pad : Fin q) (x : Fin ℓ → Fin q) (history : Array (Completed ℓ (Fin q)))
    (data : Fin d × Fin s → GateData ℓ (Fin q))
    {E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marked : Finset (Fin ℓ)}
    (H : LetterGraphCuts.History ℓ (Fin q) E marked) (hrecords : PatchTable.RecordsGraph data E marked)
    (hid : Function.Injective (fun e => (data e).id))
    (hwidth : ∀ e, L ≤ 2*((data e).interval.last.val+1-(data e).interval.first.val))
    (hmark : ∀ e, (data e).marks.card ≤ b) (hstock : ∀ e, (data e).inserted.card ≤ b)
    (hcutoff : ∀ p, (RulePatch.componentRules (PatchTable.incidence data) (.inr p)).card ≤ R)
    (hx : Strong x K Λ) (words : Fin s → BubbleWord (Fin q) K b L)
    (hcat : @Catalogue.ValidCatalogue _ ⟨pad⟩ K b L s 1 words (fun _ => 0))
    (hexposed : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span (ZMod 3) (Set.range (liftedRule pad x history)))
      (fun g => CatalogueEnumeration.row pad words (finFunctionFinEquiv g)))
    (root : Fin ℓ) (current rule : ℕ) (j : Fin s) (hc : history.size ≤ current)
    (hr : ∀ i : Fin history.size, history[i].rule < rule)
    (hold : ∀ (i : ℕ) (out : Completed ℓ (Fin q)), history[i]? = some out → ∀ side, (out.lift side).2.Follows E) :
    ∃ p, prepareBubble pad x history (words j) root current rule (left_pos P _) (right_pos P _) = some p ∧
      PreparedSpec P x E (words j) current rule p := by
  let w := words j
  have hL : 2 ≤ L := by have h := P.window; omega
  have hΛ : budget s b R ≤ Λ := by have h := P.counts; omega
  have hlo := (Catalogue.word_length_bounds w false P.window).1
  have hhi := (Catalogue.word_length_bounds w false P.window).2
  change L ≤ w.negativeWord.length at hlo
  change w.negativeWord.length ≤ 2*(L-1)+b at hhi
  rw [negative_length] at hlo hhi
  have hshort : w.left.length+w.removed.length+w.right.length ≤ 3*L := by
    have h := P.upperWidth
    omega
  have hoverlap : (w.left.length+w.removed.length+w.right.length-L+1)/2+(K+2*Λ) ≤ L := by
    have hd : (w.left.length+w.removed.length+w.right.length-L+1)/2 ≤ (L+b-1)/2 :=
      Nat.div_le_div_right (by omega)
    exact (Nat.add_le_add_right hd _).trans P.overlap
  have hneg (a : ℕ) (ha : a+L ≤ w.left.length+w.removed.length+w.right.length) :
      CatalogueEnumeration.row pad words (finFunctionFinEquiv (gram (paddedLetters pad (negativeLetters w)) L a)) = -1 := by
    rw [negativeLetters_agree pad w a ha]
    exact CatalogueEnumeration.negative_gram pad words hcat j a (by rw [negative_length]; exact ha)
  obtain ⟨os,v,he,hsp,hpath,hfresh,homit⟩ := prepareNegative_correct pad x history data H hrecords hid
    hx hL P.room hΛ hwidth hmark hstock hcutoff hc hr hold root w.left.length w.removed w.replacement
    w.right.length (negativeLetters w) hexposed hneg hlo hshort hoverlap
  have hflank : v.freshOffsets.card < w.left.length :=
    hfresh.trans_lt (P.flank.trans_le w.left_lower)
  obtain ⟨g,hn,hg,hid',hrepl,hprep⟩ := prepareBubble_of_negative pad x history w root current rule
    (left_pos P w) (right_pos P w) os v he hflank
  let p : PreparedBubble ℓ L (Fin q) := ⟨os,rule,_,_,_,_,g,hn⟩
  refine ⟨p,hprep,?_⟩
  have hf : g.negative.freshOffsets.card ≤ budget s b R := hg.symm ▸ hfresh
  have ho : g.negative.omissions.card ≤ budget s b R := hg.symm ▸ homit
  have hw := g.creation_width hn hf ho
  have hpad := P.upperWidth
  have hdual := P.lowerWidth
  have hc₁ := (g.data_card hn).1.trans w.removed_bound
  have hc₂ := (g.data_card hn).2.trans w.replacement_bound
  have hnegSpell : List.ofFn (g.negative.spelling x) = w.negativeWord := hg.symm ▸ spelling_eq x w v hsp
  refine ⟨rfl,rfl,rfl,rfl,hid',rfl,hnegSpell,positive_spelling x w g hnegSpell hrepl,
    hg.symm ▸ hpath,hf,ho,?_,?_,hc₁,hc₂,?_,?_,?_,?_⟩
  · change L ≤ 2*((g.creationInterval hn).last.val+1-(g.creationInterval hn).first.val)
    dsimp only at hw
    omega
  · change (g.creationInterval hn).last.val+1-(g.creationInterval hn).first.val ≤ 3*L
    dsimp only at hw
    omega
  · intro k hk
    exact Finset.mem_Icc.mpr (CreationInterval.ofLift_contains_position g.negative hn hk)
  · intro k hk
    exact Finset.mem_Icc.mpr (g.positive_enclosed hn hk)
  · exact g.positive_fresh_le.trans ((Nat.add_le_add hf w.replacement_bound).trans P.counts)
  · exact g.positive_omissions_le.trans ((Nat.add_le_add ho w.removed_bound).trans P.counts)

set_option maxHeartbeats 600000 in
/-- The complete batch is prepared using the one frozen dictionary, with
the geometric conclusions available at every bubble index. -/
theorem prepareRule_correct (P : Bounds K b L Λ s R)
    (pad : Fin q) (x : Fin ℓ → Fin q) (history : Array (Completed ℓ (Fin q)))
    (data : Fin d × Fin s → GateData ℓ (Fin q))
    {E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marked : Finset (Fin ℓ)}
    (H : LetterGraphCuts.History ℓ (Fin q) E marked) (hrecords : PatchTable.RecordsGraph data E marked)
    (hid : Function.Injective (fun e => (data e).id))
    (hwidth : ∀ e, L ≤ 2*((data e).interval.last.val+1-(data e).interval.first.val))
    (hmark : ∀ e, (data e).marks.card ≤ b) (hstock : ∀ e, (data e).inserted.card ≤ b)
    (hcutoff : ∀ p, (RulePatch.componentRules (PatchTable.incidence data) (.inr p)).card ≤ R)
    (hx : Strong x K Λ) (words : Fin s → BubbleWord (Fin q) K b L)
    (hcat : @Catalogue.ValidCatalogue _ ⟨pad⟩ K b L s 1 words (fun _ => 0))
    (hexposed : Exposed (fieldSpectrum (paddedLetters pad x) ℓ L)
      (Submodule.span (ZMod 3) (Set.range (liftedRule pad x history)))
      (fun g => CatalogueEnumeration.row pad words (finFunctionFinEquiv g)))
    (root : Fin ℓ) (rule : ℕ) (hr : ∀ i : Fin history.size, history[i].rule < rule)
    (hold : ∀ (i : ℕ) (out : Completed ℓ (Fin q)), history[i]? = some out → ∀ side, (out.lift side).2.Follows E) :
    ∃ ws, ∃ hlen : ws.length = s,
      prepareRule pad x history words root rule (fun j => left_pos P (words j))
        (fun j => right_pos P (words j)) = some ws ∧
      ∀ j : Fin s, PreparedSpec P x E (words j) (history.size+j.val) rule (ws.get (Fin.cast hlen.symm j)) := by
  have hp (j : Fin s) := prepareBubble_correct P pad x history data H hrecords hid
    hwidth hmark hstock hcutoff hx words hcat hexposed root (history.size+j.val) rule j
    (Nat.le_add_right _ _) hr hold
  obtain ⟨ws,he,hs⟩ := prepareRule_of_bubbles pad x history words root rule
    (fun j => left_pos P _) (fun j => right_pos P _) (fun j => (hp j).imp fun _ h => h.1)
  have hlen : ws.length = s := by simpa using hs.length_eq.symm
  refine ⟨ws,hlen,he,fun j => ?_⟩
  have hj : j.val < (List.finRange s).length := by simp
  have hh := hs.get hj (show j.val < ws.length by rw [hlen]; exact j.isLt)
  let prepare (i : Fin s) := prepareBubble pad x history (words i) root (history.size+i.val) rule
    (left_pos P (words i)) (right_pos P (words i))
  have hindex : (List.finRange s).get ⟨j.val,hj⟩ = j :=
    (List.getElem_finRange hj).trans (Fin.ext rfl)
  have hh' : prepare j = some (ws.get (Fin.cast hlen.symm j)) :=
    (congrArg prepare hindex).symm.trans hh
  obtain ⟨p,hp,hvalid⟩ := hp j
  exact (Option.some.inj (hp.symm.trans hh')) ▸ hvalid

/-- Reading back the prepared batch returns the successful call for each bubble. -/
theorem prepareRule_readback (P : Bounds K b L Λ s R) (pad : Fin q) (x : Fin ℓ → Fin q)
    (history : Array (Completed ℓ (Fin q))) (words : Fin s → BubbleWord (Fin q) K b L)
    (root : Fin ℓ) (rule : ℕ) (ws : List (PreparedBubble ℓ L (Fin q))) (hlen : ws.length = s)
    (h : prepareRule pad x history words root rule (fun j => left_pos P (words j))
      (fun j => right_pos P (words j)) = some ws) (j : Fin s) :
    prepareBubble pad x history (words j) root (history.size+j.val) rule (left_pos P _) (right_pos P _) =
      some (ws.get (Fin.cast hlen.symm j)) := by
  let f (i : Fin s) := prepareBubble pad x history (words i) root (history.size+i.val) rule
    (left_pos P _) (right_pos P _)
  have hmap {A B : Type} (f : A → Option B) (a : List A) (b : List B) (hm : a.mapM f = some b) :
      List.Forall₂ (fun x y => f x = some y) a b := by
    induction a generalizing b with
    | nil =>
      have he : [] = b := Option.some.inj hm
      subst b
      exact .nil
    | cons k tail ih =>
      cases hh : f k with
      | none => simp [List.mapM_cons,hh] at hm
      | some p =>
        cases ht : tail.mapM f with
        | none => simp [List.mapM_cons,hh,ht] at hm
        | some rest =>
          have he : p :: rest = b := by simpa [List.mapM_cons,hh,ht] using hm
          subst b
          exact .cons hh (ih rest ht)
  have hh := hmap f (List.finRange s) ws h
  have hj : j.val < (List.finRange s).length := by simp
  have hindex : (List.finRange s).get ⟨j.val,hj⟩ = j :=
    (List.getElem_finRange hj).trans (Fin.ext rfl)
  exact (congrArg f hindex).symm.trans (hh.get hj (show j.val < ws.length by rw [hlen]; exact j.isLt))

#print axioms prepareRule_readback

private theorem padded_spelling (pad : Fin q) {m : ℕ} (x : Fin m → Fin q) :
    paddedLetters pad x = fun i => (List.ofFn x).getD i pad := by
  funext i
  by_cases h : i < m
  · simp [paddedLetters,h,List.getD_eq_getElem?_getD]
  · simp [paddedLetters,h,List.getD_eq_getElem?_getD]

theorem PreparedSpec.vector_eq {P : Bounds K b L Λ s R} {pad : Fin q} {x : Fin ℓ → Fin q}
    {E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {w : BubbleWord (Fin q) K b L}
    {current rule : ℕ} {p : PreparedBubble ℓ L (Fin q)}
    (h : PreparedSpec P x E w current rule p) (g : Gram (Fin q) L) :
    bubbleVector pad x p.completed g = BubbleFamilies.vector pad w (finFunctionFinEquiv g) := by
  have hspec {m : ℕ} (y : Fin m → Fin q) :
      fieldSpectrum (paddedLetters pad y) m L g = listFieldSpectrum pad (List.ofFn y) L g := by
    unfold listFieldSpectrum
    rw [padded_spelling]
    simp
  unfold bubbleVector PreparedBubble.completed BubbleFamilies.vector
  simp only [Equiv.symm_apply_apply]
  change fieldSpectrum (paddedLetters pad (p.gate.positive.spelling x)) _ L g -
    fieldSpectrum (paddedLetters pad (p.gate.negative.spelling x)) _ L g = _
  rw [hspec,hspec,h.spelling,h.positiveSpelling]

theorem installedEdges_contains (E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop)
    (ws : List (PreparedBubble ℓ L (Fin q))) :
    E ≤ installedEdges E ws := by
  intro a c h
  induction ws generalizing E with
  | nil => exact h
  | cons p ps ih => exact ih (p.gate.edges E) (Or.inl h)

/-- Each installed bubble keeps both paths in the enlarged graph. -/
theorem installed_paths (E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop)
    (ws : List (PreparedBubble ℓ L (Fin q))) (hpath : ∀ p ∈ ws, p.gate.negative.Follows E)
    (p : PreparedBubble ℓ L (Fin q)) (hp : p ∈ ws) (side : Side) :
    (p.completed.lift side).2.Follows (installedEdges E ws) := by
  cases side with
  | negative => exact fun i j hj => installedEdges_contains E ws _ _ (hpath p hp i j hj)
  | positive =>
    induction ws generalizing E with
    | nil => simp at hp
    | cons u rest ih =>
      have hu := hpath u (List.mem_cons_self ..)
      rcases List.mem_cons.mp hp with rfl | hrest
      · exact fun i j hj => installedEdges_contains (p.gate.edges E) rest _ _
          (p.gate.positive_follows hu i j hj)
      · exact ih (u.gate.edges E)
          (fun u' hu' i j hj => Or.inl (hpath u' (List.mem_cons_of_mem _ hu') i j hj)) hrest

private theorem lift_records
    {new : Fin (d+1) × Fin s → GateData ℓ (Fin q)} {old : Fin d × Fin s → GateData ℓ (Fin q)}
    {E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marked : Finset (Fin ℓ)}
    (h : PatchTable.RecordsGraph old E marked) (hkeep : ∀ e, ∃ f, new f = old e) :
    PatchTable.RecordsGraph new E marked := by
  refine ⟨?_,?_⟩
  · intro i hi
    obtain ⟨e,he⟩ := h.1 i hi
    obtain ⟨f,hf⟩ := hkeep e
    exact ⟨f,hf ▸ he⟩
  · intro id k x hi
    obtain ⟨e,he⟩ := h.2 id k x hi
    obtain ⟨f,hf⟩ := hkeep e
    exact ⟨f,hf ▸ he⟩

/-- Install the verified batch, moving its bracket and mark records to
the enlarged gate table. Fresh identifiers are exactly their chronology indices. -/
theorem installBatch (P : Bounds K b L Λ s R) {x : Fin ℓ → Fin q}
    {E : Letter ℓ (Fin q) → Letter ℓ (Fin q) → Prop} {marked : Finset (Fin ℓ)}
    (H : LetterGraphCuts.History ℓ (Fin q) E marked)
    (old : Fin d × Fin s → GateData ℓ (Fin q)) (new : Fin (d+1) × Fin s → GateData ℓ (Fin q))
    (hrecords : PatchTable.RecordsGraph old E marked)
    (hkeep : ∀ e, ∃ f, new f = old e)
    (ws : List (PreparedBubble ℓ L (Fin q))) (hlen : ws.length = s)
    (words : Fin s → BubbleWord (Fin q) K b L) (start rule : ℕ)
    (hspec : ∀ j : Fin s, PreparedSpec P x E (words j) (start+j.val) rule (ws.get (Fin.cast hlen.symm j)))
    (hnew : ∀ e, (old e).id < start)
    (hdata : ∀ j : Fin s, new (Fin.last d,j) = (ws.get (Fin.cast hlen.symm j)).data) :
    LetterGraphCuts.History ℓ (Fin q) (installedEdges E ws) (installedMarks marked ws) ∧
      PatchTable.RecordsGraph new (installedEdges E ws) (installedMarks marked ws) := by
  have hmember (p : PreparedBubble ℓ L (Fin q)) (hp : p ∈ ws) :
      ∃ j : Fin s, p = ws.get (Fin.cast hlen.symm j) := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    exact ⟨Fin.cast hlen i,hi.symm⟩
  have hpath (p : PreparedBubble ℓ L (Fin q)) (hp : p ∈ ws) : p.gate.negative.Follows E := by
    obtain ⟨j,rfl⟩ := hmember p hp
    exact (hspec j).follows
  have hids : (ws.map (fun p => p.gate.entry)).Nodup := by
    have he : ws.map (fun p => p.gate.entry) = List.ofFn (fun i : Fin ws.length => start+i.val) := by
      conv_lhs => rw [← List.ofFn_get ws,List.map_ofFn]
      congr 1
      funext i
      exact (hspec (Fin.cast hlen i)).id
    rw [he,List.nodup_ofFn]
    intro i j h
    exact Fin.ext (Nat.add_left_cancel h)
  have hfresh : ∀ p ∈ ws, ∀ k (a : Fin q), ¬ SelectedReplay.Incident E (.fresh p.gate.entry k a) := by
    intro p hp k a
    obtain ⟨j,rfl⟩ := hmember p hp
    rw [(hspec j).id]
    apply PatchTable.RecordsGraph.entry_unused old hrecords _ k a
    intro e he
    have h := hnew e
    omega
  refine ⟨install_prepared_rule H ws hpath hids hfresh,installed_records (lift_records hrecords hkeep) ws hpath ?_ ?_⟩
  · intro p hp
    obtain ⟨j,rfl⟩ := hmember p hp
    have h := hspec j
    exact ⟨h.fresh.trans_lt (h.left.symm ▸ P.flank.trans_le (words j).left_lower),
      h.fresh.trans_lt (h.right.symm ▸ P.flank.trans_le (words j).right_lower)⟩
  · intro p hp
    obtain ⟨j,rfl⟩ := hmember p hp
    exact ⟨(Fin.last d,j),hdata j⟩

#print axioms installed_paths
#print axioms installBatch
#print axioms prepareBubble_correct
#print axioms prepareRule_correct
#print axioms PreparedSpec.vector_eq

end DeletionCode.Explicit.RuleAddition
