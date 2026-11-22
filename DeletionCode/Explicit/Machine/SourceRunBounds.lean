import DeletionCode.Explicit.Machine.SourceRecognition

/-! Bounds for the reachable state of the serialized chronological scan. -/
namespace DeletionCode.Explicit.Machine.SourceRunBounds

open SourceRecognition
open SourceRuleRows (RuleRow)
open SourceLetters (LiftData LetterData original window install)
open SourceDictionary (OccurrenceData)
open SourcePrepare (Prepared)
open OrderedCatalogue (BubbleData)
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {q N M : ℕ}

def letter (M : ℕ) (a : LetterData q) : Prop :=
  a.1 ≤ M ∧ ∀ p ∈ a.2, p.1 ≤ M

def letters (M : ℕ) (w : LiftData q) : Prop := ∀ a ∈ w, letter M a

def occurrence (M N : ℕ) (o : OccurrenceData q) : Prop :=
  o.1.1 ≤ M ∧ (∀ p ∈ o.1.2, p.2 ≤ M) ∧ o.2.length ≤ N ∧ letters M o.2

def prepared (M N : ℕ) (p : Prepared q) : Prop :=
  p.rule ≤ M ∧ p.entry ≤ M ∧ p.left ≤ N ∧ p.removed ≤ N ∧ p.right ≤ N ∧
    p.replacement.length ≤ N ∧ p.windows.length ≤ 3 ∧
    (∀ o ∈ p.windows, occurrence M N o) ∧ p.negative.length ≤ 3*N ∧ letters M p.negative

def boundedHistory (cfg : Config q) (M N i : ℕ) (hs : History q) : Prop :=
  hs.length ≤ i ∧ ∀ b ∈ hs, (Ternary.rowEncoding b.1).length ≤ N ∧ b.2.length = cfg.arity ∧ ∀ p ∈ b.2, prepared M N p

private theorem letters_getD {w : LiftData q} (h : letters M w) (i : ℕ) :
    letter M (w.getD i (0,none)) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact h _ (List.getElem_mem _)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt hi),letter]

theorem original_bound {start len : ℕ} (h : start+len ≤ M) :
    letters M (original q start len) := by
  intro a ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_range] at hj
  exact ⟨by omega,by simp⟩

private theorem window_bound {w : LiftData q} (h : letters M w) (start len : ℕ) :
    letters M (window w start len) := fun a ha =>
  h a (List.mem_of_mem_drop (List.mem_of_mem_take ha))

private theorem append_bound {u v w : LiftData q} (hu : letters M u) (hv : letters M v) {start : ℕ}
    (h : SourceLetters.appendWindow u start v = some w) : letters M w := by
  unfold SourceLetters.appendWindow at h
  split at h
  · unfold SourceLetters.splice at h
    obtain ⟨p,_,heq⟩ := Option.map_eq_some_iff.mp h
    subst w
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    split
    · exact letters_getD hu _
    · exact letters_getD hv _
  · contradiction

theorem install_bound (pad : Fin q) {current left removed : ℕ}
    {neg : LiftData q} {replacement : QWord q} (hn : letters M neg)
    (hc : current ≤ M) (hr : replacement.length ≤ M) :
    letters M (install pad current left removed neg replacement) := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  split
  · exact letters_getD hn _
  · split
    · rename_i h
      refine ⟨hc,?_⟩
      intro p hp
      have he : p = (i-left,replacement.getD (i-left) pad) := Option.some.inj (Option.mem_def.mp hp).symm
      subst p
      exact (show i-left ≤ replacement.length by omega).trans hr
    · exact letters_getD hn _

private theorem install_length (pad : Fin q) (p : Prepared q) (h : prepared M N p) :
    (install pad p.entry p.left p.removed p.negative p.replacement).length ≤ 5*N := by
  have hl := h.2.2.1
  have hr := h.2.2.2.2.2.1
  have hn := h.2.2.2.2.2.2.2.2.1
  simp only [install,List.length_map,List.length_range]
  omega

def validStores (M N : ℕ) (es : List (SourceDictionary.Stored q)) : Prop :=
  ∀ e ∈ es, e.2.1.length ≤ 5*N ∧ letters M e.2.1 ∧ e.2.2.length ≤ 5*N ∧ letters M e.2.2

private theorem completed_bound (pad : Fin q) {cfg : Config q} {hs : History q} {i : ℕ}
    (hNM : N ≤ M) (hh : boundedHistory cfg M N i hs) : validStores M N (completed pad hs) := by
  intro e he
  obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have h := (hh.2 _ hb).2.2 _ hp
  have hneg := h.2.2.2.2.2.2.2.2
  exact ⟨by dsimp [SourcePrepare.completed]; omega,hneg.2,install_length pad p h,
    install_bound pad hneg.2 h.2.1 (h.2.2.2.2.2.1.trans hNM)⟩

private theorem completed_length_le (pad : Fin q) {cfg : Config q} {hs : History q} {i : ℕ}
    (hh : boundedHistory cfg M N i hs) : (completed pad hs).length ≤ i*cfg.arity := by
  have h : (completed pad hs).length = hs.length*cfg.arity := by
    unfold completed
    rw [List.length_flatMap]
    simp only [List.length_map]
    have hbatch := hh.2
    clear hh
    induction hs with
    | nil => simp
    | cons b bs ih =>
      rw [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,
        (hbatch b (by simp)).2.1,ih (fun b hb => hbatch b (List.mem_cons_of_mem _ hb)),Nat.add_comm]
  rw [h]
  exact Nat.mul_le_mul_right _ hh.1

private theorem starts_bound {len L i : ℕ} (h : i ∈ SourceDictionary.starts len L) : i+L ≤ len := by
  simpa using (List.mem_filter.mp h).2

private theorem occurrences_bound {es : List (SourceDictionary.Stored q)} {l L : ℕ}
    (he : validStores M N es) (hl : l ≤ M) (hL : L ≤ N)
    (hN : 5*N ≤ M) (hcount : es.length ≤ M) :
    ∀ o ∈ SourceDictionary.occurrences l L es, occurrence M N o := by
  intro o ho
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ho
    have hb := (starts_bound hj).trans hl
    exact ⟨by dsimp; omega,by simp,by simpa [original] using hL,original_bound hb⟩
  · obtain ⟨j,hj,ho⟩ := List.mem_flatMap.mp ho
    have hj' := List.mem_range.mp hj
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] at ho
    have hz := he (es[j]'hj') (List.getElem_mem _)
    have supplier {w : LiftData q} {side : Bool} (hw : w.length ≤ 5*N) (hwl : letters M w)
        (ho : o ∈ SourceDictionary.suppliers j side L w) : occurrence M N o := by
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ho
      have hb := (starts_bound hk).trans (hw.trans hN)
      refine ⟨(Nat.le_of_lt hj').trans hcount, ?_, ?_,window_bound hwl _ _⟩
      · intro p hp
        have h : p = (side,k) := Option.some.inj (Option.mem_def.mp hp).symm
        subst p
        dsimp
        omega
      · exact (List.length_take_le _ _).trans hL
    rcases List.mem_append.mp ho with hh | hh
    · exact supplier hz.1 hz.2.1 hh
    · exact supplier hz.2.2.1 hz.2.2.2 hh

theorem mapM_some {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    simp at h
    subst ys
    simp
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx,bind,Option.bind] at h
    | some v =>
      cases ht : xs.mapM f with
      | none => simp [hx,ht,bind,Option.bind] at h
      | some w =>
        have heq : v::w = ys := by simpa [hx,ht,bind,Option.bind,pure] using h
        subst ys
        obtain ⟨hlen,hm⟩ := ih ht
        refine ⟨by simp [hlen], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x,by simp,hx⟩
        · obtain ⟨a,ha,hf⟩ := hm _ hy
          exact ⟨a,by simp [ha],hf⟩

private theorem selectedStarts_bound (L n : ℕ) :
    (ReplayEntry.selectedStarts L n).length ≤ 3 := by
  dsimp [ReplayEntry.selectedStarts]
  split <;> simp_all
  split <;> simp_all

private theorem select_bound (pad : Fin q) {l L : ℕ} {x w : QWord q} {es : List (SourceDictionary.Stored q)}
    {os : List (OccurrenceData q)} (h : SourceDictionary.select pad l L x es w = some os)
    (hb : ∀ o ∈ SourceDictionary.occurrences l L es, occurrence M N o) :
    os.length ≤ 3 ∧ ∀ o ∈ os, occurrence M N o := by
  unfold SourceDictionary.select at h
  obtain ⟨hlen,hm⟩ := mapM_some h
  refine ⟨hlen.le.trans (selectedStarts_bound _ _),?_⟩
  intro o ho
  obtain ⟨a,_,ha⟩ := hm _ ho
  exact hb _ (List.mem_of_find?_eq_some ha)

theorem read_bound {cfg : SourceNegative.ReadConfig} {es : List (SourceDictionary.Stored q)}
    {w : LiftData q} {loc : SourceDictionary.LocationData}
    (he : validStores M N es) (hl : cfg.1.1 ≤ M)
    (h : SourceNegative.readLocation cfg es loc = some w) : letters M w := by
  rcases cfg with ⟨⟨l,L⟩,current,rule⟩
  rcases loc with ⟨j,side⟩
  cases side with
  | none =>
    simp only [SourceNegative.readLocation,Option.elim_none] at h
    split at h
    · rename_i hs
      injection h with hw
      subst w
      exact original_bound (hs.trans hl)
    · contradiction
  | some p =>
    simp only [SourceNegative.readLocation,Option.elim_some] at h
    split at h
    · cases heq : es[j]? with
      | none => simp [heq,bind,Option.bind] at h
      | some e =>
        have hb := he e (List.mem_of_getElem? heq)
        simp only [heq,bind,Option.bind] at h
        split at h
        · injection h with hw
          subst w
          cases p.1 <;> simp [SourceDictionary.onSide,window_bound hb.2.1,window_bound hb.2.2.2]
        · contradiction
    · contradiction

theorem assemble_bound {n : ℕ} {starts : List ℕ} {ws : List (LiftData q)}
    {w : LiftData q} (hws : ∀ v ∈ ws, letters M v)
    (h : SourceNegative.assembleSelected n starts ws = some w) :
    w.length = n ∧ letters M w := by
  have hw (i : ℕ) : letters M (ws.getD i []) := by
    by_cases hi : i < ws.length
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      exact hws _ (List.getElem_mem _)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt hi),letters]
  have finish {v : LiftData q} (hv : letters M v) (he : SourceNegative.finish n v = some w) :
      w.length = n ∧ letters M w := by
    unfold SourceNegative.finish at he
    split at he
    · injection he with heq
      subst w
      exact ⟨by assumption,hv⟩
    · contradiction
  dsimp only [SourceNegative.assembleSelected] at h
  split at h
  · split at h
    · exact finish (hw 0) h
    · cases hjoin : SourceLetters.appendWindow (ws.getD 0 []) (starts.getD 1 0) (ws.getD 1 []) with
      | none =>
        split at h
        · rw [hjoin] at h
          contradiction
        · split at h
          · rw [hjoin] at h
            contradiction
          · contradiction
      | some u =>
        have hu := append_bound (hw 0) (hw 1) hjoin
        simp only [hjoin,Option.bind_some] at h
        split at h
        · exact finish hu h
        · split at h
          · cases hj : SourceLetters.appendWindow u (starts.getD 2 0) (ws.getD 2 []) with
            | none => rw [hj] at h; contradiction
            | some _ =>
              simp only [hj,Option.bind_some] at h
              exact finish (append_bound hu (hw 2) hj) h
          · contradiction
  · contradiction

private theorem negative_bound {cfg : SourceNegative.ReadConfig} {es : List (SourceDictionary.Stored q)}
    {n : ℕ} {locs : List SourceDictionary.LocationData} {w : LiftData q}
    (he : validStores M N es) (hl : cfg.1.1 ≤ M)
    (h : SourceNegative.negativeFrom cfg es n locs = some w) :
    w.length = n ∧ letters M w := by
  dsimp only [SourceNegative.negativeFrom,SourceNegative.negativeWith] at h
  split at h
  · cases hm : locs.mapM (SourceNegative.readLocation cfg es) with
    | none => simp [hm] at h
    | some ws =>
      simp only [hm,Option.bind_some] at h
      refine assemble_bound (fun v hv => ?_) h
      obtain ⟨j,_,hj⟩ := (mapM_some hm).2 _ hv
      exact read_bound he hl hj
  · contradiction

private theorem prepareBubble_bound (pad : Fin q) {cfg : SourceNegative.ReadConfig}
    {x : QWord q} {es : List (SourceDictionary.Stored q)} {b : BubbleData q} {p : Prepared q}
    (he : validStores M N es) (hl : cfg.1.1 ≤ M) (hL : cfg.1.2 ≤ N)
    (hN : 5*N ≤ M) (hcount : es.length ≤ M) (hj : cfg.2.1 ≤ M) (hr : cfg.2.2 ≤ M)
    (hb : b.1.1.length ≤ N ∧ b.1.2.length ≤ N ∧ b.2.1.length ≤ N ∧ b.2.2.length ≤ N)
    (h : SourcePrepare.prepareBubble pad cfg x es b = some p) : prepared M N p := by
  unfold SourcePrepare.prepareBubble SourceNegative.prepareNegative at h
  let w := OrderedCatalogue.side b false
  change ((SourceDictionary.select pad cfg.1.1 cfg.1.2 x es w).bind (fun os =>
    (SourceNegative.negativeFrom cfg es w.length (os.map Prod.fst)).map (fun v => (os,v)))).bind
    (SourcePrepare.prepareFrom cfg b.1.1.length b.2.1.length b.1.2.length b.2.2) = some p at h
  cases hs : SourceDictionary.select pad cfg.1.1 cfg.1.2 x es w with
  | none => simp [hs] at h
  | some os =>
    have hos := select_bound pad hs (occurrences_bound he hl hL hN hcount)
    cases hv : SourceNegative.negativeFrom cfg es w.length (os.map Prod.fst) with
    | none => simp [hs,hv] at h
    | some v =>
      have hneg := negative_bound he hl hv
      simp only [hs,Option.bind_some,hv,Option.map_some,SourcePrepare.prepareFrom] at h
      split at h
      · contradiction
      · injection h with heq
        subst p
        have hw : w.length ≤ 3*N := by
          unfold w OrderedCatalogue.side
          simp only [Bool.false_eq_true,↓reduceIte,List.length_append]
          omega
        exact ⟨hr,hj,hb.1,hb.2.2.1,hb.2.1,hb.2.2.2,hos.1,hos.2,hneg.1.le.trans hw,hneg.2⟩

private def inputSize (cfg : Config q) : ℕ := (configEncoding q cfg).length

private def coordinateBound (n : ℕ) : ℕ := (n+2)^2 + 5*n

private def invariant (cfg : Config q) (i : ℕ) (st : State q) : Prop :=
  ∀ out ∈ st.2, (∀ j ∈ out.1, j ≤ inputSize cfg+1) ∧
    boundedHistory cfg (coordinateBound (inputSize cfg)) (inputSize cfg) i out.2

private theorem width_le (cfg : Config q) : cfg.width ≤ inputSize cfg := by
  simpa [encUnary_apply,inputSize] using configEncoding_width_length_le q cfg

private theorem arity_le (cfg : Config q) : cfg.arity ≤ inputSize cfg := by
  simpa [encUnary_apply,inputSize] using configEncoding_arity_length_le q cfg

private theorem length_le (cfg : Config q) : cfg.length ≤ inputSize cfg := by
  simpa [encUnary_apply,inputSize] using configEncoding_length_length_le q cfg

private theorem gram_le (cfg : Config q) : cfg.gram ≤ inputSize cfg := by
  simpa [encUnary_apply,inputSize] using configEncoding_gram_length_le q cfg

private theorem list_length_le {α : Type} (e : α ↪ List Bool) (xs : List α) :
    xs.length ≤ (encList e xs).length := SizedListEncoding.length_le (encA := e) (encL := encList e) xs

private theorem row_size_le {cfg : Config q} {r : RuleRow q} (hr : r ∈ cfg.catalogue) :
    (SourceRuleRows.rowEncoding q r).length ≤ inputSize cfg :=
  (SizedListEncoding.length_elem_le cfg.catalogue r hr).trans (configEncoding_catalogue_length_le q cfg)

private theorem bubbles_size_le {cfg : Config q} {r : RuleRow q} (hr : r ∈ cfg.catalogue) :
    (OrderedCatalogue.ruleEncoding q r.2).length ≤ inputSize cfg := by
  refine Nat.le_trans ?_ (row_size_le hr)
  rw [SourceRuleRows.rowEncoding,length_encPair]
  omega

private theorem bubbleLengths_le {cfg : Config q} {r : RuleRow q} {b : BubbleData q}
    (hr : r ∈ cfg.catalogue) (hb : b ∈ r.2) :
    b.1.1.length ≤ inputSize cfg ∧ b.1.2.length ≤ inputSize cfg ∧
    b.2.1.length ≤ inputSize cfg ∧ b.2.2.length ≤ inputSize cfg := by
  have h : (OrderedCatalogue.bubbleEncoding q b).length ≤ inputSize cfg :=
    (SizedListEncoding.length_elem_le r.2 b hb).trans (bubbles_size_le hr)
  simp only [OrderedCatalogue.bubbleEncoding,OrderedCatalogue.wordPairEncoding,length_encPair] at h
  have h₁ : b.1.1.length ≤ (wordEncoding q b.1.1).length :=
    list_length_le (ExceptionalRecords.letterEncoding q) b.1.1
  have h₂ : b.1.2.length ≤ (wordEncoding q b.1.2).length :=
    list_length_le (ExceptionalRecords.letterEncoding q) b.1.2
  have h₃ : b.2.1.length ≤ (wordEncoding q b.2.1).length :=
    list_length_le (ExceptionalRecords.letterEncoding q) b.2.1
  have h₄ : b.2.2.length ≤ (wordEncoding q b.2.2).length :=
    list_length_le (ExceptionalRecords.letterEncoding q) b.2.2
  exact ⟨by omega,by omega,by omega,by omega⟩

private theorem prep_preserves (pad : Fin q) {cfg : Config q} {hs out : History q}
    {r : RuleRow q} {i : ℕ} (hi : i ≤ cfg.width) (hr : r ∈ cfg.catalogue)
    (hh : boundedHistory cfg (coordinateBound (inputSize cfg)) (inputSize cfg) i hs)
    (h : prep cfg pad hs r = some out) :
    out.length = hs.length+1 ∧
    boundedHistory cfg (coordinateBound (inputSize cfg)) (inputSize cfg) (i+1) out := by
  let N := inputSize cfg
  let M := coordinateBound N
  have hw := width_le cfg
  have ha := arity_le cfg
  have hNM : N ≤ M := by unfold M coordinateBound; omega
  have h5NM : 5*N ≤ M := by unfold M coordinateBound; omega
  have hlen : r.2.length ≤ N :=
    (list_length_le _ _).trans (bubbles_size_le hr)
  have he := completed_bound pad hNM hh
  have he' := completed_length_le pad hh
  have hidx {j : ℕ} (hj : j < r.2.length) : (completed pad hs).length+j ≤ M := by
    have hib : i ≤ N := hi.trans hw
    have hp : i*cfg.arity ≤ N*N := Nat.mul_le_mul hib ha
    have hM : N*N+N ≤ M := by
      unfold M coordinateBound
      nlinarith
    exact (Nat.add_le_add (he'.trans hp) (hj.le.trans hlen)).trans hM
  have hcount : (completed pad hs).length ≤ M := by
    have hp : i*cfg.arity ≤ N*N := Nat.mul_le_mul (hi.trans hw) ha
    have hl : N*N ≤ M := by unfold M coordinateBound; nlinarith
    exact he'.trans (hp.trans hl)
  unfold prep at h
  split at h
  · cases hp : SourcePrepare.prepareRule pad cfg.length cfg.gram hs.length cfg.word (completed pad hs) r.2 with
    | none => rw [hp] at h; contradiction
    | some ps =>
      simp only [hp,Option.bind_some] at h
      split at h
      · rename_i hps
        injection h with hout
        subst out
        refine ⟨by simp, ?_⟩
        refine ⟨by simpa using Nat.succ_le_succ hh.1, ?_⟩
        intro z hz
        rcases List.mem_append.mp hz with hn | hn
        · exact hh.2 _ hn
        · have hz' : z = (r.1,ps) := by simpa using hn
          subst z
          refine ⟨?_,hps,?_⟩
          · have hs := row_size_le hr
            simp only [SourceRuleRows.rowEncoding,length_encPair] at hs
            exact (show (Ternary.rowEncoding r.1).length ≤ 2*(Ternary.rowEncoding r.1).length+1+
                (OrderedCatalogue.ruleEncoding q r.2).length by omega).trans hs
          intro p hp'
          unfold SourcePrepare.prepareRule at hp
          obtain ⟨j,hj,hj'⟩ := (mapM_some hp).2 _ hp'
          have hj'' := List.mem_range.mp hj
          rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj'',Option.getD_some] at hj'
          exact prepareBubble_bound pad he ((length_le cfg).trans hNM) (gram_le cfg) h5NM hcount
            (hidx hj'') (hh.1.trans (hi.trans (hw.trans hNM)))
            (bubbleLengths_le hr (List.getElem_mem _)) hj'
      · contradiction
  · contradiction

private theorem invariant_step (pad : Fin q) (cfg : Config q) (i : ℕ) (st : State q)
    (hi : i < cfg.width+1) (h : invariant cfg i st) :
    invariant cfg (i+1) (SourceRecognition.step pad cfg st) := by
  have hnext : invariant cfg (i+1) st := by
    intro out hout
    obtain ⟨he,hh,hb⟩ := h out hout
    exact ⟨he,hh.trans (Nat.le_succ _),hb⟩
  unfold SourceRecognition.step
  split
  · cases he : st.2 with
    | none => simp [he,invariant,failed]
    | some out =>
      simp only [he,Option.elim_some]
      obtain ⟨hEvent,hh⟩ := h out (by simp [he])
      unfold SourceRecognition.scan
      cases hn : next pad cfg out.2 with
      | none =>
        intro v hv
        have hv' : (none,out.2) = v := by simpa [hn,Option.mem_def] using hv
        subst v
        exact ⟨by simp,hh.1.trans (Nat.le_succ _),hh.2⟩
      | some w =>
        simp only [hn,Option.elim_some,tryRule]
        cases hp : prep cfg pad out.2 w with
        | none => simp [hp,invariant,failed]
        | some hs =>
          have hw : w ∈ cfg.catalogue := List.mem_of_find?_eq_some hn
          obtain ⟨hlen,hb⟩ := prep_preserves pad (by omega) hw hh hp
          simp only [hp,Option.elim_some,advance,hlen,Nat.lt_succ_self,↓reduceIte]
          split
          · intro v hv
            have hv' : (some out.2.length,hs) = v := by simpa [Option.mem_def] using hv
            subst v
            refine ⟨?_,hb⟩
            intro j hj
            have heq : out.2.length = j := Option.some.inj (Option.mem_def.mp hj)
            rw [← heq]
            exact hh.1.trans ((show i ≤ cfg.width by omega).trans ((width_le cfg).trans (Nat.le_succ _)))
          · intro v hv
            have hv' : (none,hs) = v := by simpa [Option.mem_def] using hv
            subst v
            exact ⟨by simp,hb⟩
  · exact hnext

def liftBits (q M N : ℕ) : ℕ := N*(2*(4*M+q+4)+1)

private def occurrenceBits (q M N : ℕ) : ℕ := 6*M+12+liftBits q M N

private def preparedBits (q M N : ℕ) : ℕ :=
  4*M+6*N+7+2*(N*(2*q+1))+2*(3*(2*occurrenceBits q M N+1))+liftBits q M (3*N)

private def batchBits (q M N : ℕ) : ℕ := 2*N+1+N*(2*preparedBits q M N+1)

private def stateBits (q N : ℕ) : ℕ :=
  2*(N+1)+7+(N+1)*(2*batchBits q (coordinateBound N) N+1)

private theorem symbol_size_le (a : Fin q) :
    (ExceptionalRecords.letterEncoding q a).length ≤ q := by
  change (encUnary a.val).length ≤ q
  simpa [encUnary_apply] using a.isLt.le

private theorem letter_size_le (a : LetterData q) (h : letter M a) :
    (SourceLetters.letterEncoding q a).length ≤ 4*M+q+4 := by
  rcases a with ⟨i,o⟩
  have hi := h.1
  cases o with
  | none =>
    simp only [SourceLetters.letterEncoding,length_encPair,encOption_none,encUnary_apply,
      List.length_replicate,List.length_nil]
    omega
  | some a =>
    have hj := h.2 a (by simp)
    have ha := symbol_size_le a.2
    simp only [SourceLetters.letterEncoding,SourceLetters.freshEncoding,length_encPair,
      encOption_some,encUnary_apply,List.length_replicate,List.length_cons]
    dsimp at hi hj
    omega

theorem lift_size_le {w : LiftData q} (hl : w.length ≤ N) (h : letters M w) :
    (SourceLetters.liftEncoding q w).length ≤ liftBits q M N :=
  (length_encList_le _ _ (fun _ ha => letter_size_le _ (h _ ha))).trans (Nat.mul_le_mul_right _ hl)

private theorem occurrence_size_le (o : OccurrenceData q) (h : occurrence M N o) :
    (SourceDictionary.occurrenceEncoding q o).length ≤ occurrenceBits q M N := by
  rcases o with ⟨⟨i,r⟩,w⟩
  have hw := lift_size_le h.2.2.1 h.2.2.2
  have hi := h.1
  cases r with
  | none =>
    simp only [SourceDictionary.occurrenceEncoding,SourceDictionary.locationEncoding,
      length_encPair,encOption_none,encUnary_apply,List.length_replicate,List.length_nil,
      occurrenceBits]
    dsimp at hi hw
    omega
  | some a =>
    have ha := h.2.1 a (by simp)
    simp only [SourceDictionary.occurrenceEncoding,SourceDictionary.locationEncoding,
      length_encPair,encOption_some,encUnary_apply,encBool_apply,List.length_replicate,
      List.length_cons,List.length_nil,occurrenceBits]
    dsimp at hi hw
    omega

private theorem prepared_size_le (p : Prepared q) (h : prepared M N p) :
    (SourcePrepare.preparedEncoding q p).length ≤ preparedBits q M N := by
  rcases h with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀⟩
  have hrep : (wordEncoding q p.replacement).length ≤ N*(2*q+1) :=
    (length_encList_le _ _ (fun a _ => symbol_size_le a)).trans (Nat.mul_le_mul_right _ h₆)
  have hwin : (SourceDictionary.occurrencesEncoding q p.windows).length ≤ 3*(2*occurrenceBits q M N+1) :=
    (length_encList_le _ _ (fun o ho => occurrence_size_le o (h₈ _ ho))).trans (Nat.mul_le_mul_right _ h₇)
  have hneg := lift_size_le h₉ h₁₀
  simp only [SourcePrepare.preparedEncoding_apply,SourcePrepare.preparedEncodingFields,
    length_encPair,encUnary_apply,List.length_replicate,preparedBits]
  omega

private theorem batch_size_le {cfg : Config q} {b : Batch q}
    (hrow : (Ternary.rowEncoding b.1).length ≤ N) (hlen : b.2.length = cfg.arity)
    (ha : cfg.arity ≤ N) (h : ∀ p ∈ b.2, prepared M N p) :
    (batchEncoding q b).length ≤ batchBits q M N := by
  have hb : (SourcePrepare.preparedListEncoding q b.2).length ≤ N*(2*preparedBits q M N+1) :=
    (length_encList_le _ _ (fun p hp => prepared_size_le p (h _ hp))).trans
      (Nat.mul_le_mul_right _ (hlen.le.trans ha))
  simp only [batchEncoding,length_encPair,batchBits]
  omega

private theorem state_size_le (cfg : Config q) (i : ℕ) (st : State q)
    (hi : i ≤ cfg.width+1) (h : invariant cfg i st) :
    (stateEncoding q st).length ≤ stateBits q (inputSize cfg) := by
  rcases st with ⟨active,out⟩
  let N := inputSize cfg
  let M := coordinateBound N
  cases out with
  | none =>
    simp only [stateEncoding,length_encPair,encBool_apply,List.length_cons,List.length_nil,
      encOption_none,stateBits]
    omega
  | some v =>
    obtain ⟨he,hh,hb⟩ := h v (by simp)
    have hlen : v.2.length ≤ N+1 := hh.trans (hi.trans (Nat.succ_le_succ (width_le cfg)))
    have hs : (historyEncoding q v.2).length ≤ (N+1)*(2*batchBits q M N+1) :=
      (length_encList_le _ _ (fun b hmem =>
        let h := hb b hmem
        batch_size_le h.1 h.2.1 (arity_le cfg) h.2.2)).trans (Nat.mul_le_mul_right _ hlen)
    have hj : (encOption encUnary v.1).length ≤ N+2 := by
      cases h : v.1 with
      | none => simp
      | some j =>
        have h' := he j (by simp [h])
        simp only [h,encOption_some,encUnary_apply,List.length_cons,List.length_replicate]
        omega
    simp only [stateEncoding,resultEncoding,length_encPair,encBool_apply,List.length_cons,
      List.length_nil,encOption_some,stateBits]
    change _ ≤ 2*(N+1)+7+(N+1)*(2*batchBits q M N+1)
    omega

private theorem stateBits_polyBounded (q : ℕ) :
    PolyBounded (fun cfg : Config q => (configEncoding q cfg).length)
      (fun cfg => stateBits q (inputSize cfg)) := by
  have n : PolyBounded (fun cfg : Config q => (configEncoding q cfg).length) (inputSize (q := q)) :=
    PolyBounded.self
  have c (v : ℕ) : PolyBounded (fun cfg : Config q => (configEncoding q cfg).length) (fun _ => v) :=
    PolyBounded.const v
  have m := ((n.add (c 2)).pow 2).add ((c 5).mul n)
  have hl (a : ℕ) := ((c a).mul n).mul ((c 2).mul (((c 4).mul m).add (c q) |>.add (c 4)) |>.add (c 1))
  have ho := ((c 6).mul m).add (c 12) |>.add (hl 1)
  have hp := ((c 4).mul m).add ((c 6).mul n) |>.add (c 7) |>.add
    ((c 2).mul (n.mul (c (2*q+1)))) |>.add
    ((c 2).mul ((c 3).mul (((c 2).mul ho).add (c 1)))) |>.add (hl 3)
  have hb := ((c 2).mul n).add (c 1) |>.add (n.mul (((c 2).mul hp).add (c 1)))
  have hs := ((c 2).mul (n.add (c 1))).add (c 7) |>.add ((n.add (c 1)).mul (((c 2).mul hb).add (c 1)))
  simpa [stateBits,batchBits,preparedBits,occurrenceBits,liftBits,coordinateBound] using hs

theorem recognizeWith_polyTime (pad : Fin q) :
    ComputableInPolyTime (recognizeWith pad) (configEncoding q) (encOption (resultEncoding q)) := by
  let e := configEncoding q
  let s := stateEncoding q
  let r := resultEncoding q
  have hw := configEncoding_width_polyTime q (id' (encIn := e))
  have hn := unary_add' hw (const 1)
  have hs : ComputableInPolyTime (fun cfg : Config q =>
      (SourceRecognition.step pad cfg)^[cfg.width+1] (true,some (none,[]))) e s :=
    (iterateWith_spec (step := SourceRecognition.step pad) id' hn (const (true,some (none,[])))
      (step_polyTime pad) invariant
      (fun _ => by simp [invariant,boundedHistory]) (invariant_step pad)
      (stateBits_polyBounded q) state_size_le).1
  have hresult := ((fst encBool (encOption r)).ite' (const none) (snd encBool (encOption r))).comp hs
  have hl := configEncoding_length_polyTime q (id' (encIn := e))
  exact ((unary_lt' (const 0) hl).ite' hresult (const (some (none,[])))).of_enc_eq
    (fun _ => by simp [recognizeWith,run,r] <;> rfl)

theorem recognize_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) :
    ComputableInPolyTime (recognize pad b t) (uniformEncoding q) (encOption (resultEncoding q)) :=
  (recognizeWith_polyTime pad).comp (uniform_polyTime pad b t hq)

theorem outputBounds (pad : Fin q) (cfg : Config q) {out : Result q}
    (h : recognizeWith pad cfg = some out) :
    boundedHistory cfg (coordinateBound (inputSize cfg)) (inputSize cfg) (cfg.width+1) out.2 := by
  have hloop (i : ℕ) (hi : i ≤ cfg.width+1) :
      invariant cfg i ((SourceRecognition.step pad cfg)^[i] (true,some (none,[]))) := by
    induction i with
    | zero => simp [invariant,boundedHistory]
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact invariant_step pad cfg i _ (by omega) (ih (by omega))
  unfold recognizeWith at h
  split at h
  · dsimp only [run] at h
    split at h
    · contradiction
    · exact (hloop _ le_rfl out (Option.mem_def.mpr h)).2
  · injection h with he
    subst out
    simp [boundedHistory]

#print axioms outputBounds
#print axioms recognizeWith_polyTime
#print axioms recognize_polyTime

end DeletionCode.Explicit.Machine.SourceRunBounds
