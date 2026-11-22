import DeletionCode.Explicit.LocalBudget

/-! Preservation of an unmarked original letter by a gate bypass (`d:dag`). -/

namespace DeletionCode.Explicit.LetterGraphCuts

variable {V : Type*} {E : V → V → Prop} {z : V}

/-- Directed edges along the replacement of the segment from `left` to
`right`; only its interior changes. -/
def segmentEdges (left : V) (interior : List V) (right : V) : List (V × V) :=
  (left :: interior).zip (interior ++ [right])

def addGate (E : V → V → Prop) (left : V) (fresh : List V) (right : V) : V → V → Prop :=
  fun a b => E a b ∨ (a,b) ∈ segmentEdges left fresh right

/-- Indices of the two ends of an edge in a gate segment. -/
theorem mem_segmentEdges_iff {left right a b : V} {mid : List V} :
    (a,b) ∈ segmentEdges left mid right ↔
      ∃ (i : ℕ) (hi : i < mid.length+1),
        (left :: mid)[i]'(by simpa using hi) = a ∧
          (mid ++ [right])[i]'(by simpa using hi) = b := by
  have hlen : (segmentEdges left mid right).length = mid.length+1 := by
    simp [segmentEdges,List.length_zip]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i,hi,he⟩
    have hb : i < mid.length+1 := hlen ▸ hi
    change ((left :: mid).zip (mid ++ [right]))[i]'hi = (a,b) at he
    have hpair := List.getElem_zip.symm.trans he
    exact ⟨i,hb,congrArg Prod.fst hpair,congrArg Prod.snd hpair⟩
  · rintro ⟨i,hi,ha,hb⟩
    have hh : i < (segmentEdges left mid right).length := hlen.symm ▸ hi
    refine ⟨i,hh,?_⟩
    have hz : i < ((left :: mid).zip (mid ++ [right])).length := hh
    exact (List.getElem_zip (h := hz)).trans (Prod.ext ha hb)

theorem segment_reaches {left right : V} {mid : List V}
    (hpath : ∀ a b, (a,b) ∈ segmentEdges left mid right → E a b) :
    Relation.TransGen E left right := by
  induction mid generalizing left with
  | nil => exact .single (hpath _ _ (by simp [segmentEdges]))
  | cons v tail ih =>
    have he := hpath left v (by simp [segmentEdges])
    exact (Relation.TransGen.single he).trans
      (ih (fun a b h => hpath a b (List.mem_cons_of_mem _ h)))

private theorem rank_reaches (rank : V → ℕ)
    (hrank : ∀ {a b}, E a b → rank a < rank b) {a b : V}
    (h : Relation.TransGen E a b) : rank a < rank b := by
  induction h with
  | single he => exact hrank he
  | tail _ he ih => exact ih.trans (hrank he)

/-- Extend a strictly increasing graph rank across a gate. Between each
pair of old ranks leave enough slots for the entire inserted segment. -/
theorem rank_addGate [DecidableEq V] (rank : V → ℕ)
    (hrank : ∀ {a b}, E a b → rank a < rank b) (left right : V) (removed fresh : List V)
    (hpath : ∀ a b, (a,b) ∈ segmentEdges left removed right → E a b)
    (hl : left ∉ fresh) (hr : right ∉ fresh) (hd : fresh.Nodup)
    (hnew : ∀ {a b}, E a b → a ∉ fresh ∧ b ∉ fresh) :
    ∃ next : V → ℕ, ∀ {a b}, addGate E left fresh right a b → next a < next b := by
  let gap := fresh.length+1
  let next (v : V) := if v ∈ fresh then rank left*gap + fresh.idxOf v+1 else rank v*gap
  have hgap : 0 < gap := Nat.succ_pos _
  have hleft : next left = rank left*gap := by simp [next,hl]
  have hright : next right = rank right*gap := by simp [next,hr]
  have hfresh (i : ℕ) (hi : i < fresh.length) :
      next fresh[i] = rank left*gap + i+1 := by
    simp [next,List.getElem_mem hi,hd.idxOf_getElem i hi]
  have hroom : rank left*gap + gap ≤ rank right*gap := by
    have hlt := rank_reaches rank hrank (segment_reaches hpath)
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right gap (Nat.succ_le_of_lt hlt)
  refine ⟨next,?_⟩
  intro a b hab
  rcases hab with he | he
  · simpa [next,(hnew he).1,(hnew he).2] using Nat.mul_lt_mul_of_pos_right (hrank he) hgap
  · obtain ⟨i,hi,ha,hb⟩ := mem_segmentEdges_iff.mp he
    have ha' : next a = rank left*gap + i := by
      cases i with
      | zero => simpa using (congrArg next ha).symm.trans hleft
      | succ i =>
        have hh : i < fresh.length := by omega
        rw [List.getElem_cons_succ] at ha
        exact (congrArg next ha).symm.trans (hfresh i hh)
    rw [ha']
    by_cases hh : i < fresh.length
    · rw [List.getElem_append_left hh] at hb
      rw [← hb,hfresh i hh]
      omega
    · have hh' : fresh.length = i := by omega
      have hbr : b = right := by
        rw [List.getElem_append_right hh'.le] at hb
        simpa [← hh'] using hb.symm
      rw [hbr,hright]
      exact lt_of_lt_of_le (Nat.add_lt_add_left hi _) hroom

/-- Every path leaving the vertices before an unmarked letter must visit it
at the first exiting edge. Every edge also preserves the side order. -/
structure EdgeCut (E : V → V → Prop) (z : V) where
  before : V → Bool
  at_cut : before z = false
  order : ∀ {a b}, E a b → before b = true → before a = true
  exit : ∀ {a b}, E a b → before a = true → before b = false → b = z

private theorem EdgeCut.segment_order (C : EdgeCut E z) {left right : V} {mid : List V}
    (hpath : ∀ a b, (a,b) ∈ segmentEdges left mid right → E a b)
    (hr : C.before right = true) : C.before left = true := by
  induction mid generalizing left with
  | nil => exact C.order (hpath _ _ (by simp [segmentEdges])) hr
  | cons v tail ih =>
    apply C.order (hpath left v (by simp [segmentEdges]))
    apply ih (left := v)
    intro a b hab
    exact hpath a b (List.mem_cons_of_mem _ hab)

private theorem EdgeCut.segment_exit (C : EdgeCut E z) {left right : V} {mid : List V}
    (hpath : ∀ a b, (a,b) ∈ segmentEdges left mid right → E a b)
    (hkeep : z ∉ mid) (hl : C.before left = true) (hr : C.before right = false) :
    right = z := by
  induction mid generalizing left with
  | nil => exact C.exit (hpath _ _ (by simp [segmentEdges])) hl hr
  | cons v tail ih =>
    cases hv : C.before v with
    | true =>
      apply ih (left := v) _ (fun h => hkeep (List.mem_cons_of_mem _ h)) hv
      intro a b hab
      exact hpath a b (List.mem_cons_of_mem _ hab)
    | false =>
      have he := C.exit (hpath left v (by simp [segmentEdges])) hl hv
      subst v
      exact (hkeep (List.mem_cons_self ..)).elim

/-- Extend a cut across a new gate whose removed segment leaves the cut's
original position unmarked. The new interior letters lie on the same side
as the left endpoint. This holds for insertion, deletion, and replacement. -/
def EdgeCut.extend [DecidableEq V] (C : EdgeCut E z) (left right : V) (removed fresh : List V)
    (hpath : ∀ a b, (a,b) ∈ segmentEdges left removed right → E a b)
    (hkeep : z ∉ removed) (hz : z ∉ fresh) (hl : left ∉ fresh) (hr : right ∉ fresh)
    (hnew : ∀ {a b}, E a b → a ∉ fresh ∧ b ∉ fresh) :
    EdgeCut (addGate E left fresh right) z := by
  let before (v : V) : Bool := if v ∈ fresh then C.before left else C.before v
  have known (v : V) (h : v ∉ fresh) : before v = C.before v := by simp [before,h]
  have added (v : V) (h : v ∈ fresh) : before v = C.before left := by simp [before,h]
  have from_left {a b : V} (h : (a,b) ∈ segmentEdges left fresh right) :
      before a = C.before left := by
    rcases List.mem_cons.mp ((List.of_mem_zip h).1) with he | hf
    · subst a
      exact known left hl
    · exact added a hf
  have to_right {a b : V} (h : (a,b) ∈ segmentEdges left fresh right) :
      b ∈ fresh ∨ b = right := by
    simpa using (List.of_mem_zip h).2
  refine ⟨before,(known z hz).trans C.at_cut,?_,?_⟩
  · intro a b hab hb
    rcases hab with he | hg
    · rw [known b (hnew he).2] at hb
      exact (known a (hnew he).1).trans (C.order he hb)
    · rw [from_left hg]
      rcases to_right hg with hf | he
      · exact (added b hf).symm.trans hb
      · subst b
        rw [known right hr] at hb
        exact C.segment_order hpath hb
  · intro a b hab ha hb
    rcases hab with he | hg
    · rw [known a (hnew he).1] at ha
      rw [known b (hnew he).2] at hb
      exact C.exit he ha hb
    · rw [from_left hg] at ha
      rcases to_right hg with hf | he
      · rw [added b hf,ha] at hb
        contradiction
      · subst b
        rw [known right hr] at hb
        exact C.segment_exit hpath hkeep ha hb

theorem EdgeCut.extend_before_of_old [DecidableEq V] (C : EdgeCut E z)
    (left right : V) (removed fresh : List V)
    (hpath : ∀ a b, (a,b) ∈ segmentEdges left removed right → E a b)
    (hkeep : z ∉ removed) (hz : z ∉ fresh) (hl : left ∉ fresh) (hr : right ∉ fresh)
    (hnew : ∀ {a b}, E a b → a ∉ fresh ∧ b ∉ fresh) (v : V) (hv : v ∉ fresh) :
    (C.extend left right removed fresh hpath hkeep hz hl hr hnew).before v = C.before v := by
  simp [EdgeCut.extend,hv]

#print axioms EdgeCut.extend_before_of_old

theorem EdgeCut.of_reaches (C : EdgeCut E z) {u v : V}
    (h : Relation.ReflTransGen E u v) (hv : C.before v = true) :
    C.before u = true := by
  induction h with
  | refl => exact hv
  | tail _ hEdge ih => exact ih (C.order hEdge hv)

section Letters

open DeletionCode.Explicit.LetterSequence DeletionCode.Explicit.LocalBudget

variable {ℓ m c : ℕ} {α : Type*}

/-- Original-letter edges of the initial chain, with the two exterior
sentinel edges suppressed. -/
def originalEdges : Letter ℓ α → Letter ℓ α → Prop
  | .original i, .original j => j.val = i.val+1
  | _, _ => False

def initialCut (z : Fin ℓ) : EdgeCut (originalEdges (α := α)) (.original z) := by
  let before : Letter ℓ α → Bool
    | .original i => decide (i < z)
    | .fresh .. => false
  refine ⟨before,by simp [before],?_,?_⟩
  · intro a b he hb
    cases a <;> cases b <;> simp only [originalEdges] at he
    rename_i i j
    have hj : j < z := of_decide_eq_true hb
    have hi : i < z := by change i.val < z.val; omega
    exact decide_eq_true hi
  · intro a b he ha hb
    cases a <;> cases b <;> simp only [originalEdges] at he
    rename_i i j
    have hi : i < z := of_decide_eq_true ha
    have hj : ¬ j < z := of_decide_eq_false hb
    have eq : j = z := Fin.ext (by omega)
    rw [eq]

@[simp] theorem initialCut_original (z i : Fin ℓ) :
    (initialCut (α := α) z).before (.original i) = decide (i < z) := rfl

/-- A fresh letter in a patch has old-path brackets lying inside that patch.
Only the outward-facing endpoint is used when comparing it with a cut in
another patch. -/
def HasBrackets (E : Letter ℓ α → Letter ℓ α → Prop) (P : Patches ℓ c)
    (p : Fin c) (v : Letter ℓ α) : Prop :=
  ∃ lo hi : Fin ℓ, P.first p ≤ lo.val ∧ hi.val ≤ P.last p ∧ lo < hi ∧
    Relation.ReflTransGen E (.original lo) v ∧ Relation.ReflTransGen E v (.original hi)

private theorem reaches_through_segment {left right v : V} {mid : List V}
    (hp : ∀ a b, (a,b) ∈ segmentEdges left mid right → E a b) (hv : v ∈ mid) :
    Relation.ReflTransGen E left v ∧ Relation.ReflTransGen E v right := by
  induction mid generalizing left with
  | nil => simp at hv
  | cons a tail ih =>
    have he : E left a := hp _ _ (by simp [segmentEdges])
    have hrest : ∀ p q, (p,q) ∈ segmentEdges a tail right → E p q :=
      fun p q h => hp p q (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      refine ⟨Relation.ReflTransGen.single he,?_⟩
      clear ih hp he hv
      induction tail generalizing a with
      | nil => exact Relation.ReflTransGen.single (hrest _ _ (by simp [segmentEdges]))
      | cons t rest ih =>
        have ht : E a t := hrest _ _ (by simp [segmentEdges])
        exact (Relation.ReflTransGen.single ht).trans (ih t (fun p q h => hrest p q (List.mem_cons_of_mem _ h)))
    · obtain ⟨hl,hr⟩ := ih hrest hv
      exact ⟨(Relation.ReflTransGen.single he).trans hl,hr⟩

/-- The two old flanks of a gate give brackets for every inserted letter.
The initial and final bracket positions are original letters in the patch. -/
theorem gate_brackets {E : Letter ℓ α → Letter ℓ α → Prop} (P : Patches ℓ c) (p : Fin c)
    (left right : Letter ℓ α) {fresh : List (Letter ℓ α)} {v : Letter ℓ α}
    (hv : v ∈ fresh) {lo hi : Fin ℓ} (hlo : P.first p ≤ lo.val) (hhi : hi.val ≤ P.last p)
    (hlt : lo < hi) (hl : Relation.ReflTransGen E (.original lo) left)
    (hr : Relation.ReflTransGen E right (.original hi)) :
    HasBrackets (addGate E left fresh right) P p v := by
  obtain ⟨hfirst,hlast⟩ := reaches_through_segment (E := addGate E left fresh right)
    (left := left) (right := right) (mid := fresh) (fun a b ha => Or.inr ha) hv
  have retain {a b} (h : Relation.ReflTransGen E a b) :
      Relation.ReflTransGen (addGate E left fresh right) a b := by
    induction h with
    | refl => exact .refl
    | tail _ hedge ih => exact ih.tail (Or.inl hedge)
  exact ⟨lo,hi,hlo,hhi,hlt,(retain hl).trans hfirst,hlast.trans (retain hr)⟩

#print axioms gate_brackets

/-- Convert the graph invariant at an unmarked position to the cut used by
the local budget, using the path edges and the fresh-letter brackets. -/
def EdgeCut.onLift {E : Letter ℓ α → Letter ℓ α → Prop} {z : Fin ℓ}
    (C : EdgeCut E (.original z)) (u : Lift ℓ m α) (P : Patches ℓ c)
    (owner : ℕ → Option (Fin c))
    (horiginal : ∀ i : Fin ℓ, C.before (.original i) = decide (i < z))
    (hsteps : ∀ i j : Fin m, j.val = i.val+1 → E (u.letters i) (u.letters j))
    (hbrackets : ∀ i g a x p, u.letters i = .fresh g a x → owner g = some p →
      HasBrackets E P p (.fresh g a x)) : OriginalCut u P owner z := by
  refine ⟨C.before,horiginal,?_,?_,?_,?_⟩
  · intro i g a x p hi hp hleft
    obtain ⟨_,r,_,hr,_,_,hReach⟩ := hbrackets i g a x p hi hp
    exact C.of_reaches hReach (by rw [horiginal]; exact decide_eq_true (hr.trans_lt hleft))
  · intro i g a x p hi hp hright
    obtain ⟨l,_,hl,_,_,hReach,_⟩ := hbrackets i g a x p hi hp
    cases hb : C.before (.fresh g a x) with
    | false => rfl
    | true =>
      have h := C.of_reaches hReach hb
      rw [horiginal] at h
      have h' := of_decide_eq_true h
      change l.val < z.val at h'
      omega
  · intro i j hij h
    have walk (n : ℕ) (hn : n < m) (hi : i.val ≤ n)
        (hbefore : C.before (u.letters ⟨n,hn⟩) = true) : C.before (u.letters i) = true := by
      induction n with
      | zero =>
        have e : (⟨0,hn⟩ : Fin m) = i := Fin.ext (by change 0 = i.val; omega)
        simpa only [e] using hbefore
      | succ n ih =>
        by_cases hn' : i.val ≤ n
        · have hp : n < m := by omega
          exact ih hp hn' (C.order (hsteps ⟨n,hp⟩ ⟨n+1,hn⟩ rfl) hbefore)
        · have e : (⟨n+1,hn⟩ : Fin m) = i := Fin.ext (by change n+1 = i.val; omega)
          simpa only [e] using hbefore
    exact walk j.val j.isLt hij h
  · intro i j hs hi hj
    exact C.exit (hsteps i j hs) hi hj

#print axioms EdgeCut.onLift

/-- A chronological letter graph and the original positions marked so far.
Each gate follows an existing segment and uses new vertices for its interior. -/
inductive History (ℓ : ℕ) (α : Type*) [DecidableEq α] :
    (Letter ℓ α → Letter ℓ α → Prop) → Finset (Fin ℓ) → Prop where
  | initial : History ℓ α originalEdges ∅
  | gate {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
      (prior : History ℓ α E marked) (left right : Letter ℓ α) (removed fresh : List (Letter ℓ α))
      (hpath : ∀ a b, (a,b) ∈ segmentEdges left removed right → E a b)
      (hl : left ∉ fresh) (hr : right ∉ fresh) (hd : fresh.Nodup)
      (hnew : ∀ {a b}, E a b → a ∉ fresh ∧ b ∉ fresh)
      (hfresh : ∀ i : Fin ℓ, Letter.original i ∉ fresh) :
      History ℓ α (addGate E left fresh right)
        (marked ∪ (removed.filterMap Letter.position).toFinset)

/-- Every chronological letter graph admits a strictly increasing rank. -/
theorem History.rank [DecidableEq α]
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) :
    ∃ rank : Letter ℓ α → ℕ, ∀ {a b}, E a b → rank a < rank b := by
  induction H with
  | initial =>
    refine ⟨fun v => (v.position.map Fin.val).getD 0,?_⟩
    intro a b hab
    cases a <;> cases b <;> simp only [originalEdges] at hab
    simp only [Letter.position,Option.map_some,Option.getD_some]
    omega
  | gate prior left right removed fresh hpath hl hr hd hnew hfresh ih =>
    obtain ⟨rank,hrank⟩ := ih
    exact rank_addGate rank hrank left right removed fresh hpath hl hr hd hnew

theorem History.acyclic [DecidableEq α]
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (v : Letter ℓ α) : ¬ Relation.TransGen E v v := by
  obtain ⟨rank,hrank⟩ := H.rank
  exact fun h => (lt_irrefl _) (rank_reaches rank hrank h)

#print axioms History.acyclic

/-- Every unmarked original letter has a cut throughout a valid gate
history. The cut classifies the original letters by their positions. -/
theorem History.unmarked_cut [DecidableEq α]
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (z : Fin ℓ) (hz : z ∉ marked) :
    ∃ C : EdgeCut E (.original z), ∀ i : Fin ℓ, C.before (.original i) = decide (i < z) := by
  induction H with
  | initial => exact ⟨initialCut z, initialCut_original z⟩
  | gate prior left right removed fresh hpath hl hr hd hnew hfresh ih =>
    obtain ⟨C,horig⟩ := ih (fun h => hz (Finset.mem_union_left _ h))
    have hk : Letter.original z ∉ removed := by
      intro h
      apply hz
      apply Finset.mem_union_right
      rw [List.mem_toFinset,List.mem_filterMap]
      exact ⟨.original z,h,rfl⟩
    refine ⟨C.extend left right removed fresh hpath hk (hfresh z) hl hr hnew,?_⟩
    intro i
    exact (C.extend_before_of_old left right removed fresh hpath hk (hfresh z) hl hr hnew _
      (hfresh i)).trans (horig i)

/-- A path in a chronological letter graph satisfies the local budget once
the patch data supply gate capacities and the brackets of its fresh letters. -/
theorem History.local_budget [DecidableEq α]
    {E : Letter ℓ α → Letter ℓ α → Prop} {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (u : Lift ℓ m α) (P : Patches ℓ c)
    (owner : ℕ → Option (Fin c)) {L cap : ℕ} (hL : 0 < L) (hlen : m ≤ 3*L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card) (hcap : 4*cap ≤ L)
    (hmark : ∀ p, (P.marks p).card ≤ cap)
    (hfresh : ∀ p, (freshIn u owner p).card ≤ cap)
    (howner : ∀ gate a symbol i, u.letters i = .fresh gate a symbol → ∃ p, owner gate = some p)
    (hmarked : ∀ z ∈ marked, z.val ∈ Finset.univ.biUnion P.marks)
    (hsteps : ∀ i j : Fin m, j.val = i.val+1 → E (u.letters i) (u.letters j))
    (hbrackets : ∀ i g a x p, u.letters i = .fresh g a x → owner g = some p →
      HasBrackets E P p (.fresh g a x)) :
    u.freshOffsets.card ≤ 14*cap ∧ u.omissions.card ≤ 14*cap := by
  apply local_budget_of_cuts u P owner hL hlen hwidth hcap hmark hfresh howner
  intro z hz
  obtain ⟨C,horig⟩ := H.unmarked_cut z (fun hm => hz (hmarked z hm))
  exact ⟨C.onLift u P owner horig hsteps hbrackets⟩

#print axioms History.unmarked_cut
#print axioms History.local_budget

end Letters

end DeletionCode.Explicit.LetterGraphCuts
