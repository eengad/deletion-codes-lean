import DeletionCode.Explicit.LetterSequence

/-! A splice of two overlapping windows at the first shared original letter
(`d:add-rule`). Fresh letters retain the identifiers of their gates. -/

namespace DeletionCode.Explicit.LetterSequence

variable {ℓ a k b : ℕ} {α : Type*}

private def leftOffset (a : ℕ) (i : Fin k) : Fin (a+k) := ⟨a+i.val,by omega⟩

/-- The two aligned positions must denote the same original letter. -/
abbrev Shared (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) (i : Fin k) : Prop :=
  ((u.letters (leftOffset a i)).position).isSome ∧
    (u.letters (leftOffset a i)).position = (v.letters (Fin.castLE (Nat.le_add_right k b) i)).position

private theorem shared_iff (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) (i : Fin k) :
    Shared u v i ↔ ∃ p, (u.letters (leftOffset a i)).position = some p ∧
      (v.letters (Fin.castLE (Nat.le_add_right k b) i)).position = some p := by
  unfold Shared
  cases h : (u.letters (leftOffset a i)).position <;> simp [eq_comm]

/-- Search offsets of the overlap in increasing order. -/
def splicePivot (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) : Option {i : Fin k // Shared u v i} :=
  let S := Finset.univ.filter (Shared u v)
  if h : S.Nonempty then some ⟨S.min' h,(Finset.mem_filter.mp (S.min'_mem h)).2⟩ else none

theorem splicePivot_isSome {u : Lift ℓ (a+k) α} {v : Lift ℓ (k+b) α}
    {i : Fin k} (h : Shared u v i) : (splicePivot u v).isSome = true := by
  have he : (Finset.univ.filter (Shared u v)).Nonempty :=
    ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  simp [splicePivot,he]

theorem splicePivot_first {u : Lift ℓ (a+k) α} {v : Lift ℓ (k+b) α} {p : {i : Fin k // Shared u v i}}
    (hp : splicePivot u v = some p) {i : Fin k} (h : Shared u v i) : p.val ≤ i := by
  let S := Finset.univ.filter (Shared u v)
  have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  have hne : S.Nonempty := ⟨i,hm⟩
  have he : S.min' hne = p.val := by
    have hs : some (⟨S.min' hne,(Finset.mem_filter.mp (S.min'_mem hne)).2⟩ :
        {i : Fin k // Shared u v i}) = some p := by
      simpa only [splicePivot,S,dite_eq_left hne] using hp
    exact congrArg Subtype.val (Option.some.inj hs)
  rw [← he]
  exact Finset.min'_le _ _ hm

private def joinedLetters (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) (p : Fin k)
    (i : Fin (a+k+b)) : Letter ℓ α :=
  if h : i.val ≤ a+p.val then u.letters ⟨i.val,by omega⟩
  else v.letters ⟨i.val-a,by omega⟩

/-- Keep the left prefix through the shared letter and the right suffix
after it. The shared original position proves that the join is increasing. -/
private def join (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) (p : {i : Fin k // Shared u v i}) :
    Lift ℓ (a+k+b) α where
  letters := joinedLetters u v p.val
  increasing := by
    intro i j x y hij hx hy
    by_cases hj : j.val ≤ a+p.val.val
    · have hi : i.val ≤ a+p.val.val := by omega
      rw [joinedLetters,dite_eq_left hi] at hx
      rw [joinedLetters,dite_eq_left hj] at hy
      exact u.increasing (by exact hij) hx hy
    · rw [joinedLetters,dite_eq_right hj] at hy
      by_cases hi : i.val ≤ a+p.val.val
      · rw [joinedLetters,dite_eq_left hi] at hx
        obtain ⟨z,hleft,hright⟩ := (shared_iff u v p.val).mp p.property
        have hxy : x ≤ z := by
          rcases lt_or_eq_of_le hi with hi' | hi'
          · exact (u.increasing (by exact hi') hx hleft).le
          · have he : (⟨i.val,by omega⟩ : Fin (a+k)) = leftOffset a p.val :=
              Fin.ext hi'
            exact (Option.some.inj (hx.symm.trans ((congrArg (fun j => (u.letters j).position) he).trans hleft))).le
        exact hxy.trans_lt (v.increasing (show p.val.val < j.val-a by omega) hright hy)
      · rw [joinedLetters,dite_eq_right hi] at hx
        exact v.increasing (show i.val-a < j.val-a by omega) hx hy

def splice (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) : Option (Lift ℓ (a+k+b) α) :=
  (splicePivot u v).map (join u v)

/-- In the regime of `d:aligned`, the splice search succeeds when the two
overlap spellings agree. -/
theorem splice_isSome {x : Fin ℓ → α} {K Λ : ℕ} (hx : Strong x K Λ)
    (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) (hk : K+2*Λ ≤ k)
    (hspell : (u.window a k (by omega)).spelling x = (v.window 0 k (by omega)).spelling x)
    (huf : u.freshOffsets.card ≤ Λ) (hvf : v.freshOffsets.card ≤ Λ)
    (huo : u.omissions.card ≤ Λ) (hvo : v.omissions.card ≤ Λ) :
    (splice u v).isSome = true := by
  have hu : a+k ≤ a+k := le_rfl
  have hv : 0+k ≤ k+b := by omega
  obtain ⟨i,p,_,hl,hr⟩ := aligned hx _ _ hk hspell
    ((u.window_fresh_le hu).trans huf) ((v.window_fresh_le hv).trans hvf)
    ((Finset.card_le_card (u.window_omissions_subset hu)).trans huo)
    ((Finset.card_le_card (v.window_omissions_subset hv)).trans hvo)
  have hs : Shared u v i := (shared_iff u v i).mpr ⟨p,hl,by simpa [Lift.window,Fin.castLE] using hr⟩
  simpa [splice] using splicePivot_isSome hs

/-- The joined spelling agrees with both input spellings on their placed
windows, including the part of the overlap read from the other input. -/
theorem splice_spelling {u : Lift ℓ (a+k) α} {v : Lift ℓ (k+b) α}
    {w : Lift ℓ (a+k+b) α} (h : splice u v = some w) (x : Fin ℓ → α)
    (hspell : (u.window a k (by omega)).spelling x = (v.window 0 k (by omega)).spelling x) :
    (∀ i : Fin (a+k), w.spelling x (Fin.castLE (Nat.le_add_right (a+k) b) i) = u.spelling x i) ∧
    (∀ i : Fin (k+b), w.spelling x ⟨a+i.val,by omega⟩ = v.spelling x i) := by
  unfold splice at h
  cases hp : splicePivot u v with
  | none => simp [hp] at h
  | some p =>
    have hw : join u v p = w := by simpa [hp] using h
    subst w
    constructor
    · intro i
      by_cases hi : i.val ≤ a+p.val.val
      · simp only [Lift.spelling,join,joinedLetters,Fin.val_castLE,dite_eq_left hi]
      · let j : Fin k := ⟨i.val-a,by omega⟩
        have hj : a+j.val = i.val := Nat.add_sub_of_le (by omega : a ≤ i.val)
        have hs := congrFun hspell j
        simp only [Lift.spelling,Lift.window,Nat.zero_add] at hs
        have he : (⟨a+j.val,by omega⟩ : Fin (a+k)) = i := Fin.ext hj
        rw [he] at hs
        simp only [Lift.spelling,join,joinedLetters,Fin.val_castLE,dite_eq_right hi]
        exact hs.symm
    · intro i
      by_cases hi : a+i.val ≤ a+p.val.val
      · let j : Fin k := ⟨i.val,by omega⟩
        change (joinedLetters u v p.val _).symbol x = _
        rw [joinedLetters,dite_eq_left hi]
        simpa [Lift.window,Lift.spelling,j] using congrFun hspell j
      · change (joinedLetters u v p.val _).symbol x = _
        rw [joinedLetters,dite_eq_right hi]
        have he : (⟨(a+i.val)-a,by omega⟩ : Fin (k+b)) = i := Fin.ext (by change a+i.val-a=i.val; omega)
        exact congrArg (fun j => (v.letters j).symbol x) he

/-- A splice takes the left prefix through the least shared original
letter and the right suffix after it. This specification does not run the
pivot search. -/
def SpliceSpec (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α)
    (w : Lift ℓ (a+k+b) α) : Prop :=
  ∃ i : Fin k, Shared u v i ∧ (∀ j, Shared u v j → i ≤ j) ∧
    ∀ j, w.letters j = joinedLetters u v i j

theorem splice_eq_some_iff {u : Lift ℓ (a+k) α} {v : Lift ℓ (k+b) α}
    {w : Lift ℓ (a+k+b) α} : splice u v = some w ↔ SpliceSpec u v w := by
  constructor
  · intro h
    cases hp : splicePivot u v with
    | none => simp [splice,hp] at h
    | some p =>
      have hw : join u v p = w := by simpa [splice,hp] using h
      subst w
      exact ⟨p.val,p.property,fun j hj => splicePivot_first hp hj,fun _ => rfl⟩
  · rintro ⟨i,hi,hfirst,hletters⟩
    cases hp : splicePivot u v with
    | none =>
      have hs := splicePivot_isSome hi
      simp [hp] at hs
    | some p =>
      have hpi : p.val = i := le_antisymm (splicePivot_first hp hi) (hfirst p.val p.property)
      have hjoin : join u v p = w := by
        have he : (join u v p).letters = w.letters := funext fun j => by
          rw [hletters]
          change joinedLetters u v p.val j = _
          rw [hpi]
        cases hleft : join u v p
        cases w
        simpa [hleft] using he
      simpa [splice,hp] using hjoin

/-- Renumber just the gate identifier of a fresh letter. -/
def Letter.renameEntry (f : ℕ → ℕ) : Letter ℓ α → Letter ℓ α
  | .original p => .original p
  | .fresh id k x => .fresh (f id) k x

@[simp] theorem Letter.position_renameEntry (f : ℕ → ℕ) (w : Letter ℓ α) :
    (w.renameEntry f).position = w.position := by
  cases w <;> rfl

/-- Renumber fresh identifiers while retaining original positions and symbols. -/
def Lift.renameEntries {n : ℕ} (u : Lift ℓ n α) (f : ℕ → ℕ) : Lift ℓ n α where
  letters i := (u.letters i).renameEntry f
  increasing hij hp hq := u.increasing hij
    (by simpa only [Letter.position_renameEntry] using hp)
    (by simpa only [Letter.position_renameEntry] using hq)

@[simp] theorem Lift.renameEntries_letter {n : ℕ} (u : Lift ℓ n α) (f : ℕ → ℕ) (i : Fin n) :
    (u.renameEntries f).letters i = (u.letters i).renameEntry f := rfl

/-- Matching offsets and their first occurrence depend only on originals,
so renumbering fresh entries commutes with a successful splice. -/
theorem splice_renameEntries {u : Lift ℓ (a+k) α} {v : Lift ℓ (k+b) α}
    {w : Lift ℓ (a+k+b) α} (f : ℕ → ℕ) (h : splice u v = some w) :
    splice (u.renameEntries f) (v.renameEntries f) = some (w.renameEntries f) := by
  obtain ⟨i,hi,hfirst,hletters⟩ := splice_eq_some_iff.mp h
  apply splice_eq_some_iff.mpr
  refine ⟨i,by simpa only [Shared,Lift.renameEntries_letter,Letter.position_renameEntry] using hi,?_,?_⟩
  · intro j hj
    apply hfirst
    simpa only [Shared,Lift.renameEntries_letter,Letter.position_renameEntry] using hj
  · intro j
    change (w.letters j).renameEntry f = joinedLetters (u.renameEntries f) (v.renameEntries f) i j
    rw [hletters]
    by_cases hj : j.val ≤ a+i.val <;> simp [joinedLetters,hj]

#print axioms splice_renameEntries

#print axioms splice_eq_some_iff

/-- The consecutive letters of a lift are edges of the supplied graph. -/
abbrev Lift.Follows {n : ℕ} (u : Lift ℓ n α) (E : Letter ℓ α → Letter ℓ α → Prop) : Prop :=
  ∀ i j : Fin n, j.val = i.val+1 → E (u.letters i) (u.letters j)

theorem Lift.window_follows {n : ℕ} (u : Lift ℓ n α) {E : Letter ℓ α → Letter ℓ α → Prop}
    (hu : u.Follows E) (start len : ℕ) (h : start+len ≤ n) : (u.window start len h).Follows E := by
  intro i j hstep
  exact hu ⟨start+i.val,by omega⟩ ⟨start+j.val,by omega⟩ (by change start+j.val = start+i.val+1; omega)

private theorem equal_original_positions {u v : Letter ℓ α} {p : Fin ℓ}
    (hu : u.position = some p) (hv : v.position = some p) : u = v := by
  cases u <;> cases v <;> simp_all [Letter.position]

private theorem join_follows {E : Letter ℓ α → Letter ℓ α → Prop}
    (u : Lift ℓ (a+k) α) (v : Lift ℓ (k+b) α) (p : {i : Fin k // Shared u v i})
    (hu : u.Follows E) (hv : v.Follows E) : (join u v p).Follows E := by
  intro i j hstep
  change E (joinedLetters u v p.val i) (joinedLetters u v p.val j)
  by_cases hj : j.val ≤ a+p.val.val
  · have hi : i.val ≤ a+p.val.val := by omega
    simp only [joinedLetters,dite_eq_left hi,dite_eq_left hj]
    exact hu _ _ hstep
  · by_cases hi : i.val ≤ a+p.val.val
    · simp only [joinedLetters,dite_eq_left hi,dite_eq_right hj]
      obtain ⟨z,hleft,hright⟩ := (shared_iff u v p.val).mp p.property
      have he : (⟨i.val,by omega⟩ : Fin (a+k)) = leftOffset a p.val :=
        Fin.ext (by change i.val = a+p.val.val; omega)
      rw [he,equal_original_positions hleft hright]
      apply hv
      change j.val-a = p.val.val+1
      omega
    · simp only [joinedLetters,dite_eq_right hi,dite_eq_right hj]
      apply hv
      change j.val-a = i.val-a+1
      omega

/-- The join edge at the shared original letter is an edge from the right
input. Together with the two retained pieces this keeps the splice in the
same graph, before adding any new gate. -/
theorem splice_follows {E : Letter ℓ α → Letter ℓ α → Prop}
    {u : Lift ℓ (a+k) α} {v : Lift ℓ (k+b) α} {out : Lift ℓ (a+k+b) α}
    (h : splice u v = some out) (hu : u.Follows E) (hv : v.Follows E) :
    out.Follows E := by
  cases hp : splicePivot u v with
  | none => simp [splice,hp] at h
  | some p =>
    have hw : join u v p = out := by simpa [splice,hp] using h
    rw [← hw]
    exact join_follows u v p hu hv

#print axioms splice_follows

#print axioms splice_spelling
#print axioms splicePivot_first
#print axioms splice_isSome

end DeletionCode.Explicit.LetterSequence
