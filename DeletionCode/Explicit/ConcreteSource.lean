import DeletionCode.Explicit.Machine.Assembly
import DeletionCode.Explicit.RecognizerParameters
import DeletionCode.Explicit.LabelSeparation
import DeletionCode.Explicit.CompressorFrame

/-! Assemble the executable Stage 1 source callbacks at each block length. -/

namespace DeletionCode.Explicit.ConcreteSource

open FieldHash LetterSequence Recognizer UniformParameters CompressorFrame
open Machine

variable {q b t ℓ : ℕ}

abbrev Hash (q b t ℓ : ℕ) :=
  TernaryMatrix (hashWidth q b t ℓ) (q^(gram q b t ℓ))

structure Procedures (q b t : ℕ) where
  lookup : List Bool → (ℓ : ℕ) → Option (Hash q b t ℓ)
  strong : (ℓ : ℕ) → (Fin ℓ → Fin q) → Bool
  exceptional : (ℓ : ℕ) → Hash q b t ℓ → (Fin ℓ → Fin q) → Bool
  branch : (ℓ : ℕ) → Hash q b t ℓ → Fin 3 → Branch q

def runAt (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) :=
  recognize (K := windowLength q ℓ) (b := b) (s := edits t) H pad x (componentCutoff q b t ℓ)

def acceptedAt (C : Procedures q b t) (pad : Fin q) (H : Hash q b t ℓ)
    (x : Fin ℓ → Fin q) : Bool :=
  if C.strong ℓ x && !C.exceptional ℓ H x then
    match runAt pad H x with
    | some (.complete _) => true
    | _ => false
  else false

def rankAt (pad : Fin q) (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) : ℕ :=
  match runAt pad H x with
  | some (.complete hs) =>
    (labelOf (K := windowLength q ℓ) (b := b) H pad x hs).getD 0
  | _ => 0

def callbacks (hq : 1 < q) (pad : Fin q) (C : Procedures q b t) : SourceCallbacks q where
  accepted p :=
    if p.2.length < minLength q b t then true
    else (C.lookup p.1 p.2.length).elim true (fun H => acceptedAt C pad H p.2.get)
  compress p := ((C.lookup p.1 p.2.length).bind fun H =>
    CompressorFrame.compress hq pad (C.branch p.2.length H) p.2).getD []
  expand p := (C.lookup p.1 (p.2.length+1)).bind fun H =>
    CompressorFrame.decompress (C.branch (p.2.length+1) H) p.2
  label p := (C.lookup p.1 p.2.length).elim 0 (fun H => rankAt pad H p.2.get)

structure DeciderLaws (C : Procedures q b t) (pad : Fin q) : Prop where
  strong : ∀ {ℓ} (x : Fin ℓ → Fin q),
    C.strong ℓ x = true ↔ Strong x (windowLength q ℓ) (omittedLetters q b t ℓ)
  exceptional : ∀ {ℓ} (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (_ : minLength q b t ≤ ℓ),
    C.exceptional ℓ H x = true ↔
      ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t (windowLength q ℓ) x

structure LengthLaws (C : Procedures q b t) (pad : Fin q) (bits : List Bool) (n : ℕ) : Prop where
  lookup : ∀ ℓ, minLength q b t ≤ ℓ → ℓ ≤ n → ∃ H, C.lookup bits ℓ = some H
  branches : ∀ {ℓ H}, C.lookup bits ℓ = some H → ∀ i, (C.branch ℓ H i).Laws pad
  covers : ∀ {x H}, minLength q b t ≤ x.length → C.lookup bits x.length = some H →
    acceptedAt C pad H x.get = false → ∃ i payload, (C.branch x.length H i).encode x = some payload

private theorem minLength_pos (hq : 1 < q) : 0 < minLength q b t := by
  unfold minLength
  positivity

private theorem acceptedAt_spec (C : Procedures q b t) (pad : Fin q)
    (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (h : acceptedAt C pad H x = true) :
    C.strong ℓ x = true ∧ C.exceptional ℓ H x = false ∧
      ∃ S, runAt pad H x = some (.complete S) := by
  unfold acceptedAt at h
  split at h
  next ok =>
    obtain ⟨hs,he⟩ := Bool.and_eq_true_iff.mp ok
    refine ⟨hs, by simpa using he, ?_⟩
    split at h
    next hist hh => exact ⟨hist,hh⟩
    next => contradiction
  next => contradiction

theorem repairLaws (hq : 1 < q) (pad : Fin q) (C : Procedures q b t)
    {bits : List Bool} {n : ℕ} (h : LengthLaws C pad bits n) :
    (callbacks hq pad C).RepairLaws bits := by
  have hmin := minLength_pos (b := b) (t := t) hq
  have shorten {x : QWord q} (hx : (callbacks hq pad C).accepted (bits,x) = false) :
      ((callbacks hq pad C).compress (bits,x)).length+1 = x.length ∧
        (callbacks hq pad C).expand (bits,(callbacks hq pad C).compress (bits,x)) = some x := by
    have hcut : minLength q b t ≤ x.length := by
      by_contra hn
      have hsmall : x.length < minLength q b t := by omega
      simp [callbacks,hsmall] at hx
    cases hlookup : C.lookup bits x.length with
    | none => simp [callbacks,not_lt_of_ge hcut,hlookup] at hx
    | some H =>
      have hreject : acceptedAt C pad H x.get = false := by
        simpa [callbacks,not_lt_of_ge hcut,hlookup] using hx
      obtain ⟨i,v,hencode⟩ := h.covers hcut hlookup hreject
      have hp := choose_complete (C.branch x.length H) hencode
      cases hc : CompressorFrame.compress hq pad (C.branch x.length H) x with
      | none =>
        cases he : choose (C.branch x.length H) x <;>
          simp [he,CompressorFrame.compress] at hp hc
      | some w =>
        have hc' : (callbacks hq pad C).compress (bits,x) = w := by simp [callbacks,hlookup,hc]
        obtain ⟨hw,hinv⟩ := compress_correct hq pad _ (h.branches hlookup) (by omega) hc
        refine ⟨by simpa only [hc'] using hw,?_⟩
        rw [hc']
        change (C.lookup bits (w.length+1)).bind
          (fun J => CompressorFrame.decompress (C.branch (w.length+1) J) w) = some x
        rw [hw,hlookup]
        exact hinv
  refine ⟨by simp [callbacks,hmin],fun x hx => (shorten hx).1,fun x hx => (shorten hx).2,?_⟩
  intro y x hy
  cases hlookup : C.lookup bits (y.length+1) with
  | none => simp [callbacks,hlookup] at hy
  | some H =>
    exact decompress_length (C.branch (y.length+1) H) pad (h.branches hlookup)
      (by simpa [callbacks,hlookup] using hy)

private theorem script_cut {α : Type*} {b r : ℕ} {x y : List α}
    (h : Burst.Script b x y r) (k : ℕ) (hk : k ≤ r) :
    ∃ z, Burst.Script b x z k ∧ Burst.Script b z y (r-k) := by
  induction h generalizing k with
  | refl =>
    have he : k = 0 := by omega
    subst k
    exact ⟨x,.refl _,.refl _⟩
  | @step pre suffix U V r hU hV hne hprev ih =>
    by_cases hkr : k ≤ r
    · obtain ⟨z,hz,hend⟩ := ih k hkr
      exact ⟨z,hz,by simpa only [show r+1-k = (r-k)+1 by omega] using
        Burst.Script.step hU hV hne hend⟩
    · have he : k = r+1 := by omega
      subst k
      refine ⟨pre++V++suffix,.step hU hV hne hprev,?_⟩
      rw [Nat.sub_self]
      exact .refl _

private theorem confusable_of_bursts {α : Type*} {x y : List α}
    (h : Burst.WithinBursts b (2*t) x y) : Burst.Confusable b t x y := by
  obtain ⟨r,hr,hs⟩ := h
  obtain ⟨z,hxz,hzy⟩ := script_cut hs (min r t) (Nat.min_le_left _ _)
  exact ⟨z,⟨min r t,Nat.min_le_right _ _,hxz⟩,⟨r-min r t,by omega,hzy.reverse⟩⟩

private theorem rankAt_bound (C : Procedures q b t) (pad : Fin q)
    (H : Hash q b t ℓ) (x : Fin ℓ → Fin q) (hx : acceptedAt C pad H x = true) :
    rankAt pad H x < 3*hashCount q b t ℓ := by
  obtain ⟨_,_,hs,hcall⟩ := acceptedAt_spec C pad H x hx
  obtain ⟨u,hu,hbound⟩ := labelOf_exists (K := windowLength q ℓ) (b := b) H pad x hs
  simpa [rankAt,hcall,hu,hashCount] using hbound

private theorem rankAt_separate (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (C : Procedures q b t) (pad : Fin q) (d : DeciderLaws C pad)
    (hmin : minLength q b t ≤ ℓ) (H : Hash q b t ℓ) (x y : Fin ℓ → Fin q)
    (hx : acceptedAt C pad H x = true) (hy : acceptedAt C pad H y = true)
    (he : rankAt pad H x = rankAt pad H y)
    (hconf : Burst.WithinBursts b (2*t) (List.ofFn x) (List.ofFn y)) : x = y := by
  obtain ⟨hsx,hex,S,hS⟩ := acceptedAt_spec C pad H x hx
  obtain ⟨hsy,_,T,hT⟩ := acceptedAt_spec C pad H y hy
  have sx := (d.strong x).mp hsx
  have sy := (d.strong y).mp hsy
  have hxGood : ¬ ExceptionalWeight.Exceptional pad finFunctionFinEquiv.symm H b t (windowLength q ℓ) x := by
    intro hn
    have hh := (d.exceptional H x hmin).mpr hn
    rw [hex] at hh
    contradiction
  have Hbounds := basicBounds hq hb ht hmin
  have P := recognizerBounds Hbounds
  have hw := recognizer_window Hbounds
  have hpos := (minLength_pos (b := b) (t := t) (show 1 < q by omega)).trans_le hmin
  obtain ⟨u,hu,hvx,hrx⟩ := recognize_verified P H pad x sx hw hpos
  obtain ⟨v,hv,hvy,_⟩ := recognize_verified P H pad y sy hw hpos
  have hu' : u = .complete S := Option.some.inj (hu.symm.trans hS)
  have hv' : v = .complete T := Option.some.inj (hv.symm.trans hT)
  rw [hu'] at hvx hrx
  rw [hv'] at hvy
  have hk : 1 ≤ windowLength q ℓ := by unfold windowLength; omega
  obtain ⟨a,ha,_⟩ := labelOf_exists (K := windowLength q ℓ) (b := b) H pad x S
  obtain ⟨a',ha',_⟩ := labelOf_exists (K := windowLength q ℓ) (b := b) H pad y T
  have he' : a = a' := by simpa [rankAt,hS,hT,ha,ha'] using he
  exact accepted_labels_separate P H pad ⟨0,hpos⟩ ht hk hw sx sy hxGood hvx hvy hrx
    (ha.trans (he' ▸ ha'.symm)) (confusable_of_bursts hconf)

theorem eval_ofFn {β : Type*} (f : (n : ℕ) → (Fin n → Fin q) → β)
    (x : Fin ℓ → Fin q) : f (List.ofFn x).length (List.ofFn x).get = f ℓ x := by
  suffices h : (⟨(List.ofFn x).length,(List.ofFn x).get⟩ : Σ n : ℕ, Fin n → Fin q) = ⟨ℓ,x⟩ from
    congrArg (fun p : Σ n : ℕ, Fin n → Fin q => f p.1 p.2) h
  apply Sigma.ext List.length_ofFn
  have cast_eq (a c : ℕ) (h : a = c) (g : Fin a → Fin q) :
      HEq g (g ∘ Fin.cast h.symm) := by
    subst c
    rfl
  refine (cast_eq _ _ List.length_ofFn _).trans (heq_of_eq ?_)
  funext i
  simp

private theorem accepted_ofFn (hq : 1 < q) (pad : Fin q) (C : Procedures q b t)
    (bits : List Bool) (H : Hash q b t ℓ) (hl : C.lookup bits ℓ = some H)
    (hc : minLength q b t ≤ ℓ) (x : Fin ℓ → Fin q) :
    (callbacks hq pad C).accepted (bits,List.ofFn x) = acceptedAt C pad H x := by
  have h := eval_ofFn (fun n z => if n < minLength q b t then true
    else (C.lookup bits n).elim true (fun J => acceptedAt C pad J z)) x
  exact h.trans (by simp [not_lt_of_ge hc,hl])

private theorem label_ofFn (hq : 1 < q) (pad : Fin q) (C : Procedures q b t)
    (bits : List Bool) (H : Hash q b t ℓ) (hl : C.lookup bits ℓ = some H)
    (x : Fin ℓ → Fin q) :
    (callbacks hq pad C).label (bits,List.ofFn x) = rankAt pad H x := by
  have h := eval_ofFn (fun n z => (C.lookup bits n).elim 0 (fun J => rankAt pad J z)) x
  exact h.trans (by simp [hl])

/-- Source correctness with the branch and setup laws exposed at their
length-indexed interfaces. -/
theorem sourceGuarantees (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (pad : Fin q) (C : Procedures q b t) (d : DeciderLaws C pad)
    {bits : List Bool} {n : ℕ} (h : LengthLaws C pad bits n) :
    SourceGuarantees (callbacks (by omega) pad C) bits b t n (gramMultiplier t)
      (hashExponent q b t) (minLength q b t) := by
  let F := callbacks (show 1 < q by omega) pad C
  refine ⟨repairLaws (by omega) pad C h,hashCount q b t,?_,?_,?_⟩
  · intro l hlo _
    have hpos := (minLength_pos (b := b) (t := t) (show 1 < q by omega)).trans_le hlo
    simpa only [hashThreshold,edits,gram,← Nat.mul_assoc] using
      (hashCount_bounds (q := q) (b := b) (t := t) hpos).2
  · intro x hlo hhi hacc
    obtain ⟨H,hH⟩ := h.lookup x.length hlo hhi
    have hx : acceptedAt C pad H x.get = true := by
      simpa [F,callbacks,not_lt_of_ge hlo,hH] using hacc
    simpa [F,callbacks,hH] using rankAt_bound C pad H x.get hx
  · intro x y hlo hlen hhi hx hy he hc
    let l := x.length
    let x' : Fin l → Fin q := x.get
    let y' : Fin l → Fin q := fun i => y.get (Fin.cast hlen i)
    have hxs : List.ofFn x' = x := List.ofFn_get x
    have hys : List.ofFn y' = y := by
      apply List.ext_getElem
      · simp [l,hlen]
      · intro i hi hj
        simp [y']
    obtain ⟨H,hH⟩ := h.lookup l hlo hhi
    have ax : F.accepted (bits,x) = acceptedAt C pad H x' := by
      have aa := accepted_ofFn (show 1 < q by omega) pad C bits H hH hlo x'
      rwa [hxs] at aa
    have ay : F.accepted (bits,y) = acceptedAt C pad H y' := by
      have aa := accepted_ofFn (show 1 < q by omega) pad C bits H hH hlo y'
      rwa [hys] at aa
    have lx : F.label (bits,x) = rankAt pad H x' := by
      have hh := label_ofFn (show 1 < q by omega) pad C bits H hH x'
      rwa [hxs] at hh
    have ly : F.label (bits,y) = rankAt pad H y' := by
      have hh := label_ofFn (show 1 < q by omega) pad C bits H hH y'
      rwa [hys] at hh
    have sx := ax.symm.trans hx
    have sy := ay.symm.trans hy
    have he' := lx.symm.trans (he.trans ly)
    have hconf : Burst.WithinBursts b (2*t) (List.ofFn x') (List.ofFn y') := by simpa [hxs,hys] using hc
    have eq := rankAt_separate hq hb ht C pad d hlo H x' y' sx sy he' hconf
    rw [← hxs,← hys,eq]

#print axioms repairLaws
#print axioms sourceGuarantees

end DeletionCode.Explicit.ConcreteSource
