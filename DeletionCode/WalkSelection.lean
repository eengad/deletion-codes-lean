import DeletionCode.ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
A finite greedy scan of the actual step indices of a closed walk. Before a
stop, the selected earlier steps are independent, satisfy the chosen cutoff,
and represent every earlier step up to sign. The representation is causal:
its selected index is no later than the step it represents. If the scan never
stops, closed-walk parity contradicts an odd length.
-/
namespace DeletionCode.WalkSelection

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

def walkStep (p : Fin (m + 1) → V) (i : Fin m) : V := p i.succ - p i.castSucc

def selectedSpan (step : Fin m → V) (S : Finset (Fin m)) : Submodule ℚ V :=
  Submodule.span ℚ (step '' (S : Set (Fin m)))

def SignedMember (step : Fin m → V) (S : Finset (Fin m)) (v : V) : Prop :=
  ∃ r ∈ S, v = step r ∨ v = -step r

theorem selected_mem_span (step : Fin m → V) (S : Finset (Fin m))
    (r : Fin m) (hr : r ∈ S) : step r ∈ selectedSpan step S :=
  Submodule.subset_span ⟨r, hr, rfl⟩

theorem signed_mem_span (step : Fin m → V) (S : Finset (Fin m))
    (v : V) (hv : SignedMember step S v) : v ∈ selectedSpan step S := by
  obtain ⟨r, hr, h | h⟩ := hv
  · rw [h]
    exact selected_mem_span step S r hr
  · rw [h]
    exact (selectedSpan step S).neg_mem (selected_mem_span step S r hr)

/-- The concrete invariant after scanning the indices smaller than n. -/
structure ScanState (step : Fin m → V) (Good : Finset (Fin m) → Prop)
    (n : ℕ) (S : Finset (Fin m)) : Prop where
  before : ∀ r ∈ S, r.val < n
  good : Good S
  independent : LinearIndepOn ℚ step (S : Set (Fin m))
  covered : ∀ j : Fin m, j.val < n →
    ∃ r ∈ S, r.val ≤ j.val ∧ (step j = step r ∨ step j = -step r)

theorem ScanState.earlier_span {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (h : ScanState step Good n S)
    (j : Fin m) (hj : j.val < n) : step j ∈ selectedSpan step S := by
  obtain ⟨r, hr, _, heq⟩ := h.covered j hj
  exact signed_mem_span step S (step j) ⟨r, hr, heq⟩

theorem independent_insert {step : Fin m → V} {S : Finset (Fin m)}
    (hs : LinearIndepOn ℚ step (S : Set (Fin m))) (i : Fin m)
    (hi : step i ∉ selectedSpan step S) :
    LinearIndepOn ℚ step ((insert i S : Finset (Fin m)) : Set (Fin m)) := by
  simpa only [Finset.coe_insert] using hs.insert hi

private theorem ScanState.skip {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (hs : ScanState step Good n S)
    (i : Fin m) (hi : i.val = n) (hsigned : SignedMember step S (step i)) :
    ScanState step Good (n + 1) S := by
  refine ⟨fun r hr => by have := hs.before r hr; omega, hs.good, hs.independent, ?_⟩
  intro j hj
  by_cases hbefore : j.val < n
  · exact hs.covered j hbefore
  · have hji : j = i := Fin.ext (by omega)
    subst j
    obtain ⟨r, hr, heq⟩ := hsigned
    exact ⟨r, hr, by have := hs.before r hr; omega, heq⟩

private theorem ScanState.append {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (hs : ScanState step Good n S)
    (i : Fin m) (hi : i.val = n) (hout : step i ∉ selectedSpan step S)
    (hgood : Good (insert i S)) : ScanState step Good (n + 1) (insert i S) := by
  refine ⟨?_, hgood, independent_insert hs.independent i hout, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with hri | hrS
    · subst r; omega
    · have := hs.before r hrS
      omega
  · intro j hj
    by_cases hbefore : j.val < n
    · obtain ⟨r, hr, hle, heq⟩ := hs.covered j hbefore
      exact ⟨r, Finset.mem_insert_of_mem hr, hle, heq⟩
    · have hji : j = i := Fin.ext (by omega)
      subst j
      exact ⟨i, Finset.mem_insert_self i S, le_rfl, Or.inl rfl⟩

/-- Either a new relation appears, or an independent append first violates
the chosen cutoff. In both cases S consists of genuinely earlier step indices. -/
def Stopped (step : Fin m → V) (Good : Finset (Fin m) → Prop) : Prop :=
  ∃ (i : Fin m) (S : Finset (Fin m)),
    ScanState step Good i.val S ∧ ¬ SignedMember step S (step i) ∧
      (step i ∈ selectedSpan step S ∨
        (step i ∉ selectedSpan step S ∧
          LinearIndepOn ℚ step ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
          ¬ Good (insert i S)))

/-- The stopping alternative is constructed by scanning a finite prefix.
No scan trace or final selected family is an input to this theorem. -/
theorem scan_prefix (step : Fin m → V) (Good : Finset (Fin m) → Prop)
    (hgood : Good ∅) (n : ℕ) (hn : n ≤ m) :
    Stopped step Good ∨ ∃ S, ScanState step Good n S := by
  classical
  induction n with
  | zero =>
    right
    refine ⟨∅, ?_, hgood, ?_, ?_⟩
    · intro r hr
      simp at hr
    · simp
    · intro j hj
      omega
  | succ n ih =>
    rcases ih (by omega) with hstop | ⟨S, hs⟩
    · exact Or.inl hstop
    · let i : Fin m := ⟨n, by omega⟩
      by_cases hsigned : SignedMember step S (step i)
      · exact Or.inr ⟨S, hs.skip i rfl hsigned⟩
      · by_cases hspan : step i ∈ selectedSpan step S
        · exact Or.inl ⟨i, S, hs, hsigned, Or.inl hspan⟩
        · have hind := independent_insert hs.independent i hspan
          by_cases hnewgood : Good (insert i S)
          · exact Or.inr ⟨insert i S, hs.append i rfl hspan hnewgood⟩
          · exact Or.inl ⟨i, S, hs, hsigned, Or.inr ⟨hspan, hind, hnewgood⟩⟩

/-- An odd closed walk must trigger one of the two actual scan stopping cases. -/
theorem odd_closed_walk_stops (p : Fin (m + 1) → V)
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    Stopped (walkStep p) Good := by
  classical
  rcases scan_prefix (walkStep p) Good hgood m le_rfl with hstop | ⟨S, hs⟩
  · exact hstop
  · let label : Fin m → S := fun j =>
      ⟨Classical.choose (hs.covered j j.isLt),
        (Classical.choose_spec (hs.covered j j.isLt)).1⟩
    have hsteps : ∀ j : Fin m,
        p j.succ - p j.castSucc = walkStep p (label j).val ∨
        p j.succ - p j.castSucc = -walkStep p (label j).val :=
      fun j => (Classical.choose_spec (hs.covered j j.isLt)).2.2
    exact False.elim (ClosedWalk.not_odd_signed_independent_closed_walk
      (fun r : S => walkStep p r.val) hs.independent p label hclosed hsteps hodd)

/-- A coordinate unchanged by all earlier actual steps has its starting value. -/
theorem coordinate_unchanged_before {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (n : ℕ) (hn : n ≤ m) (h : H)
    (hzero : ∀ j : Fin m, j.val < n → walkStep p j h = 0) :
    p ⟨n, by omega⟩ h = p 0 h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (by omega) (fun j hj => hzero j (by omega))
    let j : Fin m := ⟨n, by omega⟩
    have hstep := hzero j (by dsimp [j]; omega)
    change p ⟨n + 1, by omega⟩ h - p ⟨n, by omega⟩ h = 0 at hstep
    exact (sub_eq_zero.mp hstep).trans hprev

/-- Generating provenance for the actual selected step indices, in their
original chronological order. -/
def GeneratingSelected {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (S : Finset (Fin m)) : Prop :=
  ∀ i ∈ S, ∀ h, walkStep p i h = -1 →
    p 0 h ≠ 0 ∨ ∃ r ∈ S, r.val < i.val ∧ walkStep p r h ≠ 0

/-- Boolean endpoints and the causal scan invariant derive generation. -/
theorem ScanState.generating {H : Type*} {p : Fin (m + 1) → H → ℚ}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep p) Good n S)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j)) : GeneratingSelected p S := by
  classical
  intro i hi h hneg
  by_cases hbase : p 0 h = 0
  · right
    by_contra hnone
    have hselected : ∀ r ∈ S, r.val < i.val → walkStep p r h = 0 := by
      intro r hr hri
      by_contra hrzero
      exact hnone ⟨r, hr, hri, hrzero⟩
    have hzero : ∀ j : Fin m, j.val < i.val → walkStep p j h = 0 := by
      intro j hji
      obtain ⟨r, hr, hrj, heq⟩ := hs.covered j (by have := hs.before i hi; omega)
      have hrzero := hselected r hr (by omega)
      rcases heq with heq | heq
      · exact (congrFun heq h).trans hrzero
      · have hcoord := congrFun heq h
        simpa only [Pi.neg_apply, hrzero, neg_zero] using hcoord
    have hsame := coordinate_unchanged_before p i.val (by have := i.isLt; omega) h hzero
    change p i.castSucc h = p 0 h at hsame
    have hpone := WitnessAlgebra.negative_step_source (p i.castSucc) (p i.succ)
      (hp i.castSucc) (hp i.succ) h hneg
    exact zero_ne_one (hbase.symm.trans (hsame.symm.trans hpone))
  · exact Or.inl hbase

/-- A bad independent append is still generating; the cutoff is irrelevant
to the Boolean provenance argument. -/
theorem ScanState.generating_after_append {H : Type*} {p : Fin (m + 1) → H → ℚ}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep p) Good n S)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j))
    (i : Fin m) (hi : i.val = n) (hout : walkStep p i ∉ selectedSpan (walkStep p) S) :
    GeneratingSelected p (insert i S) := by
  have htrue : ScanState (walkStep p) (fun _ => True) n S :=
    ⟨hs.before, trivial, hs.independent, hs.covered⟩
  exact (htrue.append i hi hout trivial).generating hp

/-- The stopping dichotomy together with derived independence and generating
provenance, using the actual Boolean walk and chronological step indices. -/
theorem odd_boolean_closed_walk_stops {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j))
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    ∃ (i : Fin m) (S : Finset (Fin m)),
      ScanState (walkStep p) Good i.val S ∧ GeneratingSelected p S ∧
      ¬ SignedMember (walkStep p) S (walkStep p i) ∧
        (walkStep p i ∈ selectedSpan (walkStep p) S ∨
          (walkStep p i ∉ selectedSpan (walkStep p) S ∧
            LinearIndepOn ℚ (walkStep p) ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
            ¬ Good (insert i S) ∧ GeneratingSelected p (insert i S))) := by
  obtain ⟨i, S, hs, hnew, hstop⟩ := odd_closed_walk_stops p Good hgood hclosed hodd
  refine ⟨i, S, hs, hs.generating hp, hnew, ?_⟩
  rcases hstop with hrel | ⟨hout, hind, hbad⟩
  · exact Or.inl hrel
  · exact Or.inr ⟨hout, hind, hbad, hs.generating_after_append hp i rfl hout⟩

#print axioms independent_insert
#print axioms scan_prefix
#print axioms odd_closed_walk_stops
#print axioms coordinate_unchanged_before
#print axioms ScanState.generating
#print axioms odd_boolean_closed_walk_stops

end DeletionCode.WalkSelection
