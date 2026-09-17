import DeletionCode.ConcreteModel

/-!
Executable initialization from one recorded position per root. Root positions
are obtained from actual occurrences in x; no successful load is assumed.
The resulting memory realizes the scheduler's initial state.
-/
namespace DeletionCode.ConcreteInitialization

open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel

variable {B : Type*} {x : Letters} {n k : ℕ}

def ValidRoots (M : Model B x n k) (records : List (B × ℕ)) : Prop :=
  ∀ b a, (b, a) ∈ records → a + negativeLength k (M.header b) ≤ n ∧
    Agree x a (negativePath k (M.header b) (M.long b)) 0 (negativeLength k (M.header b))

/-- Loading valid root records succeeds and preserves every previously stored bit. -/
theorem loadRoots_correct [DecidableEq B] (M : Model B x n k)
    (records : List (B × ℕ)) (mem : Bank B) (hs : M.Sound mem)
    (hvalid : ValidRoots M records) :
    ∃ result, loadRoots x n k M.header mem records = some result ∧ M.Sound result ∧
      (∀ b, Extends (mem b) (result b)) ∧
      (∀ b a, (b, a) ∈ records →
        WindowKnown (result b) 0 (negativeLength k (M.header b))) := by
  induction records generalizing mem with
  | nil =>
    refine ⟨mem, rfl, hs, ?_, ?_⟩
    · intro b j bit hj
      exact hj
    · intro b a hmem
      contradiction
  | cons record rest ih =>
    rcases record with ⟨b, a⟩
    have hocc := hvalid b a (by simp)
    obtain ⟨t, ht, hsound, hext, hread⟩ := ConcreteFill.loadRoot_correct
      x (negativePath k (M.header b) (M.long b)) n a
      (negativeLength k (M.header b)) (mem b) (negativeLength k (M.header b))
      (hs b) hocc.1 (by omega) hocc.2
    have hnext : M.Sound (Function.update mem b t) := M.sound_update mem hs b t hsound
    have htail : ValidRoots M rest := fun c j hj => hvalid c j (by simp [hj])
    obtain ⟨result, hresult, hrsound, hrext, hrknown⟩ := ih (Function.update mem b t) hnext htail
    have hstep : ∀ c, Extends (mem c) (Function.update mem b t c) := by
      intro c
      by_cases hcb : c = b
      · subst c
        simpa using hext
      · have hbc : b ≠ c := Ne.symm hcb
        intro j bit hj
        simpa [Function.update, hcb, hbc] using hj
    refine ⟨result, ?_, hrsound, ?_, ?_⟩
    · simpa only [loadRoots, ht, Option.bind_some] using hresult
    · intro c j bit hj
      exact hrext c j bit (hstep c j bit hj)
    · intro c j hj
      rcases List.mem_cons.mp hj with heq | hrest
      · cases heq
        apply windowKnown_mono (Function.update mem b t b) (result b) 0
          (negativeLength k (M.header b)) (hrext b)
        simpa using (show WindowKnown t 0 (negativeLength k (M.header b)) from ⟨_, hread⟩)
      · exact hrknown c j hrest

noncomputable def rootCount [Fintype B] (M : Model B x n k) : ℕ := by
  classical
  exact (Finset.univ.filter M.schedule.root).card

/-- Exactly one actual x-position is recorded for every marked root. -/
theorem root_records_exist [Fintype B] (M : Model B x n k) :
    ∃ records : List (B × ℕ), records.length = rootCount M ∧ ValidRoots M records ∧
      (∀ b, M.schedule.root b → ∃ a, (b, a) ∈ records) := by
  classical
  let roots := Finset.univ.filter M.schedule.root
  let pos : B → ℕ := fun b => if hr : M.schedule.root b then
    Classical.choose (M.root_occurrence b hr) else 0
  let records := roots.toList.map (fun b => (b, pos b))
  have hpos : ∀ b, M.schedule.root b →
      pos b + negativeLength k (M.header b) ≤ n ∧
      Agree x (pos b) (negativePath k (M.header b) (M.long b)) 0
        (negativeLength k (M.header b)) := by
    intro b hb
    dsimp [pos]
    rw [dite_eq_left hb]
    exact Classical.choose_spec (M.root_occurrence b hb)
  refine ⟨records, ?_, ?_, ?_⟩
  · simp [records, roots, rootCount]
  · intro b a hmem
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp hmem
    have hroot : M.schedule.root c := by simpa [roots] using hc
    have hcpos := hpos c hroot
    cases heq
    exact hcpos
  · intro b hb
    refine ⟨pos b, List.mem_map.mpr ⟨b, ?_, rfl⟩⟩
    simpa [roots] using hb

/-- Root loading constructs the actual invariant for the abstract initial state. -/
theorem initialization_exists [Fintype B] [DecidableEq B] (M : Model B x n k) :
    ∃ records mem, records.length = rootCount M ∧
      loadRoots x n k M.header (fun _ => empty) records = some mem ∧
      M.Invariant (Recovery.initial M.schedule) mem := by
  classical
  obtain ⟨records, hlength, hvalid, hroots⟩ := root_records_exist M
  have hempty : M.Sound (fun _ => empty) := fun b =>
    empty_sound (negativePath k (M.header b) (M.long b)) (negativeLength k (M.header b))
  obtain ⟨mem, hload, hsound, _, hknown⟩ := loadRoots_correct M records (fun _ => empty) hempty hvalid
  have hrootKnown : ∀ b, M.schedule.root b →
      WindowKnown (mem b) 0 (negativeLength k (M.header b)) := by
    intro b hb
    obtain ⟨a, ha⟩ := hroots b hb
    exact hknown b a ha
  refine ⟨records, mem, hlength, hload, Recovery.initial_wellFormed M.schedule, hsound, ?_⟩
  constructor
  · intro b w hseed
    by_cases hb : M.schedule.root b
    · have hw : w = 0 := by simpa [Recovery.initial, hb] using hseed.symm
      subst w
      have hL : windowLength k ≤ negativeLength k (M.header b) := by
        simpa [windowStart] using M.window_bound b 0
      have hk : k ≤ negativeLength k (M.header b) := by
        unfold windowLength at hL
        omega
      obtain ⟨bits, hread⟩ := windowKnown_subblock (mem b) 0
        (negativeLength k (M.header b)) 0 k (hrootKnown b hb) (by omega) (by omega)
      refine ⟨0, bits, by omega, ?_⟩
      simpa [windowStart] using hread
    · simp [Recovery.initial, hb] at hseed
  · intro b w hdone
    have hb : M.schedule.root b := by simpa [Recovery.State.Done, Recovery.initial] using hdone
    exact windowKnown_subblock (mem b) 0 (negativeLength k (M.header b))
      (windowStart (negativeExtra k (M.header b)) w) (windowLength k)
      (hrootKnown b hb) (by omega) (by simpa using M.window_bound b w)

#print axioms loadRoots_correct
#print axioms root_records_exist
#print axioms initialization_exists

end DeletionCode.ConcreteInitialization
