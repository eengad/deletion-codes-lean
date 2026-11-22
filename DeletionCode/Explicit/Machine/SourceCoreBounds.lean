import DeletionCode.Explicit.Machine.SourceCoreCheck

/-! The catalogue counts only original positions from declared final gates. -/
namespace DeletionCode.Explicit.Machine.SourceCoreBounds

open CoreWeight ReplayGrammar ReplayEntry LetterSequence
open private prefixWord readThree from DeletionCode.Explicit.ReplayGrammar
open private boundsChecked finalEntries originalPositions belongs from DeletionCode.Explicit.CoreReplay

variable {q b t E L ℓ r₀ : ℕ}

private theorem entry_bound {c : EntryCode E L b q} {d : DecodedEntry q}
    (h : decodeEntry c = some d) :
    d.entry.negativeLength ≤ 2*L+b ∧ d.entry.positiveLength ≤ 2*L+b := by
  unfold decodeEntry at h
  dsimp only at h
  split at h
  · contradiction
  next hfield =>
    simp only [not_or,Nat.not_le,Nat.not_lt] at hfield
    split at h
    next hu =>
      split at h
      next hv =>
        cases hr : readThree E L c.1 with
        | none => simp [hr] at h
        | some refs =>
          simp only [hr,bind,Option.bind] at h
          split at h
          · cases h
            simp only [Entry.negativeLength,Entry.positiveLength,prefixWord,List.length_ofFn]
            rcases hfield with ⟨_,_,hl,hr,_,_⟩
            omega
          · contradiction
      · contradiction
    · contradiction

private theorem description_bound {c : DescriptionCode E L b q} {ds : List (DecodedEntry q)}
    (h : decodeDescription c = some ds) (d : DecodedEntry q) (hd : d ∈ ds) :
    d.entry.negativeLength ≤ 2*L+b ∧ d.entry.positiveLength ≤ 2*L+b := by
  unfold decodeDescription at h
  rw [← SourceLists.collect_map] at h
  unfold SourceLists.collect at h
  split at h
  · cases h
    simp only [List.mem_flatMap,List.mem_map] at hd
    obtain ⟨o,⟨code,_,rfl⟩,hm⟩ := hd
    have hc : decodeEntry code = some d := by
      cases he : decodeEntry code <;> simp_all
    exact entry_bound hc
  · contradiction

private theorem lifts_bound {α : Type} {L N : ℕ} {anchors : ℕ → Option (Fin ℓ)}
    {done out : Array (Completed ℓ α)} {entries : List (Entry α)}
    (h : RecordedHistory L anchors done entries out)
    (he : ∀ e ∈ entries, e.negativeLength ≤ N ∧ e.positiveLength ≤ N)
    (hd : ∀ p ∈ done.toList, p.negative.1 ≤ N ∧ p.positive.1 ≤ N) :
    ∀ p ∈ out.toList, p.negative.1 ≤ N ∧ p.positive.1 ≤ N := by
  induction h with
  | done => exact hd
  | @step done out e es neg h tail ih =>
    refine ih (fun a ha => he a (List.mem_cons_of_mem _ ha)) ?_
    intro p hp
    rw [Array.toList_push,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hd p hp
    · exact he e List.mem_cons_self

private theorem count_union {α β : Type} (xs : List α) (keys : List β) (marked : α → Bool)
    (owns : α → β → Bool)
    (h : ∀ x ∈ xs, marked x = true → ∃ k ∈ keys, owns x k = true) :
    (xs.filter marked).length ≤
      (keys.map fun k => (xs.filter (fun d => marked d && owns d k)).length).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hi := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    let cnt := fun k => (xs.filter (fun d => marked d && owns d k)).length
    let add := fun k => if marked a && owns a k then 1 else 0
    change (xs.filter marked).length ≤ (keys.map cnt).sum at hi
    have ha (ks : List β) : (ks.map fun k => cnt k + add k).sum =
        (ks.map cnt).sum + (ks.map add).sum := by
      induction ks with
      | nil => rfl
      | cons c keys ih => simp only [List.map_cons,List.sum_cons,ih]; omega
    have hj : (keys.map fun k => ((a::xs).filter (fun d => marked d && owns d k)).length) =
        keys.map (fun k => cnt k + add k) := by
      apply List.map_congr_left
      intro k hk
      cases hk : marked a && owns a k <;>
        simp only [cnt,add,List.filter_cons,hk,Bool.false_eq_true,if_false,if_true,List.length_cons,Nat.add_zero]
    rw [hj,ha keys]
    cases hm : marked a with
    | false => simp only [List.filter_cons,hm,Bool.false_eq_true,if_false]; omega
    | true =>
      obtain ⟨k,hk,ho⟩ := h a List.mem_cons_self hm
      have hb : 1 ∈ keys.map add := List.mem_map.mpr ⟨k,hk,by simp [add,hm,ho]⟩
      have hc := List.le_sum_of_mem hb
      simp only [List.filter_cons,hm,if_true,List.length_cons]
      omega

private theorem count_final (ds : List (DecodedEntry q)) (keys : Finset (Fin E))
    (s : ℕ) (h : boundsChecked s ds keys = true) :
    (ds.filter (·.finalBubble)).length ≤ keys.card*s := by
  unfold boundsChecked at h
  obtain ⟨hc,hk⟩ := Bool.and_eq_true_iff.mp h
  have he := count_union ds keys.sort (·.finalBubble)
    (fun d id => d.entry.rule == id.val) (fun d hd hf => by
      have hz := List.all_eq_true.mp hk d hd
      simp only [hf,Bool.not_true,Bool.false_or] at hz
      exact List.any_eq_true.mp hz)
  have heq : (keys.sort.map (fun id => (ds.filter (belongs id.val)).length)) =
      List.replicate keys.card s := by
    rw [← Finset.length_sort (s := keys) (· ≤ ·),← List.map_const']
    apply List.map_congr_left
    intro i hi
    exact decide_eq_true_eq.mp (List.all_eq_true.mp hc i hi)
  change (ds.filter (·.finalBubble)).length ≤ (keys.sort.map (fun id => (ds.filter (belongs id.val)).length)).sum at he
  simpa [heq,List.sum_replicate,Nat.mul_comm] using he

private theorem zip_filter_le {α β : Type} (xs : List α) (ys : List β) (keep : α → Bool) :
    ((xs.zip ys).filter (fun p => keep p.1)).length ≤ (xs.filter keep).length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have h := ih ys
      cases hk : keep a <;> simp [List.filter_cons,hk,h]

private theorem original_card (w : StoredLift ℓ (Fin q)) :
    (originalPositions w).card ≤ w.1 := by
  let names (i : Fin w.1) := ((w.2.letters i).position.toList).toFinset
  have he : originalPositions w = (Finset.univ : Finset (Fin w.1)).biUnion names := by
    ext i
    simp only [originalPositions,Finset.mem_filter,Finset.mem_biUnion,Finset.mem_univ,true_and,
      names,List.mem_toFinset,Option.mem_toList,Lift.mem_positions]
    exact ⟨fun ⟨j,p,he,hp⟩ => ⟨j,Fin.ext hp ▸ he⟩,fun ⟨j,hj⟩ => ⟨j,i,hj,rfl⟩⟩
  rw [he]
  have hc := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin w.1)) names 1 (by
    intro i _
    cases h : (w.2.letters i).position <;> simp [names,h])
  simpa using hc

private theorem support_bound {r : ℕ} (m : Materialized ℓ q E r) (N : ℕ)
    (h : ∀ p ∈ m.entries, p.2.negative.1 ≤ N ∧ p.2.positive.1 ≤ N) :
    m.support.card ≤ (finalEntries m).length*(2*N) := by
  classical
  let supportOf := fun p : DecodedEntry q × Completed ℓ (Fin q) =>
    originalPositions p.2.negative ∪ originalPositions p.2.positive
  have he : m.support = (finalEntries m).toFinset.biUnion supportOf := by
    ext i
    simp only [Materialized.mem_support,Finset.mem_biUnion,List.mem_toFinset,finalEntries,List.mem_filter,
      supportOf,Finset.mem_union,originalPositions,Finset.mem_univ,true_and]
    aesop
  rw [he]
  apply (Finset.card_biUnion_le_card_mul _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ (List.toFinset_card_le _))
  intro p hp
  have hm := (List.mem_filter.mp (List.mem_toFinset.mp hp)).1
  have hn := (original_card p.2.negative).trans (h p hm).1
  have hv := (original_card p.2.positive).trans (h p hm).2
  exact (Finset.card_union_le _ _).trans (by omega)

theorem materialize_support_le (k : ReplaySlot ℓ q E L b t r₀)
    (m : Materialized ℓ q E (k.1.val+1)) (hm : materialize k = some m) :
    m.support.card ≤ 2*t*(k.1.val+1)*(4*L+2*b) := by
  unfold materialize at hm
  simp only [bind, Option.bind] at hm
  cases hc : unpackDescription k.2.1 with
  | none => simp [hc] at hm
  | some c =>
    cases hd : decodeDescription c with
    | none => simp [hc,hd] at hm
    | some ds =>
      simp only [hc,hd] at hm
      split at hm
      next hkeys =>
        split at hm
        next hb =>
          split at hm
          next hp =>
            cases ha : RulePatch.unpackAnchors (patchKeys E ds) k.2.2 with
            | none => simp [ha] at hm
            | some anchors =>
              cases hr : replay L (anchorLookup (patchKeys E ds) anchors) (ds.map DecodedEntry.entry) with
              | none => simp [ha,hr] at hm
              | some out =>
                simp only [ha,hr,Option.bind_some,Option.some.injEq] at hm
                subst m
                have hl := lifts_bound (replay_eq_some_iff.mp hr)
                  (fun e he => by obtain ⟨d,hm,rfl⟩ := List.mem_map.mp he; exact description_bound hd d hm)
                  (by simp)
                have hs := support_bound ⟨ds.zip out.toList,finalRuleKeys E ds,hkeys⟩ (2*L+b)
                  (fun p hm => hl p.2 (List.of_mem_zip hm).2)
                have hf := (zip_filter_le ds out.toList (·.finalBubble)).trans
                  (count_final ds (finalRuleKeys E ds) (2*t) hb)
                rw [hkeys] at hf
                calc
                  _ ≤ ((ds.zip out.toList).filter (fun p => p.1.finalBubble)).length*(2*(2*L+b)) := hs
                  _ ≤ _ := by
                    convert Nat.mul_le_mul_right (2*(2*L+b)) hf using 1
                    ring
          · contradiction
        · contradiction
      · contradiction

#print axioms materialize_support_le

end DeletionCode.Explicit.Machine.SourceCoreBounds
