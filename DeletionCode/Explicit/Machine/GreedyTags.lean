import DeletionCode.Explicit.GreedyTags
import DeletionCode.Explicit.Machine.EditBall
import DeletionCode.Explicit.Machine.WordEnumeration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! The greedy tag scan, with a polynomial bound on its input enumeration. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private abbrev codeEncoding (q : ℕ) := encList (wordEncoding q)

private def retain {q : ℕ} (b s : ℕ) (w : QWord q) (xs : List (QWord q)) :=
  xs.filter fun y => decide (y ∉ editBall b s w)

private theorem retain_polyTime {q : ℕ} (b s : ℕ) :
    ComputableInPolyTime (fun p : QWord q × List (QWord q) => retain b s p.1 p.2)
      (encPair (wordEncoding q) (codeEncoding q)) (codeEncoding q) := by
  unfold retain
  apply filterWithInput (snd _ _)
  exact decide_not (decide_mem ((editBall_polyTime b s).comp (fst _ _).fst') (snd _ _))

private abbrev ScanState (q : ℕ) := List (QWord q) × List (QWord q)

private abbrev scanEncoding (q : ℕ) := encPair (codeEncoding q) (codeEncoding q)

private def scanStep {q : ℕ} (b s : ℕ) (p : ScanState q) : ScanState q :=
  if p.2.isEmpty then p
  else (p.2.headD [] :: p.1, retain b s (p.2.headD []) p.2.tail)

private theorem scanStep_polyTime {q : ℕ} (b s : ℕ) :
    ComputableInPolyTime (scanStep (q := q) b s) (scanEncoding q) (scanEncoding q) := by
  have hrest := snd (codeEncoding q) (codeEncoding q)
  have hhead := (ComputableInPolyTime.headD (encA := wordEncoding q) []).comp hrest
  have htail := (listTail (wordEncoding q)).comp hrest
  unfold scanStep scanEncoding
  exact ((listIsEmpty' (wordEncoding q)).comp hrest).ite id'
    (((cons (wordEncoding q)).comp (hhead.prod (fst _ _))).prod
      ((retain_polyTime b s).comp (hhead.prod htail)))

private theorem scanStep_size {q : ℕ} (b s : ℕ) (p : ScanState q) :
    (codeEncoding q (scanStep b s p).1).length + (codeEncoding q (scanStep b s p).2).length ≤
      (codeEncoding q p.1).length + (codeEncoding q p.2).length := by
  rcases p with ⟨done, _ | ⟨w, xs⟩⟩
  · simp [scanStep]
  · have hf := length_encList_sublist (wordEncoding q)
      (List.filter_sublist (p := fun y => decide (y ∉ editBall b s w)) (l := xs))
    simp only [scanStep, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
      List.tail_cons, codeEncoding, encList_cons, List.length_append]
    unfold retain
    omega

private theorem scanStep_preserves {q : ℕ} (b s fuel : ℕ) (p : ScanState q) :
    (scanStep b s p).1.reverse ++ DeletionCode.Explicit.scan b s fuel (scanStep b s p).2 =
      p.1.reverse ++ DeletionCode.Explicit.scan b s (fuel + 1) p.2 := by
  rcases p with ⟨done, _ | ⟨w, xs⟩⟩
  · cases fuel <;> rfl
  · change (w :: done).reverse ++ DeletionCode.Explicit.scan b s fuel (retain b s w xs) =
      done.reverse ++ (w :: DeletionCode.Explicit.scan b s fuel (retain b s w xs))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem scan_polyTime {q : ℕ} (b s : ℕ) :
    ComputableInPolyTime (fun xs : List (QWord q) => DeletionCode.Explicit.scan b s xs.length xs)
      (codeEncoding q) (codeEncoding q) := by
  let inv (xs : List (QWord q)) (i : ℕ) (p : ScanState q) :=
    ((codeEncoding q p.1).length + (codeEncoding q p.2).length ≤ (codeEncoding q xs).length) ∧
    (p.1.reverse ++ DeletionCode.Explicit.scan b s (xs.length - i) p.2 = DeletionCode.Explicit.scan b s xs.length xs)
  have hsize : PolyBounded (fun xs : List (QWord q) => (codeEncoding q xs).length)
      (fun xs => 2 * (codeEncoding q xs).length + 1) :=
    ((PolyBounded.const 2).mul PolyBounded.self).add (PolyBounded.const 1)
  obtain ⟨hmachine, hcorrect⟩ := iterate_spec (length_list (wordEncoding q))
    ((const []).prod id') (scanStep_polyTime b s) inv
    (fun xs => by simp [inv, codeEncoding])
    (fun xs i p hi h => by
      refine ⟨(scanStep_size b s p).trans h.1, ?_⟩
      have hcount : xs.length - (i + 1) + 1 = xs.length - i := by omega
      exact (scanStep_preserves b s (xs.length - (i + 1)) p).trans (hcount ▸ h.2))
    hsize (fun xs i p hi h => by
      change (scanEncoding q p).length ≤ _
      rw [length_encPair]
      have hmass := h.1
      omega)
  have hresult := (listReverse (wordEncoding q)).comp hmachine.fst'
  refine hresult.of_enc_eq (fun xs => congrArg (codeEncoding q) ?_)
  have h := (hcorrect xs).2
  simp only [Nat.sub_self] at h
  exact (show _ = _ from h.symm.trans (List.append_nil _))

/-- Compute the original greedy scan for a polynomially bounded lexicographic enumeration. -/
theorem greedyTags_polyTime_of_length {α : Type} {enc : α ↪ List Bool} {m : α → ℕ}
    {q : ℕ} (hq : 2 ≤ q) (b s : ℕ) (hm : ComputableInPolyTime m enc encUnary)
    (hcount : PolyBounded (fun a => (enc a).length) (fun a => q ^ m a)) :
    ComputableInPolyTime (fun a => greedyTags q b s (m a)) enc (encList (wordEncoding q)) :=
  (scan_polyTime b s).comp (wordsOfLength_polyTime hq hm hcount)

/-- One fixed machine returns the exact greedy tag list for `m = Nat.log q N`,
where `N` is given in unary. -/
theorem greedyTags_polyTime {q : ℕ} (hq : 2 ≤ q) (b s : ℕ) :
    ComputableInPolyTime (fun N => greedyTags q b s (Nat.log q N))
      encUnary (encList (wordEncoding q)) := by
  refine greedyTags_polyTime_of_length hq b s (unary_log_const q) ?_
  refine PolyBounded.of_forall_le 1 1 (fun N => ?_)
  simp only [encUnary_apply, List.length_replicate, pow_one, one_mul]
  by_cases hN : N = 0
  · simp [hN]
  · exact (Nat.pow_log_le_self q hN).trans (Nat.le_succ N)

#print axioms greedyTags_polyTime

end DeletionCode.Explicit.Machine
