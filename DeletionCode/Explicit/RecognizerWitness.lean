import DeletionCode.Explicit.RecognizerRun
import DeletionCode.Explicit.WitnessTables

/-! The rules of the concrete first-event witness are small and lie in the kernel. -/

namespace DeletionCode.Explicit.Recognizer

open FieldHash LetterGraphCuts RulePatch FirstEvent

variable {ℓ q K b L Λ R s θ : ℕ}

def AllKernel (H : TernaryMatrix θ (q^L)) : Result ℓ q L s → Prop
  | .complete hs => ∀ p ∈ hs, H.mulVec p.row = 0
  | .firstEvent hs _ => ∀ p ∈ hs, H.mulVec p.row = 0

theorem run_kernel (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    (origin : Fin ℓ) (R : ℕ) (cat : List (Fin s → Borrowed.BubbleWord (Fin q) K b L))
    (fuel : ℕ) (hs : History ℓ q L s) (hk : ∀ p ∈ hs, H.mulVec p.row = 0)
    {r : Result ℓ q L s} (h : run H pad x origin R cat fuel hs = some r) :
    AllKernel H r := by
  induction fuel generalizing hs with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hc : nextRule H pad x hs cat with
    | none =>
      have hr : Result.complete hs = r := by simpa [run,hc] using h
      subst r
      exact hk
    | some words =>
      cases ha : appendRule pad x origin hs words with
      | none => simp [run,hc,ha] at h
      | some hs' =>
        obtain ⟨p,rfl,hrow⟩ := appendRule_shape pad x origin ha
        have hnew : H.mulVec p.row = 0 := hrow ▸ (nextRule_selected H pad x hs cat hc).2.1
        have hk' : ∀ a ∈ hs++[p], H.mulVec a.row = 0 := by
          intro a hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hk a hm
          · rcases List.mem_singleton.mp hm with rfl
            exact hnew
        have hn : hs.length < (hs++[p]).length := by simp
        let last : Fin (hs++[p]).length := ⟨hs.length,hn⟩
        cases he : componentEvent (PatchTable.incidence (gates (hs++[p]))) R last with
        | true =>
          have hres : Result.firstEvent (hs++[p]) last = r := by simpa [run,hc,ha,hn,last,he] using h
          subst r
          exact hk'
        | false =>
          apply ih _ hk'
          simpa [run,hc,ha,hn,last,he] using h

theorem recognize_kernel (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    {r : Result ℓ q L s}
    (h : recognize (K := K) (b := b) H pad x R = some r) :
    AllKernel H r := by
  by_cases hℓ : 0 < ℓ
  · exact run_kernel H pad x ⟨0,hℓ⟩ R _ _ [] (by simp) (by simpa [recognize,hℓ] using h)
  · have hres : Result.complete [] = r := by simpa [recognize,hℓ] using h
    subst r
    simp [AllKernel]

theorem firstEvent_witnessBounds (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    {hs : History ℓ q L s} {i : Fin hs.length} (hL : 0 < L) (hspos : 0 < s)
    (h : ResultValid H pad x K b Λ R (.firstEvent hs i)) :
    WitnessBounds (PatchTable.incidence (gates hs)) R i := by
  obtain ⟨_,_,hv,he,old,p,hbefore,heq,hi⟩ := h
  subst hs
  have hindex : i = ⟨old.length,by simp⟩ := Fin.ext hi
  subst i
  exact witnessBounds_append old p R hL hspos hv.lowWidth hv.highWidth hbefore he

theorem firstEvent_witnessEntries (H : TernaryMatrix θ (q^L)) (pad : Fin q) (x : Fin ℓ → Fin q)
    {hs : History ℓ q L s} {i : Fin hs.length} (hL : 0 < L) (hspos : 0 < s)
    (h : ResultValid H pad x K b Λ R (.firstEvent hs i)) :
    (retainedEntries hs (.inl i)).card ≤ s*(8*s*R+1) := by
  have hb := firstEvent_witnessBounds H pad x hL hspos h
  rw [retainedEntries_card]
  simpa only [Nat.mul_comm s] using Nat.mul_le_mul_right s hb.1

#print axioms recognize_kernel
#print axioms firstEvent_witnessEntries

end DeletionCode.Explicit.Recognizer
