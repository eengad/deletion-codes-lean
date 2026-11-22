import DeletionCode.Explicit.FamilyInjective
import DeletionCode.Explicit.BucketBalance

/-! Executable bucket lists, counted by the balance potential. -/

namespace DeletionCode.Explicit.BubbleFamilies

open FieldHash

variable {q K b L Λ θ : ℕ}

private theorem words_nodup (q : ℕ) (a : ℕ) : (wordsOfLength q a).Nodup := by
  induction a with
  | zero => simp [wordsOfLength]
  | succ a ih =>
    rw [wordsOfLength,List.nodup_flatMap]
    refine ⟨fun i _ => ih.map (fun _ _ h => (List.cons.inj h).2),?_⟩
    apply (List.nodup_finRange q).imp
    intro i j h word hw hq
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hw
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hq
    exact h (List.cons.inj (hu.trans hv.symm)).1

theorem members_nodup (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) :
    (s.members K b L Λ pad).Nodup := by
  unfold Shape.members
  apply (words_nodup q _).filterMap
  intro u v pair hu hv
  cases h₁ : s.member K b L Λ pad u with
  | none => simp [h₁] at hu
  | some a =>
    cases h₂ : s.member K b L Λ pad v with
    | none => simp [h₂] at hv
    | some b =>
      have hpair : (u,a) = (v,b) := by
        have hleft : (u,a) = pair := by simpa [h₁] using hu
        have hright : (v,b) = pair := by simpa [h₂] using hv
        exact hleft.trans hright.symm
      exact congrArg Prod.fst hpair

private theorem vectors_nodup (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) (hL : 1 ≤ L) :
    ((s.members K b L Λ pad).map (fun w => vector pad w.2)).Nodup := by
  apply (members_nodup s K b L Λ pad).map_on
  intro x hx y hy he
  have hmx := ((mem_members s K b L Λ pad x.1 x.2).mp hx).2
  have hmy := ((mem_members s K b L Λ pad y.1 y.2).mp hy).2
  have h := member_vector_injective s pad hL hmx hmy he
  exact Prod.ext h (Option.some.inj (hmx.symm.trans (h.symm ▸ hmy)))

theorem vectors_card (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) (hL : 1 ≤ L) :
    (s.vectors K b L Λ pad).card = (s.members K b L Λ pad).length := by
  rw [Shape.vectors,List.toFinset_card_of_nodup (vectors_nodup s K b L Λ pad hL),List.length_map]

theorem shapeCounts_add (s : Shape q) : s.originalCount+s.freshCount = s.fresh.length := by
  unfold Shape.originalCount Shape.freshCount
  induction s.fresh with
  | nil => simp
  | cons a as ih => cases a <;> simp <;> omega

theorem member_originalCount_lower (s : Shape q) (K b L Λ : ℕ) (pad : Fin q)
    (hne : (s.members K b L Λ pad).length ≠ 0) :
    L-Λ ≤ s.originalCount := by
  let : Inhabited (Fin q) := ⟨pad⟩
  have h : s.members K b L Λ pad ≠ [] := fun he => hne (by simp [he])
  obtain ⟨⟨x,w⟩,hm⟩ := List.exists_mem_of_ne_nil _ h
  have hmem := ((mem_members s K b L Λ pad x w).mp hm).2
  obtain ⟨hf,hΛ,hcat⟩ := member_data s K b L Λ pad hmem
  have hsize := hcat.length_lower 0 false
  change L ≤ w.negativeWord.length at hsize
  rw [fill_length hf] at hsize
  have hs := shapeCounts_add s
  omega

/-- Members with a prescribed hash in the same assignment order as the family. -/
def bucket (s : Shape q) (K b L Λ : ℕ) (pad : Fin q)
    (H : TernaryMatrix θ (q^L)) (z : Fin θ → F₃) :=
  (s.members K b L Λ pad).filter (fun w => decide (H.mulVec (vector pad w.2) = z))

theorem bucket_length (s : Shape q) (K b L Λ : ℕ) (pad : Fin q) (hL : 1 ≤ L)
    (H : TernaryMatrix θ (q^L)) (z : Fin θ → F₃) :
    (bucket s K b L Λ pad H z).length = BucketBalance.bucketCount (s.vectors K b L Λ pad) H z := by
  let v := fun w : QWord q × Borrowed.BubbleWord (Fin q) K b L => vector pad w.2
  let check := fun β : Fin (q^L) → F₃ => decide (H.mulVec β = z)
  have he : (bucket s K b L Λ pad H z).map v = ((s.members K b L Λ pad).map v).filter check := by
    rw [List.filter_map]
    rfl
  have hn := (vectors_nodup s K b L Λ pad hL).filter check
  unfold BucketBalance.bucketCount Shape.vectors
  have hk := List.toFinset_card_of_nodup hn
  rw [← he,List.length_map] at hk
  rw [← hk,he,List.toFinset_filter]
  congr 1

#print axioms member_originalCount_lower
#print axioms vectors_card
#print axioms bucket_length

end DeletionCode.Explicit.BubbleFamilies
