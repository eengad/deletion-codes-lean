import DeletionCode.Burst.BlockWords
import DeletionCode.Burst.Header
import Mathlib.Data.Fin.Tuple.Basic

/-!
Transfer across a burst by deleting its replacement symbols one at a time,
then inserting the recorded removed block. Each deletion uses at most one
extension symbol. The long right flank keeps every extension in bounds.
-/
namespace DeletionCode.Burst.SeedTransfer
open DeletionCode.Qary.Windows DeletionCode.Qary.HeaderRecovery
open DeletionCode.Burst.BlockWords
variable {α : Type*} [Inhabited α]

def shortenMany (a k : ℕ) : (r : ℕ) → (Fin r → α) → Seed α → Seed α
  | 0, _, seed => seed
  | r + 1, extras, seed =>
      shortenMany a k r (fun i => extras i.succ) (shortenSeed a k seed (extras 0))

def lengthenMany (a k : ℕ) : List α → Seed α → Seed α
  | [], seed => seed
  | symbol :: rest, seed => lengthenSeed a k (lengthenMany a k rest seed) symbol

theorem shorten_bound (a k m : ℕ) (seed : Seed α) (extra : α)
    (hbound : seed.offset + k ≤ m + 1) (hroom : a + k ≤ m) :
    (shortenSeed a k seed extra).offset + k ≤ m := by
  unfold shortenSeed
  split_ifs <;> (try dsimp) <;> omega

theorem lengthen_bound (a k m : ℕ) (seed : Seed α) (symbol : α)
    (hbound : seed.offset + k ≤ m) :
    (lengthenSeed a k seed symbol).offset + k ≤ m + 1 := by
  unfold lengthenSeed
  split_ifs <;> (try dsimp) <;> omega

theorem shortenMany_exists (p : Letters α) (a k r right : ℕ) (seed : Seed α)
    (hright : k ≤ right) (hbound : seed.offset + k ≤ a + r + right)
    (hseed : Agree p seed.offset seed.bits 0 k) :
    ∃ extras : Fin r → α,
      Agree (deleteBlock p a r) (shortenMany a k r extras seed).offset
        (shortenMany a k r extras seed).bits 0 k ∧
      (shortenMany a k r extras seed).offset + k ≤ a + right := by
  induction r generalizing p seed with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · simpa only [shortenMany, deleteBlock_zero] using hseed
    · simpa only [shortenMany, Nat.add_zero] using hbound
  | succ r ih =>
    let extra := deleteAt p a (seed.offset + k - 1)
    let next := shortenSeed a k seed extra
    have hn : Agree (deleteAt p a) next.offset next.bits 0 k :=
      shorten_seed_correct p a k seed extra hseed (fun _ _ => rfl)
    have hb : next.offset + k ≤ a + r + right :=
      shorten_bound a k (a + r + right) seed extra (by omega) (by omega)
    obtain ⟨rest, hrest, hbrest⟩ := ih (deleteAt p a) next hb hn
    refine ⟨Fin.cons extra rest, ?_, ?_⟩
    · simpa only [shortenMany, Fin.cons_zero, Fin.cons_succ, ← deleteBlock_succ] using hrest
    · simpa only [shortenMany, Fin.cons_zero, Fin.cons_succ] using hbrest

theorem shortenMany_bound (a k r right : ℕ) (seed : Seed α) (extras : Fin r → α)
    (hright : k ≤ right) (hbound : seed.offset + k ≤ a + r + right) :
    (shortenMany a k r extras seed).offset + k ≤ a + right := by
  induction r generalizing seed with
  | zero => simpa only [shortenMany, Nat.add_zero] using hbound
  | succ r ih =>
    apply ih (shortenSeed a k seed (extras 0))
    exact shorten_bound a k (a + r + right) seed (extras 0) (by omega) (by omega)

theorem lengthenMany_correct (p : Letters α) (a k : ℕ) (word : List α) (seed : Seed α)
    (hseed : Agree p seed.offset seed.bits 0 k) :
    Agree (insertBlock p a word) (lengthenMany a k word seed).offset
      (lengthenMany a k word seed).bits 0 k := by
  induction word with
  | nil => simpa only [insertBlock_nil, lengthenMany] using hseed
  | cons symbol word ih =>
    rw [insertBlock_cons]
    exact lengthen_seed_correct (insertBlock p a word) a k
      (lengthenMany a k word seed) symbol ih

theorem lengthenMany_bound (a k m : ℕ) (word : List α) (seed : Seed α)
    (hbound : seed.offset + k ≤ m) :
    (lengthenMany a k word seed).offset + k ≤ m + word.length := by
  induction word with
  | nil => simpa only [lengthenMany, List.length_nil, Nat.add_zero] using hbound
  | cons symbol word ih =>
    have h := lengthen_bound a k (m + word.length) (lengthenMany a k word seed) symbol ih
    simpa only [lengthenMany, List.length_cons, Nat.add_assoc] using h

end DeletionCode.Burst.SeedTransfer
