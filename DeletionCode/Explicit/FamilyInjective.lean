import DeletionCode.Explicit.BubbleFamilies
import DeletionCode.Qary.BubbleCatalogue

/-! Local injectivity of a fixed bubble shape (`d:local-injective`). -/

namespace DeletionCode.Explicit.BubbleFamilies

open Borrowed FieldHash
open Qary.SignedSupport Qary.SupportComponents Qary.Windows
open Qary.BubbleCatalogue (wordSpectrum_eq_pathSpectrum)

variable {q K b L : ℕ}

set_option linter.style.haveILetI false

private def singleFamily [Inhabited (Fin q)] (w : BubbleWord (Fin q) K b L) :=
  Catalogue.indexedFamily (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1))

private theorem path_spectrum (pad : Fin q) (w : BubbleWord (Fin q) K b L)
    (side : Bool) (g : Gram (Fin q) L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) →
      listFieldSpectrum pad (Catalogue.pathWord w side) L g =
        (pathSpectrum ((singleFamily w).path 0 side) L ((singleFamily w).extra 0 side) g : F₃) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h
  have hlo : L ≤ (Catalogue.pathWord w side).length := h.length_lower 0 side
  unfold listFieldSpectrum
  rw [fieldSpectrum_eq_cast,wordSpectrum_eq_pathSpectrum _ _ _ hlo]
  rfl

private theorem vector_coord (pad : Fin q) (w : BubbleWord (Fin q) K b L)
    (g : Gram (Fin q) L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) →
      vector pad w (finFunctionFinEquiv g) = (bubbleSpectrum (singleFamily w) L 0 g : F₃) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h
  have pos : listFieldSpectrum pad w.positiveWord L g = _ := path_spectrum pad w true g h
  have neg : listFieldSpectrum pad w.negativeWord L g = _ := path_spectrum pad w false g h
  simp [vector,pos,neg,bubbleSpectrum]

private theorem minus_one_iff (pad : Fin q) (w : BubbleWord (Fin q) K b L)
    (g : Gram (Fin q) L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) →
    (vector pad w (finFunctionFinEquiv g) = -1 ↔
      g ∈ windowSet ((singleFamily w).path 0 false) L ((singleFamily w).extra 0 false)) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h
  rw [vector_coord pad w g h]
  constructor
  · intro he
    by_contra hn
    by_cases hp : g ∈ windowSet ((singleFamily w).path 0 true) L ((singleFamily w).extra 0 true)
    · rw [bubble_positive_value (singleFamily w) L h.geometry 0 _ hp] at he
      exact (by decide : ((1 : ℤ) : F₃) ≠ -1) he
    · have hz : bubbleSpectrum (singleFamily w) L 0 g = 0 := by
        by_contra hne
        obtain ⟨side,hs⟩ := (bubble_support_iff (singleFamily w) L h.geometry 0 g).mp hne
        cases side
        · exact hn hs
        · exact hp hs
      rw [hz] at he
      exact (by decide : ((0 : ℤ) : F₃) ≠ -1) he
  · intro hg
    rw [bubble_negative_value (singleFamily w) L h.geometry 0 _ hg]
    decide

private theorem negative_spectrum (pad : Fin q) (w : BubbleWord (Fin q) K b L)
    (g : Gram (Fin q) L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) →
    listFieldSpectrum pad w.negativeWord L g =
      if vector pad w (finFunctionFinEquiv g) = -1 then 1 else 0 := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h
  have he : listFieldSpectrum pad w.negativeWord L g = _ := path_spectrum pad w false g h
  rw [he]
  by_cases hg : g ∈ windowSet ((singleFamily w).path 0 false) L ((singleFamily w).extra 0 false)
  · rw [ite_eq_left ((minus_one_iff pad w g h).mpr hg),
      pathSpectrum_eq_one _ _ _ _ (gram_injective_of_simple (singleFamily w) L h.geometry 0 false) hg]
    rfl
  · rw [ite_eq_right (fun hval => hg ((minus_one_iff pad w g h).mp hval)),
      pathSpectrum_eq_zero _ _ _ _ hg]
    rfl

private theorem negative_unique (pad : Fin q) (w : BubbleWord (Fin q) K b L) :
    letI : Inhabited (Fin q) := ⟨pad⟩
    Catalogue.ValidCatalogue (fun _ : Fin 1 => w) (fun _ => (0 : Fin 1)) →
    KUnique (fun i => w.negativeWord.getD i pad) w.negativeWord.length (L-1) := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  intro h a b ha hb hagree
  have he : ((singleFamily w).extra 0 false) = w.negativeWord.length-L := rfl
  let ai : Fin ((singleFamily w).extra 0 false+2) := ⟨a,by rw [he]; omega⟩
  let bi : Fin ((singleFamily w).extra 0 false+2) := ⟨b,by rw [he]; omega⟩
  have eq : vertex (singleFamily w) L 0 false ai.val =
      vertex (singleFamily w) L 0 false bi.val := by
    funext i
    change w.negativeWord.getD (a+i.val) pad = w.negativeWord.getD (b+i.val) pad
    exact hagree i.val i.isLt
  exact congrArg Fin.val (h.geometry.simple 0 false eq)

theorem member_vector_injective (s : Shape q) (pad : Fin q) {Λ : ℕ} (hL : 1 ≤ L)
    {x y : QWord q} {u v : BubbleWord (Fin q) K b L}
    (hx : s.member K b L Λ pad x = some u) (hy : s.member K b L Λ pad y = some v)
    (hvec : vector pad u = vector pad v) : x = y := by
  letI : Inhabited (Fin q) := ⟨pad⟩
  obtain ⟨hfillx,_,hu⟩ := member_data s K b L Λ pad hx
  obtain ⟨hfilly,_,hv⟩ := member_data s K b L Λ pad hy
  have hspec : listFieldSpectrum pad v.negativeWord L = listFieldSpectrum pad u.negativeWord L := by
    classical
    funext g
    rw [negative_spectrum pad v g hv,negative_spectrum pad u g hu,hvec]
  have eq := field_path_list pad u.negativeWord v.negativeWord L
    ((fill_length hfilly).trans (fill_length hfillx).symm) hL (hu.length_lower 0 false)
    (negative_unique pad u hu) hspec
  rw [eq] at hfilly
  exact fill_injective hfillx hfilly

#print axioms member_vector_injective

end DeletionCode.Explicit.BubbleFamilies
