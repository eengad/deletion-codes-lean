import DeletionCode.Explicit.CompressorFrame

/-! Embed codecs at one fixed original length into the compressor frame. -/

namespace DeletionCode.Explicit.CompressorFrame

variable {ℓ q : ℕ}

def fixedBranch (encode : (Fin ℓ → Fin q) → Option (QWord q))
    (decode : QWord q → Option (Fin ℓ → Fin q)) : Branch q where
  encode x := if h : x.length = ℓ then encode (fun i => x.get (Fin.cast h.symm i)) else none
  decode n w := if n = ℓ then (decode w).map List.ofFn else none

theorem fixedBranch_laws (pad : Fin q) (encode : (Fin ℓ → Fin q) → Option (QWord q))
    (decode : QWord q → Option (Fin ℓ → Fin q))
    (hf : ∀ {x w}, encode x = some w → headerLength q+w.length ≤ ℓ-1)
    (hi : ∀ {x w}, encode x = some w → ∀ n, decode (w++List.replicate n pad) = some x) :
    (fixedBranch encode decode).Laws pad := by
  refine ⟨?_,?_,?_⟩
  · intro x w h
    change (if h : x.length = ℓ then encode (fun i => x.get (Fin.cast h.symm i)) else none) = some w at h
    split at h
    next hlen => exact hlen.symm ▸ hf h
    next => contradiction
  · intro x w h n
    change (if h : x.length = ℓ then encode (fun i => x.get (Fin.cast h.symm i)) else none) = some w at h
    split at h
    next hlen =>
      have hword : List.ofFn (fun i : Fin ℓ => x.get (Fin.cast hlen.symm i)) = x := by
        apply List.ext_getElem
        · simpa only [List.length_ofFn] using hlen.symm
        · intro i h₁ h₂
          simp
      change (if x.length = ℓ then (decode (w++List.replicate n pad)).map List.ofFn else none) = some x
      rw [ite_eq_left hlen,hi h n]
      exact congrArg some hword
    next => contradiction
  · intro n w x h
    change (if n = ℓ then (decode w).map (List.ofFn) else none) = some x at h
    by_cases hn : n = ℓ
    · subst n
      cases hres : decode w with
      | none => simp [hres] at h
      | some y =>
        have hy : List.ofFn y = x := by simpa [hres] using h
        rw [← hy,List.length_ofFn]
    · simp [hn] at h

#print axioms fixedBranch_laws

end DeletionCode.Explicit.CompressorFrame
