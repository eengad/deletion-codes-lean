import DeletionCode.Explicit.AcceptanceWeights
import DeletionCode.Explicit.CompressorFrame
import DeletionCode.Explicit.ParameterMassBounds

/-! Combined rare-word mass and the first compressor branch. -/
namespace DeletionCode.Explicit.RareAddress

open FieldHash Machine MatchingEnumeration WeightedAddress
open scoped BigOperators

variable {q ℓ b t θ : ℕ}

abbrev HashWidth (q b t ℓ : ℕ) := q^UniformParameters.gram q b t ℓ

def liftWeight (f : (Fin ℓ → Fin q) → ℕ) (w : QWord q) : ℕ :=
  if h : w.length = ℓ then f (fun i : Fin ℓ => w[i.val]'(h.symm ▸ i.isLt)) else 0

@[simp] theorem liftWeight_ofFn (f : (Fin ℓ → Fin q) → ℕ) (x : Fin ℓ → Fin q) :
    liftWeight f (List.ofFn x) = f x := by
  simp only [liftWeight, List.length_ofFn, List.getElem_ofFn]
  rfl

/-- Transfer indexed prefix sums to the list interface, for any word weight. -/
theorem exact_of_prefix_sum (f : (Fin ℓ → Fin q) → ℕ) (mass : Mass q)
    (h : ∀ {k} (hk : k ≤ ℓ) (u : Fin k → Fin q), mass (List.ofFn u) =
      ∑ x : Fin ℓ → Fin q, if ∀ i, x (Fin.castLE hk i) = u i then f x else 0) :
    Exact (liftWeight f) mass ℓ := by
  intro p n hp
  subst ℓ
  let u (i : Fin p.length) := p[i]
  have hu : List.ofFn u = p := List.ofFn_get p
  calc
    mass p = ∑ x : Fin (p.length+n) → Fin q,
        if ∀ i, x (Fin.castLE (Nat.le_add_right p.length n) i) = u i then f x else 0 :=
      (congrArg mass hu.symm).trans (h (Nat.le_add_right p.length n) u)
    _ = ∑ z : Fin n → Fin q, f (Fin.append u z) := prefixFamily_sum u n f
    _ = extensionMass (liftWeight f) p n := by
      rw [extensionMass, sum_words]
      apply Finset.sum_congr rfl
      intro z _
      have hz : List.ofFn (Fin.append u z) = p ++ List.ofFn z := by
        rw [List.ofFn_add]
        simpa [Function.comp_def] using congrArg (· ++ List.ofFn z) hu
      rw [← hz,liftWeight_ofFn]

def exceptionWeight (pad : Fin q) (b t ℓ : ℕ) (H : TernaryMatrix θ (HashWidth q b t ℓ)) : Mass q :=
  liftWeight (ExceptionalWeight.weight
    (ExceptionalWeight.family pad (ExceptionalWeight.dictionary q (UniformParameters.gram q b t ℓ)) b t ℓ) H)

/-- The three multiplicities are added, even if one word contributes to several. -/
def weight (pad : Fin q) (b t ℓ : ℕ) (H : TernaryMatrix θ (HashWidth q b t ℓ))
    (core : Mass q) (w : QWord q) : ℕ :=
  listWeight ℓ (UniformParameters.windowLength q ℓ) (UniformParameters.omittedLetters q b t ℓ) w +
    exceptionWeight pad b t ℓ H w + core w

def prefixMass (pad : Fin q) (b t ℓ : ℕ) (hs : Ternary.Rows) (core : Mass q) (p : QWord q) : ℕ :=
  MatchingPrefixes.mass pad b t (ℓ,p) + CataloguePrefix.exceptionalPrefixMass pad b t (ℓ,hs,p) + core p

theorem catalogue_exact {m n : ℕ} (pad : Fin q) (C : Fin m → CoreWeight.Object ℓ q n)
    (H : TernaryMatrix θ n) :
    Exact (liftWeight (CoreWeight.weight C H))
      (fun p => CataloguePrefix.prefixMass pad ((ℓ,(n,CataloguePrefix.matrixRows H),p),
        List.ofFn (fun i => CataloguePrefix.objectData (C i)))) ℓ := by
  apply exact_of_prefix_sum
  intro k hk u
  rw [CataloguePrefix.prefixMass_eq,CoreWeight.prefixMass_eq_sum hk]

theorem exception_exact (pad : Fin q) (b t ℓ : ℕ) (H : TernaryMatrix θ (HashWidth q b t ℓ)) :
    Exact (exceptionWeight pad b t ℓ H)
      (fun p => CataloguePrefix.exceptionalPrefixMass pad b t (ℓ,CataloguePrefix.matrixRows H,p)) ℓ := by
  apply exact_of_prefix_sum
  intro k hk u
  rw [CataloguePrefix.exceptionalPrefixMass_eq,ExceptionalWeight.prefixMass_eq_sum _ _ hk]

theorem prefixMass_exact (pad : Fin q) (b t ℓ : ℕ) (H : TernaryMatrix θ (HashWidth q b t ℓ))
    {core coreMass : Mass q} (hc : Exact core coreMass ℓ) :
    Exact (weight pad b t ℓ H core) (prefixMass pad b t ℓ (CataloguePrefix.matrixRows H) coreMass) ℓ := by
  intro p n hp
  unfold prefixMass
  have hm := MatchingPrefixes.mass_exact pad b t ℓ p n hp
  have he := exception_exact pad b t ℓ H p n hp
  dsimp only at hm he
  rw [hm, he, hc p n hp]
  simp only [extensionMass,weight,List.sum_map_add]

open _root_.DeletionCode.Explicit.UniformParameters in
theorem root_bound (pad : Fin q) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hstart : minLength q b t ≤ ℓ) (hs : Ternary.Rows) (coreMass : Mass q)
    (he : (CataloguePrefix.exceptionalPrefixMass pad b t (ℓ,hs,[]) : ℚ) / (q : ℚ)^ℓ ≤
      3 * exceptionalConstant b t * (q : ℚ)^(b*edits t) * gram q b t ℓ *
        (ℓ : ℚ)^(edits t-1) / (hashCount q b t ℓ : ℚ))
    (hc : coreMass [] ≤ q^(ℓ-8)) : prefixMass pad b t ℓ hs coreMass [] ≤ q^(ℓ-6) := by
  have hm0 := MatchingPrefixes.mass_exact pad b t ℓ [] ℓ (by simp)
  simp only [extensionMass,List.nil_append,sum_words,listWeight_ofFn] at hm0
  have hpos : 0 < windowLength q ℓ := by unfold windowLength; omega
  have hm := MatchingWeight.weight_root_bound (ℓ := ℓ) (q := q)
    (Λ := omittedLetters q b t ℓ) hpos (by omega)
  have hmatch : (MatchingPrefixes.mass pad b t (ℓ,[]) : ℚ) / (q : ℚ)^ℓ ≤
      (ℓ : ℚ)^2 * (matchBound q b t ℓ : ℚ) / (q : ℚ)^(windowLength q ℓ) := by
    rw [hm0, Nat.cast_sum]
    simpa only [matchBound, Nat.cast_pow] using hm
  have hz : ((0 : ℕ) : ℚ) / (q : ℚ)^ℓ ≤ 3 * (gamma q b t ℓ : ℚ) *
      (∑ r ∈ Finset.Icc 1 (coreLimit t), ((ℓ : ℚ)^t / (hashCount q b t ℓ : ℚ))^r) := by
    simp only [Nat.cast_zero, zero_div]
    positivity
  obtain ⟨hmb,heb,_⟩ := root_masses_bound hq hb ht hstart hmatch he hz
  have hbasic := basicBounds hq hb ht hstart
  have hl : 8 ≤ ℓ := (by decide : 8 ≤ 400).trans (hbasic.gram_large.trans hbasic.borrowed_length)
  have hcap : 3*q^(ℓ-8) ≤ q^(ℓ-6) := by
    rw [show ℓ-6 = 2+(ℓ-8) by omega, pow_add]
    apply Nat.mul_le_mul_right
    exact (show 3 ≤ 2^2 by decide).trans (Nat.pow_le_pow_left hq 2)
  exact (show prefixMass pad b t ℓ hs coreMass [] ≤ 3*q^(ℓ-8) by unfold prefixMass; omega).trans hcap

/-- The positional digit used when peeling one base-`q` remainder. -/
def digit (pad : Fin q) (r : ℕ) : Fin q := (List.finRange q).getD (r%q) pad

def fixedDigits (pad : Fin q) : ℕ → ℕ → QWord q
  | 0, _ => []
  | n+1, r => fixedDigits pad n (r/q) ++ [digit pad r]

@[simp] theorem fixedDigits_length (pad : Fin q) (m r : ℕ) : (fixedDigits pad m r).length = m := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih => simp [fixedDigits,ih]

private theorem digit_val (pad : Fin q) (r : ℕ) : (digit pad r).val = r%q := by
  unfold digit
  have h : r%q < (List.finRange q).length := by simpa using Nat.mod_lt r (Nat.zero_lt_of_lt pad.isLt)
  rw [List.getD_eq_getElem _ _ h, List.getElem_finRange]
  rfl

private theorem rank_snoc (w : QWord q) (a : Fin q) : wordRank (w ++ [a]) = q*wordRank w+a.val := by
  simp [wordRank,List.reverse_append,Nat.ofDigits_cons,Nat.add_comm]

theorem rank_fixedDigits (pad : Fin q) (m r : ℕ) (hr : r < q^m) : wordRank (fixedDigits pad m r) = r := by
  induction m generalizing r with
  | zero => simp_all [fixedDigits,wordRank]
  | succ m ih =>
    rw [fixedDigits,rank_snoc,digit_val,ih]
    · rw [Nat.add_comm,Nat.mod_add_div]
    · exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt pad.isLt)).mpr (by rwa [← pow_succ])

/-- The first branch uses a fixed visible width so the payload ignores any final frame padding. -/
def encodePayload (pad : Fin q) (start : ℕ) (masses : ℕ → Mass q) (w : QWord q) : Option (QWord q) :=
  let ℓ := w.length
  if max 8 start ≤ ℓ ∧ 0 < masses ℓ w then
    let r := WeightedAddress.encode (masses ℓ) w
    if r < q^(ℓ-6) then some (fixedDigits pad (ℓ-6) r) else none
  else none

def decodePayload (start : ℕ) (masses : ℕ → Mass q) (ℓ : ℕ) (p : QWord q) : Option (QWord q) :=
  if max 8 start ≤ ℓ ∧ ℓ-6 ≤ p.length then
    (WeightedAddress.decode (masses ℓ) ℓ (wordRank (p.take (ℓ-6)))).filter (fun w => decide (w.length = ℓ))
  else none

def branch (pad : Fin q) (start : ℕ) (masses : ℕ → Mass q) : CompressorFrame.Branch q :=
  ⟨encodePayload pad start masses, decodePayload start masses⟩

private theorem mass_word {w : QWord q} {masses weights : ℕ → Mass q}
    (h : Exact (weights w.length) (masses w.length) w.length) : masses w.length w = weights w.length w := by
  simpa [extensionMass,wordsOfLength] using h w 0 (by simp)

theorem branch_encodes (pad : Fin q) (start : ℕ) (weights masses : ℕ → Mass q)
    {w : QWord q} (hlen : max 8 start ≤ w.length)
    (hex : Exact (weights w.length) (masses w.length) w.length)
    (hroot : masses w.length [] ≤ q^(w.length-6)) (hw : 0 < weights w.length w) :
    (branch pad start masses).encode w =
      some (fixedDigits pad (w.length-6) (WeightedAddress.encode (masses w.length) w)) := by
  have hpos := (mass_word hex).symm ▸ hw
  have hr := WeightedAddress.encode_lt hex hroot rfl hw
  simp [branch,encodePayload,hlen,hpos,hr]

theorem branch_laws (pad : Fin q) (hq : 2 ≤ q) (start : ℕ) (weights masses : ℕ → Mass q)
    (hex : ∀ ℓ ≥ start, Exact (weights ℓ) (masses ℓ) ℓ) : (branch pad start masses).Laws pad := by
  have hencode {w payload : QWord q} (h : (branch pad start masses).encode w = some payload) :
      max 8 start ≤ w.length ∧ 0 < masses w.length w ∧
        WeightedAddress.encode (masses w.length) w < q^(w.length-6) ∧
        payload = fixedDigits pad (w.length-6) (WeightedAddress.encode (masses w.length) w) := by
    unfold branch encodePayload at h
    dsimp only at h
    split at h
    · rename_i hp
      split at h
      · rename_i hr
        exact ⟨hp.1,hp.2,hr,(Option.some.inj h).symm⟩
      · contradiction
    · contradiction
  constructor
  · intro w p h
    obtain ⟨hl,_,_,rfl⟩ := hencode h
    have hhd := CompressorFrame.headerLength_le hq
    have h8 := (Nat.le_max_left 8 start).trans hl
    simp only [fixedDigits_length]
    omega
  · intro w p h n
    obtain ⟨hl,hpos,hr,rfl⟩ := hencode h
    let r := WeightedAddress.encode (masses w.length) w
    have hm := hex w.length ((Nat.le_max_right 8 start).trans hl)
    have hw : 0 < weights w.length w := (mass_word hm) ▸ hpos
    let payload := fixedDigits pad (w.length-6) r
    have htake : (payload ++ List.replicate n pad).take (w.length-6) = payload := by
      conv_lhs => rw [← fixedDigits_length pad (w.length-6) r]
      exact List.take_left
    have hfit : w.length-6 ≤ (payload ++ List.replicate n pad).length := by simp [payload]
    change decodePayload start masses w.length (payload ++ List.replicate n pad) = _
    simp only [decodePayload,hl,hfit,and_true,↓reduceIte,htake]
    rw [rank_fixedDigits pad _ _ hr,WeightedAddress.decode_encode hm rfl hw]
    simp
  · intro ℓ p w h
    unfold branch decodePayload at h
    dsimp only at h
    split at h
    · exact of_decide_eq_true (Option.filter_eq_some_iff.mp h).2
    · contradiction

#print axioms catalogue_exact
#print axioms prefixMass_exact
#print axioms root_bound
#print axioms rank_fixedDigits
#print axioms branch_encodes
#print axioms branch_laws

end DeletionCode.Explicit.RareAddress
