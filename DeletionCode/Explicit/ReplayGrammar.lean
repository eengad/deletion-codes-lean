import DeletionCode.Explicit.ReplayEntry
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite codes for the symbolic replay descriptions of `d:grammar`. -/

namespace DeletionCode.Explicit.ReplayGrammar

open ReplayEntry

variable {E L b q : ℕ}

/-- The manuscript's common bound for the numerical fields in an entry. -/
def radix (E L : ℕ) : ℕ := 100*(E+1)*(L+1)

def descriptionBound (E L b q : ℕ) : ℕ :=
  (E+1)*radix E L^(20*E)*q^(4*b*E)

/-- Six numerical entry fields, three references and two final flags, followed
by the two central words padded to length `b`. -/
abbrev EntryCode (E L b q : ℕ) :=
  (Fin 11 → Fin (radix E L)) × ((Fin b → Fin q) × (Fin b → Fin q))

/-- A length and a bounded table of entries. The decoder reads exactly the
prefix specified by the length. -/
abbrev DescriptionCode (E L b q : ℕ) :=
  Fin (E+1) × (Fin E → EntryCode E L b q)

theorem descriptionCode_card_le (E L b q : ℕ) :
    Fintype.card (DescriptionCode E L b q) ≤ descriptionBound E L b q := by
  classical
  have hradix : 1 ≤ radix E L := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.succ_pos _))
  have hq (b : ℕ) : q^(2*b) ≤ q^(4*b) := by
    by_cases h : q = 0
    · subst q
      cases b <;> simp
    · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero h) (by omega)
  have hentry : radix E L^11 * q^(2*b) ≤ radix E L^20 * q^(4*b) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hradix (by decide)) (hq b)
  have hentries := Nat.pow_le_pow_left hentry E
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  rw [← Nat.pow_add,show b+b = 2*b by omega]
  calc
    _ ≤ (E+1)*(radix E L^20*q^(4*b))^E := Nat.mul_le_mul_left _ hentries
    _ = descriptionBound E L b q := by
      simp only [Nat.mul_pow,← Nat.pow_mul,descriptionBound,mul_assoc]

private abbrev entryCount (E L b q : ℕ) :=
  radix E L^11 * (q^b*q^b)

private abbrev codeCount (E L b q : ℕ) :=
  (E+1)*(entryCount E L b q)^E

private def entryEquiv (E L b q : ℕ) : EntryCode E L b q ≃ Fin (entryCount E L b q) :=
  (Equiv.prodCongr finFunctionFinEquiv
    ((Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv).trans finProdFinEquiv)).trans
      finProdFinEquiv

/-- Enumerate all compact descriptions with a single bounded index. -/
def descriptionEquiv (E L b q : ℕ) : DescriptionCode E L b q ≃ Fin (codeCount E L b q) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.piCongrRight (fun _ => entryEquiv E L b q)).trans
    finFunctionFinEquiv)).trans finProdFinEquiv

theorem codeCount_le (E L b q : ℕ) : codeCount E L b q ≤ descriptionBound E L b q := by
  have h := Fintype.card_congr (descriptionEquiv E L b q)
  rw [Fintype.card_fin] at h
  rw [← h]
  exact descriptionCode_card_le E L b q

def packDescription (c : DescriptionCode E L b q) : Fin (descriptionBound E L b q) :=
  (descriptionEquiv E L b q c).castLE (codeCount_le E L b q)

def unpackDescription (i : Fin (descriptionBound E L b q)) : Option (DescriptionCode E L b q) :=
  if h : i.val < codeCount E L b q then
    some ((descriptionEquiv E L b q).symm ⟨i.val,h⟩)
  else none

theorem unpack_packDescription (c : DescriptionCode E L b q) :
    unpackDescription (packDescription c) = some c := by
  have h := (descriptionEquiv E L b q c).isLt
  simp [unpackDescription,packDescription,h]

#print axioms unpack_packDescription

/-- Code zero pads the reference list. Source starts use the next
`16*E*L+1` codes. Supplier codes then order entries by index,
orientation, and offset. -/
def decodeReference (E L : ℕ) (code : Fin (radix E L)) : Option (Option Reference) :=
  if code.val = 0 then some none
  else if code.val ≤ 16*E*L+1 then
    some (some (.source ((code.val : ℤ)-1-(8*E*L : ℕ))))
  else
    let raw := code.val-(16*E*L+2)
    let i := raw/(2*(3*L+1))
    let side := if raw/(3*L+1)%2 = 0 then Side.negative else Side.positive
    if i < E then some (some (.supplier i side (raw%(3*L+1)))) else none

private theorem code_space (E L : ℕ) :
    16*E*L+2+2*(3*L+1)*E ≤ radix E L := by
  unfold radix
  nlinarith

private def sideCode : Side → ℕ
  | .negative => 0
  | .positive => 1

/-- Encode one reference at the stated manuscript bounds. -/
def encodeReference (E L : ℕ) : Option Reference → Option (Fin (radix E L))
  | none => some ⟨0,Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.succ_pos _)⟩
  | some (.source delta) =>
    if h : -(8*(E : ℤ)*L) ≤ delta ∧ delta ≤ 8*(E : ℤ)*L then
      let code := (delta+8*(E : ℤ)*L+1).toNat
      have hz : (code : ℤ) = delta+8*(E : ℤ)*L+1 := by
        dsimp [code]
        exact Int.toNat_of_nonneg (by omega)
      have hb : code < 16*E*L+2 := by
        have he : (code : ℤ) < 16*(E : ℤ)*L+2 := by nlinarith [h.2]
        exact_mod_cast he
      some ⟨code,hb.trans_le ((Nat.le_add_right _ _).trans (code_space E L))⟩
    else none
  | some (.supplier i side offset) =>
    if h : i < E ∧ offset ≤ 3*L then
      let width := 3*L+1
      let code := 16*E*L+2+((2*i+sideCode side)*width+offset)
      have hb : sideCode side < 2 := by cases side <;> decide
      have hix : 2*i+sideCode side+1 ≤ 2*E := by omega
      have hu := Nat.mul_le_mul_left width hix
      have hoff : offset < width := by dsimp [width]; omega
      have hcode : code < 16*E*L+2+2*width*E := by
        have he : width*(2*i+sideCode side+1) = (2*i+sideCode side)*width+width := by ring
        have he' : width*(2*E) = 2*width*E := by ring
        rw [he,he'] at hu
        dsimp [code]
        omega
      some ⟨code,hcode.trans_le (code_space E L)⟩
    else none

theorem encodeReference_none (E L : ℕ) :
    ∃ code, encodeReference E L none = some code ∧ decodeReference E L code = some none := by
  refine ⟨_,rfl,?_⟩
  simp [decodeReference]

theorem encodeReference_source (E L : ℕ) {delta : ℤ}
    (hlo : -(8*(E : ℤ)*L) ≤ delta) (hhi : delta ≤ 8*(E : ℤ)*L) :
    ∃ code, encodeReference E L (some (.source delta)) = some code ∧
      decodeReference E L code = some (some (.source delta)) := by
  simp only [encodeReference,dite_eq_left (And.intro hlo hhi)]
  refine ⟨_,rfl,?_⟩
  let code := (delta+8*(E : ℤ)*L+1).toNat
  have hz : (code : ℤ) = delta+8*(E : ℤ)*L+1 := Int.toNat_of_nonneg (by omega)
  have he : ((16*E*L+1 : ℕ) : ℤ) = 16*(E : ℤ)*L+1 := by push_cast; rfl
  have hd : ((8*E*L : ℕ) : ℤ) = 8*(E : ℤ)*L := by push_cast; rfl
  have hu : code ≠ 0 := by omega
  have hb : code ≤ 16*E*L+1 := by
    have hb' : (code : ℤ) ≤ 16*(E : ℤ)*L+1 := by nlinarith
    exact_mod_cast hb'
  change (if code = 0 then _ else if code ≤ 16*E*L+1 then _ else _) = _
  simp [hu,hb,hd]
  omega

theorem encodeReference_supplier (E L : ℕ) {i offset : ℕ} {side : Side}
    (hi : i < E) (hpos : offset ≤ 3*L) :
    ∃ code, encodeReference E L (some (.supplier i side offset)) = some code ∧
      decodeReference E L code = some (some (.supplier i side offset)) := by
  simp only [encodeReference,dite_eq_left (And.intro hi hpos)]
  refine ⟨_,rfl,?_⟩
  let w := 3*L+1
  let raw := (2*i+sideCode side)*w+offset
  let code := 16*E*L+2+raw
  have hw : 0 < w := Nat.succ_pos _
  have hp : offset < w := by dsimp [w]; omega
  have hn : code ≠ 0 := by dsimp [code]; omega
  have hb : ¬ code ≤ 16*E*L+1 := by dsimp [code]; omega
  have hs : code-(16*E*L+2) = raw := by dsimp [code]; omega
  have hq : raw/w = 2*i+sideCode side := by
    dsimp [raw]
    rw [Nat.mul_comm (2*i+sideCode side) w,Nat.add_comm (w*(2*i+sideCode side)) offset,
      Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hp,zero_add]
  have hr : raw%w = offset := by
    dsimp [raw]
    rw [Nat.mul_comm (2*i+sideCode side) w,Nat.add_comm (w*(2*i+sideCode side)) offset,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hp]
  have hd : raw/(2*w) = i := by
    rw [Nat.mul_comm 2 w,← Nat.div_div_eq_div_mul,hq]
    cases side <;> simp [sideCode]; omega
  change (if code = 0 then _ else if code ≤ 16*E*L+1 then _ else _) = _
  simp only [hn,hb,ite_false]
  let tail := code-(16*E*L+2)
  change (if tail/(2*w) < E then some (some (Reference.supplier (tail/(2*w))
    (if tail/w%2 = 0 then Side.negative else Side.positive) (tail%w))) else none) = _
  have ht : tail = raw := hs
  rw [ht,hd,hq,hr]
  cases side <;> simp [hi,sideCode]

#print axioms encodeReference_source
#print axioms encodeReference_supplier

structure DecodedEntry (q : ℕ) where
  entry : Entry (Fin q)
  finalBubble : Bool
  finalRule : Bool

private def prefixWord (w : Fin b → Fin q) (n : ℕ) (h : n ≤ b) : List (Fin q) :=
  List.ofFn (fun i : Fin n => w (i.castLE h))

private def readThree (E L : ℕ) (f : Fin 11 → Fin (radix E L)) :
    Option (List Reference) := do
  let first ← decodeReference E L (f 6)
  let second ← decodeReference E L (f 7)
  let third ← decodeReference E L (f 8)
  match first,second,third with
  | some a,none,none => some [a]
  | some a,some b,none => some [a,b]
  | some a,some b,some c => some [a,b,c]
  | _,_,_ => none

/-- Reject malformed entries before running symbolic replay. Chronological
supplier checks and actual lift lengths are checked by the evaluator. -/
def decodeEntry (code : EntryCode E L b q) : Option (DecodedEntry q) := do
  let f := code.1
  let rule := (f 0).val
  let patch := (f 1).val
  let left := (f 2).val
  let right := (f 3).val
  let u := (f 4).val
  let v := (f 5).val
  if rule ≥ E ∨ patch ≥ E ∨ left ≥ L ∨ right ≥ L ∨ (f 9).val > 1 ∨ (f 10).val > 1 then
    none
  else if hu : u ≤ b then
    if hv : v ≤ b then
      let refs ← readThree E L f
      let entry : Entry (Fin q) :=
        ⟨rule,patch,left,prefixWord code.2.1 u hu,prefixWord code.2.2 v hv,right,refs⟩
      if refs.length = (selectedStarts L entry.negativeLength).length then
        some ⟨entry,decide ((f 9).val = 1),decide ((f 10).val = 1)⟩
      else none
    else none
  else none

def ReferenceFits (E L : ℕ) : Reference → Prop
  | .source delta => -(8*(E : ℤ)*L) ≤ delta ∧ delta ≤ 8*(E : ℤ)*L
  | .supplier i _ offset => i < E ∧ offset ≤ 3*L

theorem encodeReference_roundtrip (E L : ℕ) (r : Option Reference)
    (h : ∀ ref ∈ r, ReferenceFits E L ref) :
    ∃ code, encodeReference E L r = some code ∧ decodeReference E L code = some r := by
  cases r with
  | none => exact encodeReference_none E L
  | some ref =>
    have hfit := h ref (by simp)
    cases ref with
    | source delta => exact encodeReference_source E L hfit.1 hfit.2
    | supplier i side offset => exact encodeReference_supplier E L hfit.1 hfit.2

private def encodeNat (E L n : ℕ) : Option (Fin (radix E L)) :=
  if h : n < radix E L then some ⟨n,h⟩ else none

private def packFields (rr pp ll rl u v x y z fb fr : Fin (radix E L)) :
    Fin 11 → Fin (radix E L) :=
  fun i => [rr,pp,ll,rl,u,v,x,y,z,fb,fr].get ⟨i.val,i.isLt⟩

/-- Encode a single entry, padding unused central-word slots with the
supplied alphabet symbol. -/
def encodeEntry (E L b q : ℕ) (pad : Fin q) (d : DecodedEntry q) :
    Option (EntryCode E L b q) := do
  let e := d.entry
  let rule ← encodeNat E L e.rule
  let patch ← encodeNat E L e.patch
  let left ← encodeNat E L e.left
  let right ← encodeNat E L e.right
  let removed ← encodeNat E L e.removed.length
  let inserted ← encodeNat E L e.replacement.length
  let ref₀ ← encodeReference E L e.references[0]?
  let ref₁ ← encodeReference E L e.references[1]?
  let ref₂ ← encodeReference E L e.references[2]?
  let fb ← encodeNat E L d.finalBubble.toNat
  let fr ← encodeNat E L d.finalRule.toNat
  pure (packFields rule patch left right removed inserted ref₀ ref₁ ref₂ fb fr,
    (fun i => e.removed.getD i.val pad), (fun i => e.replacement.getD i.val pad))

/-- The syntactic requirements which actual witness entries must meet. -/
structure EntryFits (E L b : ℕ) (e : Entry (Fin q)) : Prop where
  rule : e.rule < E
  patch : e.patch < E
  left : e.left < L
  right : e.right < L
  removed : e.removed.length ≤ b
  replacement : e.replacement.length ≤ b
  references : ∀ r ∈ e.references, ReferenceFits E L r
  ref_count : e.references.length = (selectedStarts L e.negativeLength).length

private theorem reference_count (L n : ℕ) :
    1 ≤ (selectedStarts L n).length ∧ (selectedStarts L n).length ≤ 3 := by
  by_cases hz : n-L = 0 <;> by_cases ho : n-L = 1 <;> simp [selectedStarts,hz,ho]

private theorem padded_prefix (pad : Fin q) (w : List (Fin q)) (h : w.length ≤ b) :
    prefixWord (fun i : Fin b => w.getD i.val pad) w.length h = w := by
  apply List.ext_getElem
  · simp [prefixWord]
  · intro i hi h'
    simp [prefixWord,List.getD_eq_getElem?_getD]

private theorem refs_read_roundtrip (rs : List Reference) (c₀ c₁ c₂ : Fin (radix E L))
    (hmin : 1 ≤ rs.length) (hmax : rs.length ≤ 3)
    (h₀ : decodeReference E L c₀ = some rs[0]?)
    (h₁ : decodeReference E L c₁ = some rs[1]?)
    (h₂ : decodeReference E L c₂ = some rs[2]?)
    (f : Fin 11 → Fin (radix E L))
    (hf₀ : f 6 = c₀) (hf₁ : f 7 = c₁) (hf₂ : f 8 = c₂) :
    readThree E L f = some rs := by
  unfold readThree
  rw [hf₀,hf₁,hf₂,h₀,h₁,h₂]
  rcases rs with _ | ⟨r,rs⟩
  · simp at hmin
  rcases rs with _ | ⟨s,rs⟩
  · rfl
  rcases rs with _ | ⟨t,rs⟩
  · rfl
  cases rs with
  | nil => rfl
  | cons => simp at hmax

theorem encodeEntry_roundtrip {pad : Fin q} (d : DecodedEntry q)
    (hb : b ≤ L) (hd : EntryFits E L b d.entry) :
    ∃ c, encodeEntry E L b q pad d = some c ∧ decodeEntry c = some d := by
  let e := d.entry
  have hE : E < radix E L := by unfold radix; nlinarith
  have hL : L < radix E L := by unfold radix; nlinarith
  have hflag : ∀ flag : Bool, flag.toNat < radix E L := by
    intro flag
    have h := code_space E L
    cases flag <;> simp <;> omega
  have fit (i : ℕ) (r : Reference) (hr : r ∈ e.references[i]?) :
      ReferenceFits E L r := hd.references r (List.mem_of_getElem? (by simpa using hr))
  obtain ⟨c₀,hc₀,hr₀⟩ := encodeReference_roundtrip E L e.references[0]? (fit 0)
  obtain ⟨c₁,hc₁,hr₁⟩ := encodeReference_roundtrip E L e.references[1]? (fit 1)
  obtain ⟨c₂,hc₂,hr₂⟩ := encodeReference_roundtrip E L e.references[2]? (fit 2)
  let f := packFields ⟨e.rule,hd.rule.trans hE⟩ ⟨e.patch,hd.patch.trans hE⟩
    ⟨e.left,hd.left.trans hL⟩ ⟨e.right,hd.right.trans hL⟩
    ⟨e.removed.length,hd.removed.trans_lt (hb.trans_lt hL)⟩
    ⟨e.replacement.length,hd.replacement.trans_lt (hb.trans_lt hL)⟩
    c₀ c₁ c₂ ⟨d.finalBubble.toNat,hflag _⟩ ⟨d.finalRule.toNat,hflag _⟩
  let c : EntryCode E L b q := ⟨f,fun i => e.removed.getD i.val pad,fun i => e.replacement.getD i.val pad⟩
  have hpacked : encodeEntry E L b q pad d = some c := by
    simp [encodeEntry,encodeNat,e,c,f,hc₀,hc₁,hc₂,hd.rule.trans hE,hd.patch.trans hE,
      hd.left.trans hL,hd.right.trans hL,hd.removed.trans_lt (hb.trans_lt hL),
      hd.replacement.trans_lt (hb.trans_lt hL),hflag]
  have hcount := reference_count L e.negativeLength
  have hread : readThree E L f = some e.references :=
    refs_read_roundtrip e.references c₀ c₁ c₂
      (hd.ref_count ▸ hcount.1) (hd.ref_count ▸ hcount.2) hr₀ hr₁ hr₂ f rfl rfl rfl
  refine ⟨c,hpacked,?_⟩
  have hflag₁ : ∀ flag : Bool, flag.toNat ≤ 1 := by intro flag; cases flag <;> decide
  have hflag₂ : ∀ flag : Bool, decide (flag.toNat = 1) = flag := by intro flag; cases flag <;> decide
  have hone : (f 0).val = e.rule := rfl
  have htwo : (f 1).val = e.patch := rfl
  have hthree : (f 2).val = e.left := rfl
  have hfour : (f 3).val = e.right := rfl
  have hfive : (f 4).val = e.removed.length := rfl
  have hsix : (f 5).val = e.replacement.length := rfl
  have hnine : (f 9).val = d.finalBubble.toNat := rfl
  have hten : (f 10).val = d.finalRule.toNat := rfl
  have hentry : (⟨e.rule,e.patch,e.left,e.removed,e.replacement,e.right,e.references⟩ : Entry (Fin q)) = e := by
    cases e
    rfl
  have hd' : e.references.length = (selectedStarts L e.negativeLength).length := hd.ref_count
  simp [decodeEntry,c,hone,htwo,hthree,hfour,hfive,hsix,hnine,hten,hread,
    Nat.not_le_of_gt hd.rule,Nat.not_le_of_gt hd.patch,Nat.not_le_of_gt hd.left,
    Nat.not_le_of_gt hd.right,Nat.not_lt_of_ge (hflag₁ _),hd.removed,hd.replacement,
    padded_prefix,hentry,hd',e,-List.getD_eq_getElem?_getD]

#print axioms encodeEntry_roundtrip

def decodeDescription (c : DescriptionCode E L b q) : Option (List (DecodedEntry q)) :=
  (List.ofFn fun i : Fin c.1.val => c.2 (i.castLE (Nat.le_of_lt_succ c.1.isLt))).mapM decodeEntry

private def paddingEntry (E L b q : ℕ) (pad : Fin q) : EntryCode E L b q :=
  ⟨fun _ => ⟨0,Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.succ_pos _)⟩,
    fun _ => pad,fun _ => pad⟩

/-- Copy just the coded entries into a fixed-size table. The remaining
entries are padding, and their letters are never read during replay. -/
def encodeDescription (E L b q : ℕ) (pad : Fin q) (ds : List (DecodedEntry q)) :
    Option (DescriptionCode E L b q) := do
  let codes ← ds.mapM (encodeEntry E L b q pad)
  if h : codes.length ≤ E then
    some ⟨⟨codes.length,Nat.lt_succ_of_le h⟩,
      fun i => codes.getD i.val (paddingEntry E L b q pad)⟩
  else none

private theorem encode_entries (pad : Fin q) (ds : List (DecodedEntry q))
    (hb : b ≤ L) (hd : ∀ d ∈ ds, EntryFits E L b d.entry) :
    ∃ codes, ds.mapM (encodeEntry E L b q pad) = some codes ∧
      codes.mapM decodeEntry = some ds ∧ codes.length = ds.length := by
  induction ds with
  | nil => exact ⟨[],rfl,rfl,rfl⟩
  | cons d rest ih =>
    obtain ⟨c,hc,hdec⟩ := encodeEntry_roundtrip (pad := pad) d hb (hd d List.mem_cons_self)
    obtain ⟨cs,hcs,hrd,hlen⟩ := ih (fun e he => hd e (List.mem_cons_of_mem _ he))
    exact ⟨c::cs,by simp [hc,hcs],by simp [hdec,hrd],by simp [hlen]⟩

theorem encodeDescription_roundtrip (pad : Fin q) (ds : List (DecodedEntry q))
    (hb : b ≤ L) (hn : ds.length ≤ E) (hd : ∀ d ∈ ds, EntryFits E L b d.entry) :
    ∃ c, encodeDescription E L b q pad ds = some c ∧ decodeDescription c = some ds := by
  obtain ⟨codes,hencode,hdecode,hlen⟩ := encode_entries (E := E) pad ds hb hd
  have hfit := hlen.le.trans hn
  let c : DescriptionCode E L b q := ⟨⟨codes.length,Nat.lt_succ_of_le hfit⟩,
    fun i => codes.getD i.val (paddingEntry E L b q pad)⟩
  refine ⟨c,by simp [encodeDescription,hencode,hfit,c],?_⟩
  have hprefix : (List.ofFn fun i : Fin codes.length =>
      codes.getD i.val (paddingEntry E L b q pad)) = codes := by
    conv_rhs => rw [← List.ofFn_get codes]
    congr 1
    funext i
    simp [List.getD_eq_getElem?_getD]
  change (List.ofFn fun i : Fin codes.length =>
      codes.getD i.val (paddingEntry E L b q pad)).mapM decodeEntry = some ds
  rw [hprefix]
  exact hdecode

#print axioms encodeDescription_roundtrip

/-- Decode and replay without querying a source letter. -/
def replayDescription {ℓ : ℕ} (c : DescriptionCode E L b q)
    (anchor : ℕ → Option (Fin ℓ)) : Option (Array (Completed ℓ (Fin q))) := do
  let decoded ← decodeDescription c
  replay L anchor (decoded.map DecodedEntry.entry)

#print axioms descriptionCode_card_le

end DeletionCode.Explicit.ReplayGrammar
