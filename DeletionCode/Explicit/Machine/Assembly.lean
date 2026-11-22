import DeletionCode.Explicit.Machine.WrapperDecoding
import DeletionCode.Explicit.WrapperRedundancy

/-! Assemble the final machine statement from the source-data obligations. -/
namespace DeletionCode.Explicit.Machine

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

def assembledTables (t b q G A l₀ n : ℕ) : TagTables q :=
  prepareTags q b t n (publicLabelBound q b (2 * t) G A l₀ n)

def assembledSetup (t b q G A l₀ : ℕ) (src : ℕ → List Bool) (n : ℕ) : List Bool :=
  encPair encBits encBits (tagTablesEncoding q (assembledTables t b q G A l₀ n), src n)

theorem assembledSetup_polyTime {t b q G A l₀ : ℕ} (hq : 2 ≤ q) {src : ℕ → List Bool}
    (hsrc : ComputableInPolyTime src encUnary encBits) :
    ComputableInPolyTime (assembledSetup t b q G A l₀ src) encUnary encBits := by
  have ht := prepareTags_setup_polyTime hq b t (publicLabelBound_polyTime q b (2 * t) G A l₀)
  exact (ht.prod hsrc).of_enc_eq (fun _ => rfl)

def readPublic (q : ℕ) (bits : List Bool) : Option (PublicData q) :=
  (parseTagTables q (unframe bits)).map (fun T => (T, dropFrame bits))

theorem readPublic_polyTime (q : ℕ) :
    ComputableInPolyTime (readPublic q) encBits (encOption (publicDataEncoding q)) := by
  have h := (parseTagTables_polyTime q).comp ComputableInPolyTime.unframe
  exact h.optionMapWithInput (f := fun bits T => (T, dropFrame bits))
    ((snd encBits (tagTablesEncoding q)).prod
      (ComputableInPolyTime.dropFrame.comp (fst encBits (tagTablesEncoding q))))

theorem readPublic_setup (t b q G A l₀ : ℕ) (src : ℕ → List Bool) (n : ℕ) :
    readPublic q (assembledSetup t b q G A l₀ src n) =
      some (assembledTables t b q G A l₀ n, src n) := by
  simp only [assembledSetup, readPublic, encPair_apply, encBits_apply, unframe_frame_append,
    dropFrame_frame_append, parseTagTables_encoding, Option.map_some]

private theorem onPublic_polyTime {q : ℕ} {α : Type} {enc : α ↪ List Bool}
    {f : WrapperInput q → α}
    (hf : ComputableInPolyTime f (wrapperInputEncoding q) enc) (fallback : α) :
    ComputableInPolyTime
      (fun p : SourceInput q => (readPublic q p.1).elim fallback (fun data => f (data, p.2)))
      (inputEncoding q) enc := by
  let ip := inputEncoding q
  have hdata := (readPublic_polyTime q).comp (fst encBits (wordEncoding q))
  exact hdata.optionElimWithInput (const fallback)
    (hf.comp ((snd ip (publicDataEncoding q)).prod
      ((snd encBits (wordEncoding q)).comp (fst ip (publicDataEncoding q)))))

def assembledEncode {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (p : SourceInput q) : QWord q :=
  (readPublic q p.1).elim [] (fun data => encodeWrapped zero l₀ F (data, p.2))

def assembledImageTest {q : ℕ} (zero : Fin q) (l₀ : ℕ) (F : SourceCallbacks q)
    (p : SourceInput q) : Option (QWord q) :=
  (readPublic q p.1).elim none (fun data => imageTestWrapped zero l₀ F (data, p.2))

def assembledDecode {q : ℕ} (zero : Fin q) (l₀ b t : ℕ) (F : SourceCallbacks q)
    (p : SourceInput q) : QWord q :=
  ((readPublic q p.1).elim none (fun data => decodeWrapped zero l₀ b t F (data, p.2))).getD []

theorem assembledEncode_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (assembledEncode zero l₀ F) (inputEncoding q) (wordEncoding q) :=
  onPublic_polyTime (encodeWrapped_polyTime hq zero l₀ F H) []

theorem assembledImageTest_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (assembledImageTest zero l₀ F) (inputEncoding q)
      (encOption (wordEncoding q)) :=
  onPublic_polyTime (imageTestWrapped_polyTime hq zero l₀ F H) none

theorem assembledDecode_polyTime {q : ℕ} (hq : 2 ≤ q) (zero : Fin q) (l₀ b t : ℕ)
    (F : SourceCallbacks q) (H : F.Certified) :
    ComputableInPolyTime (assembledDecode zero l₀ b t F) (inputEncoding q) (wordEncoding q) :=
  optionGetDWithInput (onPublic_polyTime (decodeWrapped_polyTime hq zero l₀ b t F H) none)
    (const [])

/-- Correctness obligations for the unfinished half at one block length.
The probability parameter is used only in the proof and need not be serialized. -/
structure SourceGuarantees {q : ℕ} (F : SourceCallbacks q) (bits : List Bool)
    (b t n G A l₀ : ℕ) : Prop where
  repair : F.RepairLaws bits
  labels : ∃ P : ℕ → ℕ,
    (∀ l, l₀ ≤ l → l ≤ n → P l < 3 * l ^ (2 * t - 1) * gramLength q b G l ^ A) ∧
    (∀ x : QWord q, l₀ ≤ x.length → x.length ≤ n → F.accepted (bits, x) = true →
      F.label (bits, x) < 3 * P x.length) ∧
    (∀ x y : QWord q, l₀ ≤ x.length → x.length = y.length → x.length ≤ n →
      F.accepted (bits, x) = true → F.accepted (bits, y) = true →
      F.label (bits, x) = F.label (bits, y) → Burst.WithinBursts b (2 * t) x y → x = y)

private theorem outputLength_bound {f : ℕ → List Bool}
    (hf : ComputableInPolyTime f encUnary encBits) :
    ∃ M d : ℕ, ∀ n ≥ 1, (f n).length ≤ M * n ^ d := by
  obtain ⟨c, d, h⟩ := hf.polyBounded_length.exists_le
  refine ⟨c * 2 ^ d, d, fun n hn => ?_⟩
  have hlen : (f n).length ≤ c * (n + 1) ^ d := by simpa using h n
  apply hlen.trans
  rw [mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)

private theorem loglog_nonneg {q n : ℕ} (hq : 2 ≤ q) (hn : q ≤ n) :
    0 ≤ Real.logb q (Real.logb q n) := by
  have hbase : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  apply Real.logb_nonneg hbase
  rw [← Real.logb_self_eq_one hbase]
  exact Real.logb_le_logb_of_le hbase (by positivity) (by exact_mod_cast hn)

/-- The final theorem's conclusion, conditional only on the source-data
machine certificates and the existing stage 1 source-data laws. -/
theorem deterministic_of_source (t b q G A l₀ n₀ : ℕ) (ht : 2 ≤ t) (hq : 2 ≤ q)
    (src : ℕ → List Bool) (F : SourceCallbacks q)
    (hsrc : ComputableInPolyTime src encUnary encBits) (H : F.Certified)
    (hlaws : ∀ n ≥ n₀, SourceGuarantees F (src n) b t n G A l₀) :
    ∃ (C d n₀ : ℕ) (k : ℕ → ℕ) (setup : ℕ → List Bool)
      (encode decode : List Bool × List (Fin q) → List (Fin q)),
      ComputableInPolyTime setup encUnary encBits ∧
      ComputableInPolyTime encode (inputEncoding q) (wordEncoding q) ∧
      ComputableInPolyTime decode (inputEncoding q) (wordEncoding q) ∧
      ∀ n ≥ n₀,
        (setup n).length ≤ C * n ^ d ∧ k n ≤ n ∧
        (n : ℝ) - (k n : ℝ) ≤
          (2 * (t : ℝ) - 1) * Real.logb q n +
            C * Real.logb q (Real.logb q n) ∧
        ∀ u : List (Fin q), u.length = k n →
          let x := encode (setup n, u)
          x.length = n ∧
            ∀ z, Burst.WithinBursts b t x z → decode (setup n, z) = u := by
  let zero : Fin q := ⟨0, by omega⟩
  let tables := assembledTables t b q G A l₀
  let setup := assembledSetup t b q G A l₀ src
  have hsetup : ComputableInPolyTime setup encUnary encBits := assembledSetup_polyTime hq hsrc
  obtain ⟨M, d, hsize⟩ := outputLength_bound hsetup
  obtain ⟨K, N, hwrap⟩ := wrapped_code_of_source_data hq ht b G A l₀
  refine ⟨max M K, d, max (max n₀ N) q, fun n => (tables n).k, setup,
    assembledEncode zero l₀ F, assembledDecode zero l₀ b t F, hsetup,
    assembledEncode_polyTime hq zero l₀ F H, assembledDecode_polyTime hq zero l₀ b t F H, ?_⟩
  intro n hn
  have hn₀ : n₀ ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnq : q ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have laws := hlaws n hn₀
  obtain ⟨P, hP, hlabel, hsep⟩ := laws.labels
  let T := tables n
  let D := F.repairData (src n) laws.repair
  let label := labelAt l₀ (fun u => F.label (src n, u))
  let W := T.wrapper zero D label
  obtain ⟨hred, hcorrect⟩ := hwrap n hnN
  have hk : T.k ≤ n := by change n - _ - _ ≤ n; omega
  have hcoef : (K : ℝ) ≤ (max M K : ℕ) := by exact_mod_cast Nat.le_max_right M K
  have hmono := mul_le_mul_of_nonneg_right hcoef (loglog_nonneg hq hnq)
  refine ⟨(hsize n hn1).trans (Nat.mul_le_mul_right (n ^ d) (Nat.le_max_left M K)),
    hk, hred.trans (add_le_add_right hmono _), ?_⟩
  intro u hu
  have correct := hcorrect zero D (fun w => F.label (src n, w)) P hP hlabel hsep u hu
  have he : assembledEncode zero l₀ F (setup n, u) = W.encode u := by
    change (readPublic q (assembledSetup t b q G A l₀ src n)).elim [] _ = _
    rw [readPublic_setup]
    exact encodeWrapped_eq zero l₀ F T laws.repair u
  change (assembledEncode zero l₀ F (setup n, u)).length = n ∧
    ∀ z, Burst.WithinBursts b t (assembledEncode zero l₀ F (setup n, u)) z →
      assembledDecode zero l₀ b t F (setup n, z) = u
  rw [he]
  refine ⟨correct.1, fun z hz => ?_⟩
  change ((readPublic q (assembledSetup t b q G A l₀ src n)).elim none _).getD [] = u
  rw [readPublic_setup, Option.elim_some, decodeWrapped_eq zero l₀ b t F T laws.repair]
  change (W.decode b t z).getD [] = u
  have hd : W.decode b t z = some u := correct.2 z hz
  rw [hd]
  rfl

-- The proposition is copied verbatim from `DeletionCode.Explicit.deterministic`.
example (t b q G A l₀ n₀ : ℕ) (ht : 2 ≤ t) (hq : 2 ≤ q)
    (src : ℕ → List Bool) (F : SourceCallbacks q)
    (hsrc : ComputableInPolyTime src encUnary encBits) (H : F.Certified)
    (hlaws : ∀ n ≥ n₀, SourceGuarantees F (src n) b t n G A l₀) :
    ∃ (C d n₀ : ℕ) (k : ℕ → ℕ) (setup : ℕ → List Bool)
      (encode decode : List Bool × List (Fin q) → List (Fin q)),
      ComputableInPolyTime setup encUnary encBits ∧
      ComputableInPolyTime encode (inputEncoding q) (wordEncoding q) ∧
      ComputableInPolyTime decode (inputEncoding q) (wordEncoding q) ∧
      ∀ n ≥ n₀,
        (setup n).length ≤ C * n ^ d ∧ k n ≤ n ∧
        (n : ℝ) - (k n : ℝ) ≤
          (2 * (t : ℝ) - 1) * Real.logb q n +
            C * Real.logb q (Real.logb q n) ∧
        ∀ u : List (Fin q), u.length = k n →
          let x := encode (setup n, u)
          x.length = n ∧
            ∀ z, Burst.WithinBursts b t x z → decode (setup n, z) = u := by
  exact deterministic_of_source t b q G A l₀ n₀ ht hq src F hsrc H hlaws

#print axioms assembledSetup_polyTime
#print axioms readPublic_polyTime
#print axioms assembledEncode_polyTime
#print axioms assembledImageTest_polyTime
#print axioms assembledDecode_polyTime
#print axioms deterministic_of_source

end DeletionCode.Explicit.Machine
