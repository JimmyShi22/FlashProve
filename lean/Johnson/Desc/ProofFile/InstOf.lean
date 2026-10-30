-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/InstOf.lean: from an instance of the proof file's description (`ProofFile.Inst`,
Pub.lean: the request file's bytes, the table's key, the reply file's bytes) to the integer model's
instance at the reference sizes (`Inst.Model.Instance ppref`, Inst/Model/Program.lean: a window of
1,024 tokens, the reply token y, the two numbers r, e); and that this reading agrees with the
description's own reading of the two files. Two definitions with code, and laws on them. No goal is
stated.
Why. A term for the honest side at that description has to say of which model instance a trace is
made. The library has the reading already, at every size: `Johnson.RunOne.reqOfFilesGAt`
(Johnson/RunOne/ClosedGuardAt.lean): the builder `buildReqAt` (Johnson/Flat/ClaimsTrue.lean) behind
the test `readerTakesAt`. Here it is laid at `ProofFile.Inst`, and tied to what the description reads.
"The program's own reader" is ClosedGuardAt.lean's name for what `readerTakesAt` asks: both files
are made of whole words, and two routines of `verify-on-bytes` under OnBytes/Model/,
`Head.stFromCall` and `Head.coveredOf`, return.
  `instReq ξ : Option (ReqAt ppref)` := `reqOfFilesGAt ppref ξ.pub.request ξ.y`; **`instOf ξ`** :
    Option (Instance ppref): its value. They read the two files' bytes: not the table's key, no
    public file, no hash.
  `instOf_bytes`: what is read says the two files byte for byte (`requestBytesOf`, `replyBytesOf`:
    Johnson/Flat/WordsBytes.lean), and r < e, and y = 0 where e < T. `instOf_words`: the same in
    words.
  `instOf_iff`: it returns exactly where the program's own reader takes the two files
    (`readerTakesAt ppref`: whole words; `Head.stFromCall`; `Head.coveredOf`). By `insOf_words`
    (Johnson/Flat/InsOf.lean).
  **`instOf_agrees`**: under hT : Z.p.X.T = 1,024 and hV : Z.p.X.P.h.V = 202,048 (as `ppref.T`,
    `ppref.V`): the first state `startS Z ξ.pub` is not the blank one; the request that the output
    head's seat reads off it (`Kinds.Head.requestOf`, Johnson/Stored/HeadSeatAt.lean) has r, e and
    the tokens of the instance, field by field, and token 0 behind the window; the token of the
    reply that is asked about (`Reply.tokOf ξ.asked`, Johnson/Desc/Reply/ReplyStep.lean) is y;
    `isToken` and `reqForm` say yes. Beneath it `reads_withReq`, `startS_of_instOf`,
    `asked_of_instOf`, `toks_wordsOf`.
  **`instOf_of_hold`**: under hT, hV: wherever the description's tests on the instance pass
    (`holdBy`, Pub.lean), `instOf` returns: the first three of these tests are the reader's.
  `backReq_of_instOf`: the reading of the request file on the soundness side (`Meaning.backReq`,
    Johnson/Meaning/ReqBytes.lean) gives the same request without its reply. Its premise is on
    `instReq`.
  `instOf_of_eq`: every well-formed instance is read back off the two files that say it: so the
    premise "instOf ξ = some x" of the laws above can be met. `instOf_none`, `instOf_empty`:
    controls: where the reader refuses nothing is read; two empty files are refused.
  `held_ok`, `refuse_no`, `size_bytes`: three small helpers.
Limits. The reference sizes `ppref` alone. hT and hV are premises here, and no return of `holdBy` is
shown. `instOf_of_hold` goes one way: `instOf` reads neither the key nor Z, and nothing here says
that `holdBy` returns where `instOf` does. That `buildReqAt ppref` is `Flat.buildReq`
(Johnson/Flat/LedgerClaim.lean), the builder that is laid at the full size (for example in
Johnson/Top/Pub/MoreOwn.lean), is not shown here. THE ACCEPTANCE POLICY IS NO PART OF AN INSTANCE
(Johnson/Flat/Instance.lean's own limit). `instOf` SAYS WHAT THE TWO FILES' BYTES SAY: that a
prover's trace is the model's trace at that instance is for whoever states it to show. Nothing on
whether the model serves an instance, on a trace, on an honest prover or on whether anything is
accepted. Nothing on soundness, on a binding of the commitment (the opening form, `BindsWith`), on
correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.RunOne.ClosedGuardAt
import Johnson.Desc.ProofFile.Pub
import Johnson.Stored.HeadSeatAt
import Johnson.Desc.Reply.ReplyStep
import Johnson.Meaning.ReqBytes
import Johnson.Flat.InstanceLaws
import Johnson.Flat.InsOf
import Johnson.Flat.EarlyApart
import Johnson.Flat.FinIsCanonical
import Johnson.Flat.CoveredAt
import Johnson.Flat.LayBytes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile
open OnBytes OnBytes.Flat OnBytes.Model
open _root_.Inst.Model (ppref Instance)
open Johnson.RunOne (reqOfFilesGAt reqOfFilesAt readerTakesAt reqOfFilesGAt_bytes stmOf)
open VerifiableInference.Desc.First (S)

/-- The request that the request file's and the reply file's bytes say: an instance with the two
facts "r < e" and "y = 0 where e < T" in its type; nothing where the program's own reader refuses
the two files. -/
def instReq (ξ : Inst) : Option (ReqAt ppref) := reqOfFilesGAt ppref ξ.pub.request ξ.y

/-- **The instance that the request file's and the reply file's bytes say**: nothing where the
program's own reader refuses the two files. -/
def instOf (ξ : Inst) : Option (Instance ppref) := (instReq ξ).map (·.val)

/-- **What is read says the two files, byte for byte**, and is well formed. -/
theorem instOf_bytes {ξ : Inst} {x : Instance ppref} (h : instOf ξ = some x) :
    requestBytesOf x = ξ.pub.request ∧ replyBytesOf x = ξ.y ∧ x.r < x.e ∧
      (x.e < ppref.T → x.y.val = 0) := by
  unfold instOf instReq at h
  cases hq : reqOfFilesGAt ppref ξ.pub.request ξ.y with
  | none =>
    rw [hq] at h
    cases h
  | some q =>
    rw [hq] at h
    obtain rfl : q.val = x := Option.some.inj h
    exact ⟨(reqOfFilesGAt_bytes ppref hq).1, (reqOfFilesGAt_bytes ppref hq).2, q.property.1,
      q.property.2⟩

/-- **It returns exactly where the program's own reader takes the two files.** -/
theorem instOf_iff (ξ : Inst) :
    (instOf ξ).isSome = readerTakesAt ppref ξ.pub.request ξ.y := by
  unfold instOf instReq reqOfFilesGAt
  cases t : readerTakesAt ppref ξ.pub.request ξ.y with
  | false => rfl
  | true =>
    rw [if_pos rfl]
    unfold readerTakesAt at t
    simp only [Bool.and_eq_true, beq_iff_eq] at t
    obtain ⟨-, t⟩ := t
    cases hs : Head.stFromCall (Verify.words32 ξ.pub.request) (Verify.words32 ξ.y) ppref.T with
    | error e =>
      rw [hs] at t
      cases t
    | ok so =>
      rw [hs] at t
      cases hc : Head.coveredOf so ppref.T ppref.V with
      | error e =>
        have t1 : (Head.coveredOf so ppref.T ppref.V).toBool = true := t
        rw [hc] at t1
        cases t1
      | ok cov =>
        obtain ⟨i, g0, -, -, -, -, -, w1, w2⟩ :=
          insOf_words (P := ppref) (x := stmOf ξ.pub.request ξ.y) hs hc
        have e : reqOfFilesAt ppref ξ.pub.request ξ.y = some ⟨i, w1, w2⟩ := by
          show (buildOf ppref _ _).bind _ = _
          rw [show buildOf ppref (K.promptOf (stmOf ξ.pub.request ξ.y),
            K.outputOf (stmOf ξ.pub.request ξ.y)) (K.auxOf (stmOf ξ.pub.request ξ.y)) = some i from
                g0]
          show (if h : WellFormedAt i then some (⟨i, h⟩ : ReqAt ppref) else none) = _
          rw [dif_pos ⟨w1, w2⟩]
        rw [e]
        rfl

/-- The tokens that the state's reader reads off the words of an instance. -/
theorem toks_wordsOf {P : _root_.Inst.Model.Params} (x : Instance' P) (hV : P.V ≤ 2 ^ 32) (i : Nat)
    :
    (((requestWordsOf x).extract 0 P.T).map (·.toNat)).getD i 0 =
      if h : i < P.T then (x.prompt ⟨i, h⟩).val else 0 := by
  unfold requestWordsOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_extract]
  split
  · rename_i h
    have h' : i < P.T := by simpa using h
    rw [dif_pos h']
    simp [Array.getElem?_append, h', UInt32.toNat_ofNat']
    have := (x.prompt ⟨i, h'⟩).isLt
    omega
  · rename_i h
    have h' : ¬ i < P.T := by simpa using h
    rw [dif_neg h']
    rfl

/-- The request file's and the reply file's words are the instance's. -/
theorem instOf_words {ξ : Inst} {x : Instance ppref} (h : instOf ξ = some x) :
    Verify.words32 ξ.pub.request = requestWordsOf x ∧ Verify.words32 ξ.y = replyWordsOf x := by
  obtain ⟨e1, e2, -, -⟩ := instOf_bytes h
  constructor
  · rw [← e1]
    exact words32_bytesOfWords _
  · rw [← e2]
    exact words32_bytesOfWords _

section
variable {Z : Pub} (hT : Z.p.X.T = ppref.T) (hV : Z.p.X.P.h.V = ppref.V) {ξ : Inst}
  {x : Instance ppref} (h : instOf ξ = some x)
include h

/-- What the state with the request's words laid reads of them. -/
theorem reads_withReq (s₀ : S) :
    (s₀.withReq (Verify.words32 ξ.pub.request)).reqT = ppref.T ∧
      (s₀.withReq (Verify.words32 ξ.pub.request)).rowR = x.r ∧
      (s₀.withReq (Verify.words32 ξ.pub.request)).rowE = x.e ∧
      ∀ i, (s₀.withReq (Verify.words32 ξ.pub.request)).tokv.getD i 0 =
        if k : i < ppref.T then (x.prompt ⟨i, k⟩).val else 0 := by
  rw [(instOf_words h).1]
  have hs : (s₀.withReq (requestWordsOf x)).reqT = ppref.T := by
    show (requestWordsOf x).size - 2 = ppref.T
    rw [size_requestWordsOf]
    rfl
  have hr : x.r < 2 ^ 32 := lt_of_le_of_lt (Nat.lt_succ_iff.1 x.rF.isLt) (by decide)
  have he : x.e < 2 ^ 32 := lt_of_le_of_lt x.e_le (by decide)
  refine ⟨hs, ?_, ?_, fun i => ?_⟩
  · show ((requestWordsOf x).getD (s₀.withReq (requestWordsOf x)).reqT 0).toNat = x.r
    rw [hs, requestWordsOf_r, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hr]
  · show ((requestWordsOf x).getD ((s₀.withReq (requestWordsOf x)).reqT + 1) 0).toNat = x.e
    rw [hs, requestWordsOf_e, UInt32.toNat_ofNat', Nat.mod_eq_of_lt he]
  · show (((requestWordsOf x).extract 0 (s₀.withReq (requestWordsOf x)).reqT).map (·.toNat)).getD i
      0
      = _
    rw [hs]
    exact toks_wordsOf x (by decide) i

include hT hV

/-- The first state is not the blank one: the tests on the request that read no reply pass. -/
theorem startS_of_instOf : startS Z ξ.pub = Z.s₀.withReq (Verify.words32 ξ.pub.request) := by
  obtain ⟨-, -, w1, -⟩ := instOf_bytes h
  obtain ⟨r0, r1, r2, r3⟩ := reads_withReq h Z.s₀
  unfold startS
  have ok : (Z.s₀.withReq (Verify.words32 ξ.pub.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
    unfold S.reqOk
    rw [hT, hV, r1, r2]
    have sz : (Z.s₀.withReq (Verify.words32 ξ.pub.request)).req.size = ppref.T + 2 := by
      show (Verify.words32 ξ.pub.request).size = _
      rw [(instOf_words h).1, size_requestWordsOf]
    have e3 := x.e_le
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not, Array.all_eq_true, decide_eq_true_eq]
    refine ⟨⟨sz, fun i hi => ?_⟩, by omega, by omega⟩
    have g := r3 i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at g
    have g' : (Z.s₀.withReq (Verify.words32 ξ.pub.request)).tokv[i] =
        if k : i < ppref.T then (x.prompt ⟨i, k⟩).val else 0 := g
    rw [g']
    split
    · exact (x.prompt _).isLt
    · decide
  simp only [ok, if_true]

end

section
variable {Z : Pub} (hT : Z.p.X.T = ppref.T) (hV : Z.p.X.P.h.V = ppref.V) {ξ : Inst}
  {x : Instance ppref} (h : instOf ξ = some x)
include h

/-- The reply that is asked about is the instance's token. -/
theorem asked_of_instOf :
    OnBytes.Desc.Reply.tokOf ξ.asked = x.y.val ∧
      OnBytes.Desc.Reply.isToken ppref.V ξ.asked = true := by
  have e : OnBytes.Desc.Reply.tokOf ξ.asked = x.y.val := by
    show (askedReplyOf ξ.y).c0.toNat = x.y.val
    rw [askedReplyOf_c0, (instOf_words h).2]
    show (UInt32.ofNat x.y.val).toNat = _
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans x.y.isLt (by decide))
  refine ⟨e, ?_⟩
  unfold OnBytes.Desc.Reply.isToken
  have e' : ξ.asked.c0.toNat = x.y.val := e
  rw [e']
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨rfl, rfl⟩, x.y.isLt⟩

include hT hV

/-- **THE INSTANCE AGREES WITH THE DESCRIPTION's OWN READING OF THE TWO FILES**: with the request
that the output head's seat reads off the first state, field by field, and with the token of the
reply that is asked about. -/
theorem instOf_agrees :
    startS Z ξ.pub = Z.s₀.withReq (Verify.words32 ξ.pub.request) ∧
      (VerifiableInference.Desc.Kinds.Head.requestOf (startS Z ξ.pub)).r = x.r ∧
      (VerifiableInference.Desc.Kinds.Head.requestOf (startS Z ξ.pub)).e = x.e ∧
      (∀ t : Fin ppref.T,
        (VerifiableInference.Desc.Kinds.Head.requestOf (startS Z ξ.pub)).tok t.val =
          (x.prompt t).val) ∧
      (∀ i, ppref.T ≤ i →
        (VerifiableInference.Desc.Kinds.Head.requestOf (startS Z ξ.pub)).tok i = 0) ∧
      OnBytes.Desc.Reply.tokOf ξ.asked = x.y.val ∧
      OnBytes.Desc.Reply.isToken ppref.V ξ.asked = true ∧
      OnBytes.Desc.Reply.reqForm ppref.T x.r x.e x.y.val = true := by
  obtain ⟨-, -, w1, w2⟩ := instOf_bytes h
  obtain ⟨-, r1, r2, r3⟩ := reads_withReq h Z.s₀
  obtain ⟨a1, a2⟩ := asked_of_instOf h
  have es := startS_of_instOf hT hV h
  rw [es]
  refine ⟨rfl, r1, r2, fun t => ?_, fun i hi => ?_, a1, a2, ?_⟩
  · show (Z.s₀.withReq (Verify.words32 ξ.pub.request)).tokv.getD t.val 0 = _
    rw [r3, dif_pos t.isLt]
  · show (Z.s₀.withReq (Verify.words32 ξ.pub.request)).tokv.getD i 0 = _
    rw [r3, dif_neg (Nat.not_lt.2 hi)]
  · unfold OnBytes.Desc.Reply.reqForm
    have e3 := x.e_le
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨w1, e3⟩, ?_⟩
    by_cases k : x.e = ppref.T
    · exact Or.inl k
    · exact Or.inr (w2 (by omega))

end

/-- A step of `holdBy` that has returned. -/
theorem held_ok {α : Type} {at_ : String} {y : Except String α} {a : α}
    (h : held at_ y = .ok a) : y = .ok a := by
  cases y with
  | error e => cases h
  | ok b =>
    have e : b = a := Except.ok.inj (h : (Except.ok b : Except (String × String) α) = .ok a)
    rw [e]

/-- A refusal that did not come. -/
theorem refuse_no {b : Bool} {name : String} {u : Unit} (h : refuseIf b name = .ok u) :
    b = false := by
  cases b
  · rfl
  · cases h

/-- **Wherever the description's tests on the instance pass, the instance is read.** -/
theorem instOf_of_hold {o : SecondHashFunctionArgument} {mk : LinksBy} {Z : Pub} (hT : Z.p.X.T = ppref.T)
    (hV : Z.p.X.P.h.V = ppref.V) {ξ : Inst} {G : Ground} (h : holdBy o mk Z ξ = .ok G) :
    (instOf ξ).isSome = true := by
  rw [instOf_iff]
  unfold holdBy at h
  obtain ⟨_, h1, h⟩ := OnBytes.Params.exc_bind h
  obtain ⟨so, h2, h⟩ := OnBytes.Params.exc_bind h
  obtain ⟨cov, h3, -⟩ := OnBytes.Params.exc_bind h
  have k1 := refuse_no (held_ok h1)
  have k2 := held_ok h2
  have k3 := held_ok h3
  rw [hT] at k2 k3
  rw [hV] at k3
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at k1
  unfold readerTakesAt
  rw [k2]
  show (_ && _ && (Head.coveredOf so ppref.T ppref.V).toBool) = true
  rw [k3, k1.1, k1.2]
  rfl

/-- The reading of the request file on the soundness side agrees. -/
theorem backReq_of_instOf {ξ : Inst} {q : ReqAt ppref} (h : instReq ξ = some q) :
    Meaning.backReq ξ.pub.request = some (reqWithoutReply q) := by
  rw [← (reqOfFilesGAt_bytes ppref h).1]
  exact Meaning.backReq_bytes q

/-- Words laid as bytes: four bytes a word. -/
theorem size_bytes (w : Array UInt32) : (bytesOfWords w).size = 4 * w.size := by
  unfold bytesOfWords
  rw [size_catWords, Array.length_toList]

/-- **Every well-formed instance is read back off the two files that say it**, whatever the table's
key: so the premise "instOf ξ = some x" can be met at every such x (lay the two files and any key
into ξ: f1 and f2 then hold by definition, and `by dsimp only` closes them). -/
theorem instOf_of_eq {ξ : Inst} (q : ReqAt ppref) (f1 : ξ.pub.request = requestBytesOf q.val)
    (f2 : ξ.y = replyBytesOf q.val) : instOf ξ = some q.val := by
  have hs := stFromCall_wordsOf q.val (by decide) (by decide) q.property.1 q.property.2
  obtain ⟨cov, hc⟩ := coveredOf_wordsOf q.val (by decide) (by decide) q.property.1
  have t : readerTakesAt ppref (requestBytesOf q.val) (replyBytesOf q.val) = true := by
    unfold readerTakesAt
    rw [show Verify.words32 (requestBytesOf q.val) = requestWordsOf q.val from
      words32_bytesOfWords _, show Verify.words32 (replyBytesOf q.val) = replyWordsOf q.val from
      words32_bytesOfWords _, hs]
    show (_ && _ && (Head.coveredOf _ ppref.T ppref.V).toBool) = true
    rw [hc]
    have s1 : (requestBytesOf q.val).size % 4 = 0 := by
      unfold requestBytesOf
      rw [size_bytes]
      omega
    have s2 : (replyBytesOf q.val).size % 4 = 0 := by
      unfold replyBytesOf
      rw [size_bytes]
      omega
    rw [s1, s2]
    rfl
  have hi : (instOf ξ).isSome = true := by
    rw [instOf_iff, f1, f2]
    exact t
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hi
  obtain ⟨e1, e2, -, -⟩ := instOf_bytes hx
  have ey : x.y = q.val.y := by
    have a1 := (asked_of_instOf hx).1
    have a2 : OnBytes.Desc.Reply.tokOf ξ.asked = q.val.y.val := by
      show (askedReplyOf ξ.y).c0.toNat = _
      rw [askedReplyOf_c0, f2]
      exact Meaning.asked_word q
    exact Fin.ext (a1.symm.trans a2)
  have el : layB x = layB q.val := by
    unfold layB
    rw [e1, f1, ey]
  have u1 := unlayB_layB (P := ppref) (by decide) (by decide) x
  have u2 := unlayB_layB (P := ppref) (by decide) (by decide) q.val
  rw [el, u2] at u1
  rw [hx, ← Option.some.inj u1]

/-- A control: where the program's reader refuses the two files nothing is read. -/
theorem instOf_none {ξ : Inst} (h : readerTakesAt ppref ξ.pub.request ξ.y = false) :
    instOf ξ = none := by
  have e := instOf_iff ξ
  rw [h] at e
  exact Option.not_isSome_iff_eq_none.1 (by rw [e]; decide)

/-- A control: two empty files are refused. -/
theorem instOf_empty (k : TableKey) : instOf ⟨⟨ByteArray.empty, k⟩, ByteArray.empty⟩ = none :=
  instOf_none (show readerTakesAt ppref ByteArray.empty ByteArray.empty = false by
    decide +kernel)

end ProofFile

#print axioms ProofFile.instOf_bytes
#print axioms ProofFile.instOf_iff
#print axioms ProofFile.toks_wordsOf
#print axioms ProofFile.instOf_words
#print axioms ProofFile.reads_withReq
#print axioms ProofFile.startS_of_instOf
#print axioms ProofFile.asked_of_instOf
#print axioms ProofFile.instOf_agrees
#print axioms ProofFile.held_ok
#print axioms ProofFile.refuse_no
#print axioms ProofFile.instOf_of_hold
#print axioms ProofFile.backReq_of_instOf
#print axioms ProofFile.size_bytes
#print axioms ProofFile.instOf_of_eq
#print axioms ProofFile.instOf_none
#print axioms ProofFile.instOf_empty
