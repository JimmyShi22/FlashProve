-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean: the closed check of an entry file, `verifyEntryFull` and
`verifyEntrySmall`, and a form of it that is written for evaluation.

This file holds no run, and no theorem says that a term here comes home or says yes on anything:
these are facts of runs, and this head reports none.

What this file states, assumes and does not show, its terms and its limits in full: the comment on
`verifyEntryFull`.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictRd
import OnBytes.TypedOracleCompiler.Slice.AskedWords
import OnBytes.TypedOracleCompiler.Run.EntryPageSafeO
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictShortEq
import OnBytes.Flat.LinkSibFit
import Run.CodingBitsLaws

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.EntryRunTop
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryFillRun TypedOracleCompiler.Slice.EntryReadsAt
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.EntryPageSafe
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (hcfg : D.base.cfg.size = 32) (d₁ : Sd1 lg s)
  (sh : OnBytes.Params.IndexShape) (pd : Dig 256) (O : ByteArray → ByteArray)

/-- `famOfG` in the form that hashes bytes: a hash function on bytes an argument. -/
def famOfO : Fam (typedOracleFamily 256 (D.K + 1) (Ls D d₁)) :=
  famSafeO D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (d₁, d₁)
    (pinsE D d₁ (cfgOf D) hcfg pd (restAt D sh)) (D.K + 1) (8 * saltOf D) (backOf D d₁) O

/-- It is `famOfG` at `gOf O`. -/
theorem famOfO_G : famOfO D hcfg d₁ sh pd O = famOfG D hcfg d₁ sh pd (gOf O) :=
  famSafeO_G _ _ _ _ _ _ _ _ _

end TypedOracleCompiler.Slice.EntryRunTop

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.EntryPageSafe (gOf gOf_oracle toBytesT)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of seedEntry seedOfDrawnC)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁ scAt)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- `entryPartG` in the form for a run: the family hashes bytes (`famOfO`), and the seeds'
comparison and the lax verifier go along short lists (`cmpEL`, `laxEL`,
OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean). -/
def entryPartO (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (a : AskedE)
    (O : ByteArray → ByteArray) : Bool :=
  pinsFit (entryXD G c) G.q.link.table &&
    match assembleS (entryXD G c)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
    | none => false
    | some π =>
      cmpEL (entryXD G c) (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)
          (seedOfDrawnC G.q.link.table.cubeBits G.q.link.table.answers)
          (EntryRunTop.famOfO (entryXD G c) hc (d1Run G.q.link.table.cubeBits
            G.q.link.table.answers)
            G.q.link.table pd O)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] 0
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2 &&
        laxEL (entryXD G c) _ (bodyS (entryXD G c).a (entryXD G c).base.plan.salt)
          (ownES (entryXD G c) (hok c hc))
          (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (fun _ => TSE (entryXD G c) (seedEntry G.q.link.table.cubeBits G.q.link.table.answers))
          (EntryRunTop.famOfO (entryXD G c) hc (d1Run G.q.link.table.cubeBits
            G.q.link.table.answers)
            G.q.link.table pd O)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root]
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a) π

/-- It is `entryPartG` at `gOf O`: on all arguments. -/
theorem entryPartO_eq (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (a : AskedE)
    (O : ByteArray → ByteArray) :
    entryPartO G hok c hc pd a O = entryPartG G hok c hc pd a (gOf O) := by
  unfold entryPartO entryPartG
  rw [EntryRunTop.famOfO_G]
  cases assembleS (entryXD G c)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
  | none => rfl
  | some π =>
    simp only []
    rw [yesShort_eq (entryXD G c) (hok c hc) _ _ _
      [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] rfl]

/-- The check does not hang on how its two digests are written. -/
theorem entryPartG_congr {c c' : ByteArray} (e : c = c') (hc : c.size = 32) (hc' : c'.size = 32)
    {pd pd' : Dig 256} (ep : pd = pd') (a : AskedE) (g : Fam (rom 256)) :
    entryPartG G hok c hc pd a g = entryPartG G hok c' hc' pd' a g := by
  subst e ep
  rfl

/-- g's own value at the first public string. -/
theorem own₀_scAt (cfg : Cfg) (g : Fam (rom 256)) :
    own₀ (pubS₀ cfg) g (scAt cfg) = g () (scAt cfg) := by
  have h : scAt cfg ∈ pubS₀ cfg := Finset.mem_singleton_self _
  unfold own₀ OnBytes.Slice.Shapes.cutT
  rw [if_pos h]
  rfl

/-- g's own value at the string of the parameter bytes at its own first digest. -/
theorem own₁_s0Of (cfg : Cfg) (prm : ByteArray → ByteArray) (g : Fam (rom 256)) :
    own₁ (pubS₀ cfg) (pubS₁ [prm] cfg) g (s0Of (prm (dgOf cfg (own₀ (pubS₀ cfg) g)))) =
      g () (s0Of (prm (dgOf cfg (own₀ (pubS₀ cfg) g)))) := by
  have h : s0Of (prm (dgOf cfg (own₀ (pubS₀ cfg) g))) ∈
      pubS₁ [prm] cfg (own₀ (pubS₀ cfg) g) := by
    unfold pubS₁
    exact List.mem_toFinset.2 (List.mem_singleton.2 rfl)
  unfold own₁ OnBytes.Slice.Shapes.cutT
  rw [if_pos h]
  rfl

/-- `verifyEntryG` in the form for a run: both digests are bound first, as bytes, ahead of all that
reads them: b₀ is O's answer at the string of the three public files, b₁ its answer at the string of
the parameter bytes at the digest made of b₀. That a run then hashes each once is a fact of compiled
code, no theorem. -/
def verifyEntryO (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) : Bool :=
  let b₀ := O (toBytesT (scAt cfg))
  let c := _root_.Run.digToBytes (_root_.Run.digS b₀)
  let b₁ := O (toBytesT (s0Of (G.bytesAt c)))
  entryPartO G hok c (_root_.Run.size_digToBytes _) (_root_.Run.digS b₁) a O

/-- It is `verifyEntryG` at `gOf O`: on all arguments. -/
theorem verifyEntryO_eq (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    verifyEntryO G hok cfg a O = verifyEntryG G hok cfg a (gOf O) := by
  have e0 : dgOf cfg (own₀ (pubS₀ cfg) (gOf O)) =
      _root_.Run.digToBytes (_root_.Run.digS (O (toBytesT (scAt cfg)))) := by
    show _root_.Run.digToBytes (own₀ (pubS₀ cfg) (gOf O) (scAt cfg)) = _
    rw [own₀_scAt]
    rfl
  unfold verifyEntryO verifyEntryG
  dsimp only
  rw [entryPartO_eq]
  refine entryPartG_congr G hok e0.symm _ _ ?_ a _
  rw [own₁_s0Of, e0]
  rfl

/-- At the format's oracle on bytes it is `verifyEntryG` at the realised oracle on bit strings. -/
theorem verifyEntryO_oracle (cfg : Cfg) (a : AskedE) :
    verifyEntryO G hok cfg a _root_.Fmt.oracle = verifyEntryG G hok cfg a _root_.Run.oBits := by
  rw [verifyEntryO_eq, gOf_oracle]

/-! ## At the realised oracle -/

/-- At the realised oracle the two digests that the check asks for are the format's own: the digest
of the three public files, and the digest of the parameter bytes at it. Asked: what is hashed for
the first is within the hash's bound on lengths. The limits: the comment on `verifyEntryFull`. -/
theorem verifyEntryG_oBits (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) (a : AskedE) :
    verifyEntryG G hok cfg a _root_.Run.oBits =
      entryPartG G hok (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        (OnBytes.Params.configurationDigest_size _)
        (EntryRunTop.pdOf (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay,
          cfg.KL])))
        a _root_.Run.oBits := by
  have e0 := OnBytes.Slice.Shapes.dgOf_own₀ cfg hb
  have hpd := (homeOf G hok 0).pd_own₁ cfg hb
    (params_le_of_ok _ (hok _ (OnBytes.Params.configurationDigest_size _)))
    (homeOf_prm G hok 0 _)
  unfold verifyEntryG
  refine entryPartG_congr G hok e0 _ _ ?_ a _
  rw [e0]
  exact hpd

/-- So `verifyE`, at a statement whose digest is that of the three public files, is the check at the
realised oracle, and the comparison of the commitment ID. -/
theorem verifyE_entryG (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) (id : String)
    (a : AskedE) :
    verifyE G hok ⟨id, OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL],
        OnBytes.Params.configurationDigest_size _⟩ a =
      (verifyEntryG G hok cfg a _root_.Run.oBits &&
        (stmtId G.q.link.table (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
          (_root_.Run.bytesToDig a.first.root)
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1 == id)) := by
  rw [verifyE_split, verifyEntryG_oBits G hok cfg hb a]

/-! ## Tests on the parsed value -/

/-- Tests on the plain data that a parser hands over, at a table's shape sh: every word of a field's
element in the chain as read is below the prime (`askedWords`); every opened leaf's salt has the
shape's number of bytes; the run's value is not 32 zero bytes; every round's nonce is below 2 ^ 64;
both roots have 32 bytes; both lists of answers have the shape's length, 2 ^ v * answers; every
answer's three words are canonical; the chain's salt has 32 bytes. No hash function is asked. The
limits: the comment on `verifyEntryFull`. -/
def askedFit (sh : OnBytes.Params.IndexShape) (a : AskedE) : Bool :=
  askedWords a &&
    (a.out.rounds.toList.all fun ro => ro.opens.all fun y =>
      y.2.2.salts.all fun s => s.size == sh.saltBytes) &&
    a.out.run.all _root_.Fmt.runOk &&
    (a.out.rounds.toList.all fun ro => decide (ro.nonce < 2 ^ 64)) &&
    (a.first.root.size == 32) && (a.further.root.size == 32) &&
    (a.first.answers.length == 2 ^ sh.v * sh.answers) &&
    (a.further.answers.length == 2 ^ sh.v * sh.answers) &&
    a.first.answers.all OnBytes.okE && a.further.answers.all OnBytes.okE &&
    (match a.out.run with
      | some r => r.size == 32
      | none => false)

/-- Where the tests say yes, both roots have 32 bytes. -/
theorem askedFit_roots (sh : OnBytes.Params.IndexShape) (a : AskedE) (h : askedFit sh a = true) :
    a.first.root.size = 32 ∧ a.further.root.size = 32 := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.1 h.1.1.1.1.1.1.2, beq_iff_eq.1 h.1.1.1.1.1.2⟩

/-- Where the tests say yes, every round's nonce as read is below 2 ^ 64. -/
theorem askedFit_nonces (sh : OnBytes.Params.IndexShape) (a : AskedE) (h : askedFit sh a = true) :
    ∀ ro ∈ a.out.rounds.toList, ro.nonce < 2 ^ 64 := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  have hN := h.1.1.1.1.1.1.1.2
  simp only [List.all_eq_true, decide_eq_true_eq] at hN
  exact hN

/-- Where the tests say yes, every word of a field's element in the chain as read is below the
prime. -/
theorem askedFit_words (sh : OnBytes.Params.IndexShape) (a : AskedE) (h : askedFit sh a = true) :
    askedWords a = true := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- Where the tests say yes, every salt of every opening of every round has the shape's number of
bytes. -/
theorem askedFit_salts (sh : OnBytes.Params.IndexShape) (a : AskedE) (h : askedFit sh a = true) :
    ∀ ro ∈ a.out.rounds.toList, ∀ y ∈ ro.opens, ∀ s ∈ y.2.2.salts, s.size = sh.saltBytes := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  have hS := h.1.1.1.1.1.1.1.1.1.2
  simp only [List.all_eq_true, beq_iff_eq] at hS
  exact hS

/-- Where the tests say yes, the run's value is not 32 zero bytes. -/
theorem askedFit_runOk (sh : OnBytes.Params.IndexShape) (a : AskedE) (h : askedFit sh a = true) :
    ∀ r, a.out.run = some r → _root_.Fmt.runOk r = true := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  have hZ := h.1.1.1.1.1.1.1.1.2
  intro r hr
  rw [hr] at hZ
  exact hZ

/-- Where the tests say yes, the instance that the check reads is the instance made of the two typed
records that are read off the parsed value. -/
theorem askedFit_recX (sh : OnBytes.Params.IndexShape) (lg : ℕ) (a : AskedE)
    (h : askedFit sh a = true) :
    OnBytes.Flat.recX (OnBytes.Flat.recsOf sh.v lg sh.answers a) = xOfAskedC lg sh.answers a := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  exact OnBytes.Flat.recX_recsOf sh.v lg sh.answers a (beq_iff_eq.1 h.1.1.1.1.2)
    (beq_iff_eq.1 h.1.1.1.2) (List.all_eq_true.1 h.1.1.2) (List.all_eq_true.1 h.1.2)

/-- Where the tests say yes, the typed string's salt has 256 bits. -/
theorem askedFit_salt (sh : OnBytes.Params.IndexShape) (a : AskedE) (h : askedFit sh a = true)
    {X : Type} (D : XD) (dec : X → _root_.Run.PQ.View → Bool) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec a.out = some π) : π.salt.length = 256 := by
  unfold askedFit at h
  simp only [Bool.and_eq_true] at h
  have hr := h.2
  unfold assembleS at hπ
  cases hrun : a.out.run with
  | none =>
    rw [hrun] at hr
    cases hr
  | some r =>
    rw [hrun] at hr hπ
    have h32 : r.size = 32 := beq_iff_eq.1 hr
    split at hπ
    · rename_i run pl tab tx e1 e2 e3 e4
      obtain rfl := Option.some.inj e1
      obtain rfl := Option.some.inj hπ
      show (_root_.Run.bytesToBits r).length = 256
      rw [_root_.Run.length_bytesToBits, h32]
    · cases hπ

/-! ## The closed terms -/

/-- The check at the full size: the tests on the parsed value, then `verifyEntryG` at the full-size
ground. No letter is left but the three public files, the parsed value and the hash function.

This file states: definitions and equations. `verifyEntryFull cfg a g` and
`verifyEntrySmall cfg a g` are Booleans made of the three public files cfg, a parsed value a
and a hash function g alone: tests on the parsed value (`askedFit`), then the check `verifyEntryG`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean) at the reference parameters of the full size or of the small
example. `runEntryFull` and `runEntrySmall` take a hash function O on bytes and are written for
evaluation; they are the closed checks at the function `gOf O`, on all arguments (`runEntryFull_eq`,
`runEntrySmall_eq`). `verifyE_entryG`: the check `verifyE` (OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean), at
a statement whose digest is that of the three public files, is `verifyEntryG` at the format's hash
as a function on bit strings (`Run.oBits`) and the comparison of the commitment ID.

It assumes: no hypothesis in the equations of the closed checks; their variables are cfg, a and g or
O. `verifyEntryG_oBits` and `verifyE_entryG` ask one bound on the lengths of the public files, which
is shown at no file. In the general forms the reference parameters G are a variable: a record of
data with laws (`EntryGround`, OnBytes/Tie/EntryGround.lean), and hok, that the description made of
G is in order at every digest of 32 bytes, is a hypothesis; at the two closed checks both are
written terms. The general forms ask also that the digest has 32 bytes (hc, hcfg). The laws of
`askedFit` ask that it says yes, and `askedFit_salt` besides that the typing returns a value.

It does not show: that any term here says yes on anything or ends when it is evaluated. No bound, no
probability, nothing on soundness. The roots, the answers, the seeds and the run's value come out of
the parsed value: a yes is a yes for the roots and answers that the parser named. Not every field of
the value is read, and the closed check does not refuse all that "read strictly, then check"
refuses. The tests on the parsed value are no part of the checker of which the bounds speak; that
honest files pass them is not shown here. The closed checks do not look at the commitment ID, and
the parameter file's lines are not tested against the reference parameters. The closed checks are
written by hand
and are not the compiler's output by their text. The tie is `verifyEntryG_iff`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean): at every function `verifyEntryG` says yes exactly if the
pins fit and the checker of the entry's part, at the converter that hands over a, returns a value.
The verifier in that checker is the lax one of Link out of the compiler under OnBytes/TypedOracleCompiler/, another
form of the library's. The limits in full, for
every statement of this file: below.

Terms: lean/GLOSSARY.md. In the comments of this file a "letter" is a variable, an "arm" is the
check of one file taken as a protocol, a "ground" is a set of reference parameters typed in Lean,
the "pins" are the constants in the strings that are hashed, a "family" gives an answer to each
typed query, "comes home" means that an evaluation ends, and a "run" is an evaluation by Lean's
evaluator or of compiled code ("the run's value" is another thing: GLOSSARY.md, run's value). Where
a comment of this file names the head of a file, read with it the comment to which that head points.

THE LIMITS.

OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean: the check of an entry file in the form for a run, with its
equation to `verifyEntryG`; what the check is at the realised oracle; tests on the parsed value; and
the closed terms at the two written grounds.

Definitions, and statements with their proofs. `verifyEntryG` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean)
has code, but by the heads of the files on its walk `whyOutE` does not run at the full size, and its
family keeps answers as functions on bits: of a like form the head of
OnBytes/TypedOracleCompiler/Run/CodingFnThin.lean reports 256 calls of the hash for one digest; of this one nothing
is measured. Here the same check is written with the family that hashes bytes (`famSafeO`,
OnBytes/TypedOracleCompiler/Run/EntryPageSafeO.lean) and with the seeds' comparison and the lax verifier along short
lists (`cmpEL`, `laxEL`, OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean), and is shown equal to
`verifyEntryG` at `gOf O`, for all other arguments (`yesShort_eq`,
OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean).

Main names:
  `EntryRunTop.famOfO`, `famOfO_G`: `famOfG` in the form that hashes bytes; it is `famOfG` at
    `gOf O`.
  `entryPartO`, `entryPartO_eq`: the form for a run is `entryPartG` at `gOf O`, on all arguments.
  `verifyEntryO`: both digests are bound first, as bytes, ahead of all that reads them (that a run
    then hashes each once is a fact of compiled code, no theorem).
    `own₀_scAt`, `own₁_s0Of`: g's own
    values at the two public strings.
    `verifyEntryO_eq`: it is `verifyEntryG` at `gOf O`, on all arguments. `verifyEntryO_oracle`: at
    `Fmt.oracle` it is `verifyEntryG` at `Run.oBits`.
  `verifyEntryG_oBits`: at `Run.oBits` the two digests that the check asks for are the format's own:
    it is `entryPartG` at `Params.configurationDigest` of the three public files and `pdOf` there.
    Asked: one bound on lengths, shown at no file. `verifyE_entryG`: so `verifyE` at that digest is
    `verifyEntryG` at `Run.oBits` and the comparison of the commitment ID.
  `askedFit sh a` : Bool: every word of a field's element in the chain as read is below the prime
    (`askedWords`, OnBytes/TypedOracleCompiler/Slice/AskedWords.lean); every opened leaf's salt has the shape's
    number of bytes; the run's value is not 32 zero bytes; every round's nonce is below 2 ^ 64; both
    roots have 32 bytes; both lists of answers have the shape's length; every answer's three words
    are canonical; the chain's salt has 32 bytes. `askedFit_words`, `askedFit_salts`,
    `askedFit_runOk`, `askedFit_nonces`, `askedFit_roots`. `askedFit_recX`: then the instance that
    the check reads is `Flat.recX` of the two typed records read off a (`recX_recsOf`,
    OnBytes/Flat/LinkSibFit.lean). `askedFit_salt`: then the typed string's salt has 256 bits.
  `verifyEntryFull`, `verifyEntrySmall` cfg a g : Bool: `askedFit` and `verifyEntryG` at
    `recordGround` | `smallRecordGround`: no letter is left but the three public files, the parsed
    value and the hash function. `verifyEntryFull_iff`, `verifyEntrySmall_iff`.
  `runEntryFull`, `runEntrySmall` cfg a O : Bool; `runEntryFull_eq`, `runEntrySmall_eq`: the form
    for a run is the closed check at `gOf O`, on all arguments.

Limits.
  1. This file holds no run, and no theorem says that a term here comes home or says yes on
     anything: these are facts of runs, and this head reports none. The equations say that two terms
     have one verdict, not which.
  2. The tests on the parsed value are no part of the checker of which the bounds speak: they can
     only make the check refuse more. Why the last eight stand here: without them a yes does not
     give what a tie to the arm at the three files' own object asks (a list with one answer more, or
     a shorter salt, has the same decision and another first string; byte strings of several lengths
     are one typed root; a nonce is a natural number in the parsed value, and a file spells one in
     at most eight bytes, R8.2 in Fmt/Rules8.lean, so that one of 2 ^ 64 or more is read off no
     file). The first three are asked by no tie and no bound of this library: they repeat three
     refusals of the format's reader, for a value that comes from a parser which has passed no such
     reader: that reader refuses a word that is not below the prime (the test's prime is that of the
     program's field, whatever field a plan names), reads every leaf's salt at the verifier's own
     length, and refuses a run's value of 32 zero bytes (`Fmt.rdElt`, `Fmt.rdOpening`, `Fmt.runOk`).
     The tests test nothing of the two lists of seeds. That honest files pass them is not shown
     here. Of the first three the laws are not in this library; of the other eight no law ends in
     the tests' own terms at these values; a piece lies at another reader (`cutChain_facts`,
     Run/OneIsTypedFullProofs.lean).
  3. The closed terms take from the user the three public files alone. The two roots, both tables'
     answers and the seeds come out of a: a yes is a yes for the roots and answers that the parser
     named. The run's value, which is the typed string's salt and the start of every own leaf's,
     comes out of a too; tested are its length and that it is not 32 zero bytes. The format's reader
     makes it itself, as the hash number 172 of the parameters' digest and 32 random bytes of the
     file (`runValueW`, Fmt/Rules4.lean): so the closed check does not refuse run's values that no
     file spells. A nonce in a round without work is tested to be below 2 ^ 64 and then dropped. Not
     every field of the parsed value is read. By the text of the typing (`assembleS`,
     OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean), and by no theorem: of an opening the given digests, the
     root and the place behind it are not read (each path is looked up in the opening's record of
     vertices met, and of that record the siblings on a listed place's way alone); of a round the
     message's bytes, what was drawn and the list are not; of the chain the parameters' digest, its
     two chaining values and its own record of vertices are not. Nor are all forms tested that the
     format's reader tests: that the places of an opening increase and lie below the tree's size,
     that its places, columns and salts are equally many, that a root among a round's values and a
     vertex in an opening's record have 32 bytes, the number of openings and their shapes are not.
     So the closed check does not refuse all that "read strictly, then check" refuses. The
     commitment ID is not looked at: another part. The parameter file's lines are not tested against
     the ground.
  4. The closed terms are not the compiler's output by their text. They are written by hand: the
     tests on the parsed value, the pins' test, the typing of the chain (`assembleS`), the seeds'
     comparison, and a form of the lax verifier of Link out of the compiler under OnBytes/TypedOracleCompiler/. The
     tie is `verifyEntryG_iff` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean): at every function
     `verifyEntryG` says yes exactly if the pins fit and the checker of the entry's part, at the
     converter that hands over a, returns a value. `runEntryFull` and `runEntrySmall` are shown
     equal to the closed checks at the functions `gOf O` alone.
  5. All that the heads of EntryVerdictG.lean, EntryVerdictRd.lean, EntryPageSafeO.lean and
     EntryVerdictShortEq.lean do not claim. No bound is joined here. No probability stands here.
     Nothing on soundness.
-/
def verifyEntryFull (cfg : Cfg) (a : AskedE) (g : Fam (rom 256)) : Bool :=
  askedFit OnBytes.Tie.recordGround.q.link.table a &&
    verifyEntryG OnBytes.Tie.recordGround record_ok cfg a g

/-- The check at the small example. The limits: the comment on `verifyEntryFull`. -/
def verifyEntrySmall (cfg : Cfg) (a : AskedE) (g : Fam (rom 256)) : Bool :=
  askedFit OnBytes.Tie.smallRecordGround.q.link.table a &&
    verifyEntryG OnBytes.Tie.smallRecordGround small_record_ok cfg a g

/-- The form for a run, at the full size. The limits: the comment on `verifyEntryFull`. -/
def runEntryFull (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) : Bool :=
  askedFit OnBytes.Tie.recordGround.q.link.table a &&
    verifyEntryO OnBytes.Tie.recordGround record_ok cfg a O

/-- The form for a run, at the small example. The limits: the comment on `verifyEntryFull`. -/
def runEntrySmall (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) : Bool :=
  askedFit OnBytes.Tie.smallRecordGround.q.link.table a &&
    verifyEntryO OnBytes.Tie.smallRecordGround small_record_ok cfg a O

/-- The form for a run is the check, at the function made of O: on all arguments. -/
theorem runEntryFull_eq (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    runEntryFull cfg a O = verifyEntryFull cfg a (gOf O) :=
  congrArg (askedFit OnBytes.Tie.recordGround.q.link.table a && ·) (verifyEntryO_eq _ _ cfg a O)

/-- The form for a run is the check, at the function made of O: on all arguments. -/
theorem runEntrySmall_eq (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    runEntrySmall cfg a O = verifyEntrySmall cfg a (gOf O) :=
  congrArg (askedFit OnBytes.Tie.smallRecordGround.q.link.table a && ·)
    (verifyEntryO_eq _ _ cfg a O)

/-- The closed check says yes exactly if the tests on the parsed value and `verifyEntryG` do. -/
theorem verifyEntryFull_iff (cfg : Cfg) (a : AskedE) (g : Fam (rom 256)) :
    verifyEntryFull cfg a g = true ↔
      askedFit OnBytes.Tie.recordGround.q.link.table a = true ∧
        verifyEntryG OnBytes.Tie.recordGround record_ok cfg a g = true :=
  Bool.and_eq_true _ _ ▸ Iff.rfl

/-- The closed check says yes exactly if the tests on the parsed value and `verifyEntryG` do. -/
theorem verifyEntrySmall_iff (cfg : Cfg) (a : AskedE) (g : Fam (rom 256)) :
    verifyEntrySmall cfg a g = true ↔
      askedFit OnBytes.Tie.smallRecordGround.q.link.table a = true ∧
        verifyEntryG OnBytes.Tie.smallRecordGround small_record_ok cfg a g = true :=
  Bool.and_eq_true _ _ ▸ Iff.rfl

end TypedOracleCompiler.Slice
