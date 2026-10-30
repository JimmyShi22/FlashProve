-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageX.lean: the encoding of the typed queries into the single oracle's strings as a function of
the description of a chain that opens stored tables (an entry file's chain); all data of
Run/CodingPageX.lean's record `PageCX`, at the interface `D.L dec` and the tag "link".

This file does for a description `D : XD` (Run/PlanQXRun.lean) what Run/PageQ.lean does for a plain
chain's description. The rounds behind the first query, the chain's own leaves and the serialisers
behind the escape are Run/PageQ.lean's and Run/PageQChain.lean's, taken at the tag "link": the
shapes and annotations are the same types. New are two things. (1) The stored leaves' code
(Run/CodingPage174.lean). (2) The first chain query: under two outer roots. The typed query holds
the two roots; the call holds the statement's bytes `D.stm r0 r1`, and `D.stm` is any function: a
code must read the roots back. So a reader for the statement is asked, as data with both laws
(`StmInv D`). Definitions that compute, with their laws.
No definition here takes the interface as an argument: the arguments are the description, the
decision, 256 bits, the reader; the interface stands in types. (Tried at one description: the test
of Run/M3EngineOne.lean [not in this library] ends; so here read: not tested in this library)

Main names:
  `tagsOK_all`: Run/PageQChain.lean's test on the words with a tree's number holds at all rounds'
    data.
  `chainDX`, `leafPX`, `symX`, `pbX`, `serAllX`: the chain's data; the own leaves' code; the
    serialisers. A symbol of a stored table is written behind the escape as a number in binary
    (`Ser.natG`) and a list of words. (A round's number and a nonce are written there in unary, as
    in Run/PageQ.lean and Run/SerThin.lean: see the Limits.)
  `StmInv D`; `stmX`, `unstmX` with both laws.
  `pdX D`: the format's digest of the parameter bytes, as a digest: a constant of the description.
  `selF`, `mkF` with both laws; `first0X`; `firstPX dec pd V`: the first chain query: written
    exactly if the query is of round 0, in the first format with two digests and no statement, has
    no root and the trivial round's plain part, the statement's bytes are fewer than 2^64, and the
    salt is empty or has 256 bits. The string is that of the call number 160 with pd in the place of
    the parameters' digest, the statement of the two roots, an empty record and the salt.
  `pageXPd dec pd K hcfg V`: the record of data, with any 256 bits pd in that place; `pageX`: at
    `pdX D`.

Limits: this file does not say that the strings are those of Run/PlanQXRun.lean's spellings
(`firstX`, `leafX`, `PDX`): not proved here (Run/PageXFit.lean). No `StmInv` is given at any
description here (Run/PageXStm.lean); where the statement is not one-to-one in the two roots there
is none, and nothing is built. Nothing ties pd to the parameter bytes but at `pageX`. That a string
written here lies in the format's domain (`Fmt.hDom`) is not asked and not claimed. A record's
answers are not rendered as an instance: the interface's instances have one value; answers can ride
in `D.stm` and in the decision alone, and nothing ties the two. A chain query whose nonce is not
below 2^64 is written behind the escape with the nonce in unary: a string of more than 2^64 bits,
for each block. What the evaluator builds is a fact about a compiler. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPageX
import Run.PlanQXRun
import Run.PageQ
import Run.Toy1TieTree

set_option autoImplicit false

namespace Run.PQ
open Rom Compile Compile.Batch Iop

/-! ## A test of Run/PageQChain.lean that holds at every description -/

/-- The word with a tree's number has the leaves' number in its low 16 bits, at all rounds' data. -/
theorem tagsOK_all (salt : ℕ) : ∀ ds : List RD, tagsOK salt ds = true
  | [] => rfl
  | d :: ds => by
      show (decide ((leafWord d.tree salt).take 16 = t164) && tagsOK salt ds) = true
      rw [tagsOK_all salt ds, Bool.and_true, decide_eq_true_iff]
      exact tag_low 164 _

variable (D : XD) (dec : View → Bool)

/-- A plain part of some round of the protocol under the tag "link". -/
abbrev PBX : Type :=
  PlainPart (Compile.Batch.shapeOf (D.L dec) .link) (Compile.Batch.annOf (D.L dec) .link)

/-! ## The chain behind the first query, and the chain's own leaves: Run/PageQ.lean's -/

/-- The chain's data: the description's label, kinds and work; the messages' codes are
Run/PageQ.lean's for plain chains. -/
def chainDX : ChainD (D.L dec) .link where
  label := D.base.label
  kind := fun i => if i = 0 then 7 else ((D.base.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((D.base.rounds[i - 1]?).map (·.entry.work)).getD 0
  rc := rcQ D.base D.C dec
  hrc := rcQ_ge D.base D.C dec

/-- The code of the chain's own leaves: Run/PageQ.lean's for plain chains. -/
def leafPX : PCode (SymAny (Compile.Batch.shapeOf (D.L dec) .link)) := leafQ D.base D.C dec

/-! ## The total code behind the escape -/

/-- Serialisers of a symbol with its position, for the three protocols of the interface. -/
def symX : ∀ t : Tag, Ser (SymAny (Compile.Batch.shapeOf (D.L dec) t))
  | .link => symQ D.base D.C dec .onl
  | .onl => serNo _
  | .test => serNo _

/-- Serialisers of a plain part of some round, for the three protocols of the interface. -/
def pbX : ∀ t : Tag, Ser (PlainPart (Compile.Batch.shapeOf (D.L dec) t) (Compile.Batch.annOf (D.L dec) t))
  | .link => pbQ D.base D.C dec .onl
  | .onl => Ser.empty
  | .test => Ser.empty

/-- The serialisers; a symbol of a stored table is a number, in binary, and a list of words. -/
def serAllX : SerP (fun _ : Unit => D.L dec) :=
  ⟨Ser.unit, Ser.prod Ser.natG (Ser.list serW), symX D dec, pbX D dec⟩

/-! ## The first query -/

/-- A reader for the statement: from the bytes `D.stm r0 r1` back to the two roots, as digests,
with both laws. -/
structure StmInv where
  /-- the reader -/
  un     : ByteArray → Option (Dig 256 × Dig 256)
  /-- it reads the roots out of their statement -/
  un_stm : ∀ a b, un (D.stm (digToBytes a) (digToBytes b)) = some (a, b)
  /-- it reads roots only out of their statement -/
  stm_un : ∀ s a b, un s = some (a, b) → D.stm (digToBytes a) (digToBytes b) = s

/-- The statement's bytes, of the two roots. -/
def stmX : Option (Dig 256 × Dig 256) → Option ByteArray
  | some r => some (D.stm (digToBytes r.1) (digToBytes r.2))
  | none => none

variable {D} in
/-- The two roots, of the statement's bytes. -/
def unstmX (V : StmInv D) (b : ByteArray) : Option (Option (Dig 256 × Dig 256)) :=
  (V.un b).map some

variable {D} in
/-- The reading undoes the spelling. -/
theorem unstm_stmX (V : StmInv D) (x : Option (Dig 256 × Dig 256)) (b : ByteArray)
    (h : stmX D x = some b) : unstmX V b = some x := by
  cases x with
  | none => cases h
  | some r =>
      rw [← Option.some.inj h]
      show (V.un _).map some = _
      rw [V.un_stm]
      rfl

variable {D} in
/-- The spelling undoes the reading. -/
theorem stm_unstmX (V : StmInv D) (b : ByteArray) (x : Option (Dig 256 × Dig 256))
    (h : unstmX V b = some x) : stmX D x = some b := by
  unfold unstmX at h
  cases hu : V.un b with
  | none => rw [hu] at h; cases h
  | some r =>
      rw [hu] at h
      rw [← Option.some.inj h]
      exact congrArg some (V.stm_un b r.1 r.2 hu)

/-- The parameters' digest, as a digest: a constant of the description. -/
def pdX : Dig 256 := bytesToDig (_root_.Fmt.paramsDigest D.base.params)

/-- As bytes it is the format's digest of the parameter bytes. -/
theorem bytes_pdX : digToBytes (pdX D) = _root_.Fmt.paramsDigest D.base.params :=
  TieTree.dig_bytes _ (_root_.Fmt.size_H 169 0 1 _root_.Fmt.zero32 D.base.params)

variable (pd : Dig 256)

/-- A chain query of round 0 in the first format, with a list of two digests, no statement, no root
and the trivial round's plain part, as (pd, the two roots, the salt). -/
def selF (q : FbIn 256 (D.L dec) .link) :
    Option (Dig 256 × Option (Dig 256 × Dig 256) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [cm, cm'] none salt, none =>
      if isP0Q D.base D.C dec q.plain = true then some (pd, some (cm, cm'), salt) else none
  | _, _, _ => none

/-- The way back: refused if the first digest is not pd, or there are no roots. -/
def mkF (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool) :
    Option (FbIn 256 (D.L dec) .link) :=
  match a.2.1 with
  | some r =>
      if a.1 = pd then some ⟨0, .f1 [r.1, r.2] none a.2.2, none, p0Q D.base D.C dec⟩ else none
  | none => none

/-- What `selF` reads: the query's fields. -/
theorem selF_some (q : FbIn 256 (D.L dec) .link)
    (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool) (h : selF D dec pd q = some a) :
    ∃ cm cm' salt, q = ⟨0, .f1 [cm, cm'] none salt, none, p0Q D.base D.C dec⟩ ∧
      a = (pd, some (cm, cm'), salt) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selF at h
  split at h
  · rename_i cm cm' salt e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 [cm, cm'] none salt := e2
    have e3' : rt = none := e3
    by_cases hq : isP0Q D.base D.C dec plain = true
    · have h' : (if isP0Q D.base D.C dec plain = true then some (pd, some (cm, cm'), salt)
          else none) = some a := h
      rw [if_pos hq] at h'
      refine ⟨cm, cm', salt, ?_, (Option.some.inj h').symm⟩
      rw [e1', e2', e3', (isP0Q_iff D.base D.C dec plain).1 hq]
    · have h' : (if isP0Q D.base D.C dec plain = true then some (pd, some (cm, cm'), salt)
          else none) = some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

/-- The way back undoes `selF`. -/
theorem mkF_selF (q : FbIn 256 (D.L dec) .link)
    (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool) (h : selF D dec pd q = some a) :
    mkF D dec pd a = some q := by
  obtain ⟨cm, cm', salt, rfl, rfl⟩ := selF_some D dec pd q a h
  exact if_pos rfl

/-- `selF` undoes the way back. -/
theorem selF_mkF (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool)
    (q : FbIn 256 (D.L dec) .link) (h : mkF D dec pd a = some q) : selF D dec pd q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some r =>
      have h0 : (if p = pd then
          some (⟨0, .f1 [r.1, r.2] none salt, none, p0Q D.base D.C dec⟩ : FbIn 256 (D.L dec) .link)
          else none) = some q := h
      by_cases hp : p = pd
      · rw [if_pos hp] at h0
        rw [← Option.some.inj h0, hp]
        show (if isP0Q D.base D.C dec (p0Q D.base D.C dec) = true then
          some (pd, some (r.1, r.2), salt) else none) = _
        rw [if_pos ((isP0Q_iff D.base D.C dec _).2 rfl)]
      · rw [if_neg hp] at h0
        cases h0

variable {D} in
/-- Run/CodingPage160.lean's code of a first call, on (digest, the two roots, salt). -/
def first0X (V : StmInv D) : PCode (Dig 256 × Option (Dig 256 × Dig 256) × List Bool) :=
  pFirst0 D.base.label (stmX D) (unstmX V) (unstm_stmX V) (stm_unstmX V)

variable {D} in
/-- The first chain query. Written exactly if the query is of round 0, in the first format with
two digests and no statement, has no root and the trivial round's plain part, the statement's bytes
are fewer than 2^64, and the salt is empty or has 256 bits. The string is that of the call number
160 with pd in the place of the parameters' digest, the statement of the two roots, an empty record
and the salt. -/
def firstPX (V : StmInv D) : PCode (FbIn 256 (D.L dec) .link) :=
  (first0X V).pull (selF D dec pd) (mkF D dec pd) (mkF_selF D dec pd) (selF_mkF D dec pd)

variable {D} in
/-- Every string of the first query's code begins with the header of the call number 160. -/
theorem firstPX_hdr (V : StmInv D) (q : FbIn 256 (D.L dec) .link) (s : List Bool)
    (h : (firstPX dec pd V).put q = some s) : ∃ r, s = hdr160 D.base.label ++ r := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact pFirst0_hdr _ _ _ _ _ a s ha

/-! ## The data -/

variable {D} in
/-- All data of the encoding, from the description, 256 bits pd for the place of the parameters'
digest, a reader for the statement, and the fact that the configuration's digest has 32 bytes. Where
the statement is not one-to-one in the two roots there is no `StmInv`, and nothing is built. -/
def pageXPd (K : ℕ) (hcfg : D.base.cfg.size = 32) (V : StmInv D) : PageCX (D.L dec) K .link where
  cfg := D.base.cfg
  hcfg := hcfg
  chain := chainDX D dec
  chainTag := tag_low 162 D.base.label
  first := firstPX dec pd V
  firstTag := fun q s hq => by
    obtain ⟨r, rfl⟩ := firstPX_hdr dec pd V q s hq
    exact tag16_hdr 0 160 0 D.base.label _root_.Fmt.zero32 rfl r
  firstHd := fun q s hq e he => by
    obtain ⟨r, rfl⟩ := firstPX_hdr dec pd V q s hq
    exact hdr_not_prefix e 0 he 160 0 D.base.label _root_.Fmt.zero32 r
  saltBits := 8 * D.base.plan.salt
  leafP := leafPX D dec
  leafTag := leafQ_tag D.base D.C dec (tagsOK_all _ _)
  back := backP (fun _ : Unit => D.L dec) (serAllX D dec) K
  storedP := pStored D.a D.base.plan.salt
  storedTag := pStored_tag D.a D.base.plan.salt

variable {D} in
/-- `pageXPd` at the format's own digest of the parameter bytes, `pdX D`. -/
abbrev pageX (K : ℕ) (hcfg : D.base.cfg.size = 32) (V : StmInv D) : PageCX (D.L dec) K .link :=
  pageXPd dec (pdX D) K hcfg V

end Run.PQ
