-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRow13.lean: SOUNDNESS RECORD BY RECORD OF THE ENTRY'S WRITTEN LINK AT THE
DECISION OF THE LEAN PORT'S LINK (linkVerify … .decides (Entry.start …)), AT KEYS THAT ARE A LETTER
OR ARE WRITTEN OF THE INSTANCE, in the form in which the entry's list of debts asks it
(EntryDebts.sound, OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean), FROM TWO HYPOTHESES THAT ARE NOT PROVED
HERE, at the small and at the full-size files of the setting "record with work". The list of counts
has one type in two written forms: row13_of and row13_at, whose parameters are letters, type it as
EntryDebts.sound does, `Err (Link0 D fun _ => true).shape`; the four theorems at the files type it
at `link0Shape D` (OnBytes/TypedOracleCompiler/Slice/LinkShape.lean, which says why): the same type by unfolding.

What is put together. (1) The carrier entry_hS (OnBytes/TypedOracleCompiler/Slice/EntryFromLink.lean): soundness of
the library's written link at each instance's pair of records, with one list of error counts, passes
to the sibling's written link of a description D. (2) hL, A HYPOTHESIS: at every pair of keys that
hold a pair of records r (KeyHasR, OnBytes/Slice/BlkRecRow.lean), the first with the item 0 and the
second with the item 1, and at every decision whose yes gives the yes of the port's link at these
keys, the library's written link is round-by-round sound for Sz.LangE2T at r, with the list of
counts of sr_link_joh | fr_link_joh (OnBytes/Slice/SmallRecLink.lean, FullRecLink.lean). (3) hB, A
HYPOTHESIS: each count is at most 2^-128 of its own round's written verifier messages; where a round
has work its test bits are among the message's bits, so part of the 128 bits is work
(OnBytes/Slice/FullRecNum.lean says where). (4) For each instance x a pair of keys that hold x's
pair of records: in row13_of, sr_row13, fr_row13 a letter with its hypothesis (hK); in row13_at,
sr_row13_z, fr_row13_z the keys that are WRITTEN of x's two records (keysOfX,
OnBytes/TypedOracleCompiler/Slice/KeysOfX.lean: keyOf with the items 0 and 1), which hold them (keyHasR_keyOf).

The description D is ANY description with four data: its plan's field is the second; its rounds'
data are the library's, read as the sibling's; its stored tables have the positions of the tables'
code; its openings of stored tables are the library's.

The decision is (linkVerify q.link k0 k1).decides (Entry.start q), q the typed parameters of the
link's chain. It does not read the digest of the public files (dec_linkAtCfg), as a function of the
two keys; the keys that the port makes do hang on that digest, through the seeds' name. So the
statements hold with linkAtCfg q c for q, at every c.

Main theorems.
 row13_of        the general form, over letters; the keys are a letter.
 row13_at        the same at keysOfX, with the language's five sizes as letters that equal S's.
 dec_linkAtCfg   the decision at linkAtCfg p c is the decision at p.
 sr_size, fr_size   the sizes of zSmall | zFull (OnBytes/TypedOracleCompiler/Slice/ShapesAtSmall.lean,
                 ShapesAtFull.lean) are those of srS | frS, with 19 | 29 coordinates and one answer.
 sr_row13, fr_row13       at the small and at the full-size files.
 sr_row13_z, fr_row13_z   at keysOfX, with the language at the sizes of zSmall | zFull.

Not claimed. NO SOUNDNESS IS PROVED: hL is a hypothesis, and it holds the theorem on codes
(Cb.BCHKS46At) and the tie to the decision inside it. hB is a hypothesis: no count is evaluated.
That any description meets the four data (of asTypedCompilerDescription srD | asTypedCompilerDescription frD: OnBytes/TypedOracleCompiler/Slice/
SmallRecDesc.lean, FullRecDesc.lean). That keys with hK, or the keys keysOfX, are those that a
program makes. That the decision says yes on any view. The language (lgEX) has three ways out: see
the head of OnBytes/Slice/LinkChainJoh.lean. Nothing on where a seed comes from, on a compiler, a
wiring, a page, bytes or a file. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFromLink
import OnBytes.TypedOracleCompiler.Slice.LinkShape
import OnBytes.TypedOracleCompiler.Slice.KeysOfX
import OnBytes.TypedOracleCompiler.Slice.ShapesAtSmall
import OnBytes.TypedOracleCompiler.Slice.ShapesAtFull
import OnBytes.Slice.BlkRecRow
import OnBytes.Slice.SmallRecLink
import OnBytes.Slice.FullRecLink
import OnBytes.Tie.EntryAtCfg

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open OnBytes OnBytes.Slice TypedOracleCompiler.Run
open OnBytes.Slice.Shapes (zSmall zFull)
open OnBytes.Tie (linkAtCfg)
open OnBytes.Params (smallRecordRead recordRead)
open _root_.Iop (Err)
open _root_.Run.PQ (View)
open scoped ENNReal

/-- The decision of an entry's check at two keys does not read the digest of the public files. -/
theorem dec_linkAtCfg (p : Params.Link) (c : ByteArray) (k0 k1 : TableKey) :
    (linkVerify (linkAtCfg p c).link k0 k1).decides (Entry.start (linkAtCfg p c)) =
      (linkVerify p.link k0 k1).decides (Entry.start p) := rfl

/-- The general form. hL: at keys that hold a pair of records, with the items 0 and 1, and at a
decision whose yes gives the yes of the port's link at these keys, the library's written link is
sound at that pair, with the counts ε. hb: the counts are below e. hK: the keys of each instance
hold its pair of records. Then at a description with the four data the sibling's written link at
the port's own decision is sound at each instance, with one list of counts below e. -/
theorem row13_of {An : Type} (S : Sz) (lg s : ℕ)
    (an : An → (decRec S.P.T S.P.v S.eM lg s).ix.Row × (decRec S.P.T S.P.v S.eM lg s).Z.S → GE)
    (d1 d2 d3 d4 d5 : _root_.Run.PQ.RD) (tl : List _root_.Run.PQ.RD)
    (xs : List _root_.Run.PQ.XO) (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (d1 :: d2 :: d3 :: d4 :: d5 :: tl).map PQ.ofLib) (ha : D.a = S.P.T.a)
    (hxs : D.xs = xs) (Λ : Params.LinkShape) (s0 : Start)
    (ε : Err (written S d1 d2 d3 d4 d5 tl xs fun _ => true).shape) (e : ℝ≥0∞)
    (hb : Err.Below ε e)
    (hL : ∀ (first further : TableKey) (r : (S.lkR (recZ S.P.T.l lg s)).X0), first.item = 0 →
      further.item = 1 → KeyHasR S.P.v lg s (Λ.side false 1).index first r.1 →
      KeyHasR S.P.v lg s (Λ.side true 1).index further r.2 → ∀ dec : View → Bool,
      (∀ V, dec V = true → (linkVerify Λ first further).decides s0 V = true) →
      (written S d1 d2 d3 d4 d5 tl xs dec).Sound
        (fun _ y => S.LangE2T (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) r y) ε)
    (key : XE An lg s → TableKey × TableKey)
    (hK : ∀ x, (key x).1.item = 0 ∧ (key x).2.item = 1 ∧
      KeyHasR S.P.v lg s (Λ.side false 1).index (key x).1 (recOf S lg s an x).1 ∧
      KeyHasR S.P.v lg s (Λ.side true 1).index (key x).2 (recOf S lg s an x).2) :
    ∃ ε' : Err (Link0 D fun _ => true).shape,
      (∀ x, (Link0 D ((linkVerify Λ (key x).1 (key x).2).decides s0)).Sound
        (fun _ => lgEX S.P.T S.P.v S.eM lg s D an x) ε') ∧ Err.Below ε' e :=
  entry_hS S lg s an d1 d2 d3 d4 d5 tl xs D hf hds ha hxs
    (fun x => (linkVerify Λ (key x).1 (key x).2).decides s0) ε e hb fun x =>
      hL (key x).1 (key x).2 (recOf S lg s an x) (hK x).1 (hK x).2.1 (hK x).2.2.1 (hK x).2.2.2 _
        fun _ h => h

/-- The general form at the written keys, with the five sizes of the language as letters T, v,
eM, lg, s that equal those of S, lg₀, s₀. Asked beside what row13_of asks: the tables' shape in the
link's shape has these numbers of row variables, answers and coordinates. -/
theorem row13_at {An : Type} (S : Sz) (lg₀ s₀ : ℕ) (d1 d2 d3 d4 d5 : _root_.Run.PQ.RD)
    (tl : List _root_.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) (D : PQ.XD)
    (hf : D.base.plan.field = .two)
    (hds : D.ds = (d1 :: d2 :: d3 :: d4 :: d5 :: tl).map PQ.ofLib) (ha : D.a = S.P.T.a)
    (hxs : D.xs = xs) (Λ : Params.LinkShape) (s0 : Start)
    (ε : Err (written S d1 d2 d3 d4 d5 tl xs fun _ => true).shape) (e : ℝ≥0∞)
    (hb : Err.Below ε e)
    (hL : ∀ (first further : TableKey) (r : (S.lkR (recZ S.P.T.l lg₀ s₀)).X0), first.item = 0 →
      further.item = 1 → KeyHasR S.P.v lg₀ s₀ (Λ.side false 1).index first r.1 →
      KeyHasR S.P.v lg₀ s₀ (Λ.side true 1).index further r.2 → ∀ dec : View → Bool,
      (∀ V, dec V = true → (linkVerify Λ first further).decides s0 V = true) →
      (written S d1 d2 d3 d4 d5 tl xs dec).Sound
        (fun _ y => S.LangE2T (recZ S.P.T.l lg₀ s₀) (S.P.T.l - 3 * s₀) r y) ε)
    (hΛv : Λ.table.v = S.P.v) (hΛs : Λ.table.answers = s₀) (hΛc : Λ.table.cubeBits = lg₀)
    (T : _root_.Fmt.M1.Code) (v eM lg s : ℕ) (hT : T = S.P.T) (hv : v = S.P.v) (he : eM = S.eM)
    (hlg : lg = lg₀) (hs : s = s₀)
    (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) :
    ∃ ε' : Err (Link0 D fun _ => true).shape,
      (∀ x, (Link0 D ((linkVerify Λ (keysOfX v lg s an x).1 (keysOfX v lg s an x).2).decides
          s0)).Sound (fun _ => lgEX T v eM lg s D an x) ε') ∧ Err.Below ε' e := by
  subst hT hv he hlg hs
  exact row13_of S lg s an d1 d2 d3 d4 d5 tl xs D hf hds ha hxs Λ s0 ε e hb hL
    (keysOfX S.P.v lg s an) fun x =>
      ⟨rfl, rfl, keyHasR_keyOf (recOf S lg s an x).1 _ hΛv hΛs hΛc 0,
        keyHasR_keyOf (recOf S lg s an x).2 _ hΛv hΛs hΛc 1⟩

/-! ## The small files -/

/-- The sizes of zSmall are those of srS, with 19 coordinates of a seed's point and one answer. -/
theorem sr_size : zSmall.T = srS.P.T ∧ zSmall.v = srS.P.v ∧ zSmall.eM = srS.eM ∧ zSmall.lg = 19 ∧
    zSmall.s = 1 := ⟨rfl, rfl, rfl, Shapes.zSmall_lg, rfl⟩

/-- At the small files, from hL and hB, which are not proved here. The head tells what
they say. D: any description with the four data. key: for each instance a pair of keys that hold its
pair of records. -/
theorem sr_row13 {An : Type}
    (an : An → (decRec srS.P.T srS.P.v srS.eM 19 1).ix.Row ×
      (decRec srS.P.T srS.P.v srS.eM 19 1).Z.S → GE)
    (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds).map
      PQ.ofLib)
    (ha : D.a = srS.P.T.a) (hxs : D.xs = srD.xs)
    (hL : ∀ (first further : TableKey) (r : (srS.lkR srZ).X0), first.item = 0 →
      further.item = 1 → KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1 →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2 →
      ∀ dec : View → Bool,
      (∀ V, dec V = true →
        (linkVerify smallRecordRead.link first further).decides (Entry.start smallRecordRead) V =
          true) →
      (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
          dec).Sound (fun _ y => srS.LangE2T srZ 524285 r y)
        (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
          (srS.badJ srS.e1)
          (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1)
            srS.eU)
          (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)))
    (hB : Err.Below (s := (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4)
        (srRd 5 :: srC.rds) srD.xs fun _ => true).shape)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1)
          srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL))
      (((2 : ℝ≥0∞)⁻¹) ^ 128))
    (key : XE An 19 1 → TableKey × TableKey)
    (hK : ∀ x, (key x).1.item = 0 ∧ (key x).2.item = 1 ∧
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index (key x).1
        (recOf srS 19 1 an x).1 ∧
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index (key x).2
        (recOf srS 19 1 an x).2) :
    ∃ ε : Err (link0Shape D),
      (∀ x, (Link0 D ((linkVerify smallRecordRead.link (key x).1 (key x).2).decides
          (Entry.start smallRecordRead))).Sound
        (fun _ => lgEX srS.P.T srS.P.v srS.eM 19 1 D an x) ε) ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  row13_of srS 19 1 an (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs D hf
    hds ha hxs smallRecordRead.link (Entry.start smallRecordRead) _ _ hB hL key hK

/-- At the small files, at the written keys and in the sizes of zSmall, from hL and hB,
which are not proved here. -/
theorem sr_row13_z {An : Type}
    (an : An → (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s).ix.Row ×
      (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s).Z.S → GE)
    (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds).map
      PQ.ofLib)
    (ha : D.a = srS.P.T.a) (hxs : D.xs = srD.xs)
    (hL : ∀ (first further : TableKey) (r : (srS.lkR srZ).X0), first.item = 0 →
      further.item = 1 → KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1 →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2 →
      ∀ dec : View → Bool,
      (∀ V, dec V = true →
        (linkVerify smallRecordRead.link first further).decides (Entry.start smallRecordRead) V =
          true) →
      (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
          dec).Sound (fun _ y => srS.LangE2T srZ 524285 r y)
        (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
          (srS.badJ srS.e1)
          (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1)
            srS.eU)
          (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)))
    (hB : Err.Below (s := (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4)
        (srRd 5 :: srC.rds) srD.xs fun _ => true).shape)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1)
          srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL))
      (((2 : ℝ≥0∞)⁻¹) ^ 128)) :
    ∃ ε : Err (link0Shape D),
      (∀ x, (Link0 D ((linkVerify smallRecordRead.link (keysOfX zSmall.v zSmall.lg zSmall.s an x).1
          (keysOfX zSmall.v zSmall.lg zSmall.s an x).2).decides
            (Entry.start smallRecordRead))).Sound
        (fun _ => lgEX zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s D an x) ε) ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  row13_at srS 19 1 (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs D hf
    hds ha hxs smallRecordRead.link (Entry.start smallRecordRead) _ _ hB hL rfl rfl Shapes.zSmall_lg
    zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s sr_size.1 sr_size.2.1 sr_size.2.2.1
    sr_size.2.2.2.1 sr_size.2.2.2.2 an

/-! ## The full-size files -/

/-- The sizes of zFull are those of frS, with 29 coordinates of a seed's point and one answer. -/
theorem fr_size : zFull.T = frS.P.T ∧ zFull.v = frS.P.v ∧ zFull.eM = frS.eM ∧ zFull.lg = 29 ∧
    zFull.s = 1 := ⟨rfl, rfl, rfl, Shapes.zFull_lg, rfl⟩

/-- At the full-size files, from hL and hB, which are not proved here. The head tells
what they say. D: any description with the four data. key: for each instance a pair of keys that
hold its pair of records. -/
theorem fr_row13 {An : Type}
    (an : An → (decRec frS.P.T frS.P.v frS.eM 29 1).ix.Row ×
      (decRec frS.P.T frS.P.v frS.eM 29 1).Z.S → GE)
    (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map
      PQ.ofLib)
    (ha : D.a = frS.P.T.a) (hxs : D.xs = frD.xs)
    (hL : ∀ (first further : TableKey) (r : (frS.lkR frZ).X0), first.item = 0 →
      further.item = 1 → KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1 →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2 →
      ∀ dec : View → Bool,
      (∀ V, dec V = true →
        (linkVerify recordRead.link first further).decides (Entry.start recordRead) V =
          true) →
      (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
          dec).Sound (fun _ y => frS.LangE2T frZ 402653181 r y)
        (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
          (frS.badJ frS.e1)
          (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1)
            frS.eU)
          (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)))
    (hB : Err.Below (s := (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4)
        (frRd 5 :: frC.rds) frD.xs fun _ => true).shape)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1)
          frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL))
      (((2 : ℝ≥0∞)⁻¹) ^ 128))
    (key : XE An 29 1 → TableKey × TableKey)
    (hK : ∀ x, (key x).1.item = 0 ∧ (key x).2.item = 1 ∧
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index (key x).1
        (recOf frS 29 1 an x).1 ∧
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index (key x).2
        (recOf frS 29 1 an x).2) :
    ∃ ε : Err (link0Shape D),
      (∀ x, (Link0 D ((linkVerify recordRead.link (key x).1 (key x).2).decides
          (Entry.start recordRead))).Sound
        (fun _ => lgEX frS.P.T frS.P.v frS.eM 29 1 D an x) ε) ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  row13_of frS 29 1 an (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs D hf
    hds ha hxs recordRead.link (Entry.start recordRead) _ _ hB hL key hK

/-- At the full-size files, at the written keys and in the sizes of zFull, from hL and
hB, which are not proved here. -/
theorem fr_row13_z {An : Type}
    (an : An → (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s).ix.Row ×
      (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s).Z.S → GE)
    (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map
      PQ.ofLib)
    (ha : D.a = frS.P.T.a) (hxs : D.xs = frD.xs)
    (hL : ∀ (first further : TableKey) (r : (frS.lkR frZ).X0), first.item = 0 →
      further.item = 1 → KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1 →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2 →
      ∀ dec : View → Bool,
      (∀ V, dec V = true →
        (linkVerify recordRead.link first further).decides (Entry.start recordRead) V =
          true) →
      (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
          dec).Sound (fun _ y => frS.LangE2T frZ 402653181 r y)
        (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
          (frS.badJ frS.e1)
          (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1)
            frS.eU)
          (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)))
    (hB : Err.Below (s := (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4)
        (frRd 5 :: frC.rds) frD.xs fun _ => true).shape)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1)
          frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL))
      (((2 : ℝ≥0∞)⁻¹) ^ 128)) :
    ∃ ε : Err (link0Shape D),
      (∀ x, (Link0 D ((linkVerify recordRead.link (keysOfX zFull.v zFull.lg zFull.s an x).1
          (keysOfX zFull.v zFull.lg zFull.s an x).2).decides
            (Entry.start recordRead))).Sound
        (fun _ => lgEX zFull.T zFull.v zFull.eM zFull.lg zFull.s D an x) ε) ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  row13_at frS 29 1 (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs D hf
    hds ha hxs recordRead.link (Entry.start recordRead) _ _ hB hL rfl rfl Shapes.zFull_lg
    zFull.T zFull.v zFull.eM zFull.lg zFull.s fr_size.1 fr_size.2.1 fr_size.2.2.1 fr_size.2.2.2.1
    fr_size.2.2.2.2 an

end TypedOracleCompiler.Slice
