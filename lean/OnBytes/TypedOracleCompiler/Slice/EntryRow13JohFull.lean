-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRow13JohFull.lean: under the statement on codes (Cb.BCHKS46At: a hypothesis
of these theorems, proved in none of these files; Cb.Gl.bchks46At, Cb/Bridge/GlCodesProved.lean,
proves it from the files under lean/ThirdParty/, adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15)): soundness record by record of the entry's
written link at the decision of the Lean
port's link (linkVerify … .decides (Entry.start …)), at keys that are written of the instance, with
one list of counts, each at most 2^-128 of its own round's written verifier messages, work counted,
in the form in which the entry's list of debts asks it (EntryDebts.sound,
OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean), with the list typed at `link0Shape D`
(OnBytes/TypedOracleCompiler/Slice/LinkShape.lean), the same type by unfolding, at the full-size files of the
setting "record with work".

OnBytes/TypedOracleCompiler/Slice/EntryRow13.lean states this from two hypotheses, hL and hB. Here they are met: hL
by fr_link_sound (OnBytes/Slice/FullRecYes.lean), which asks Cb.BCHKS46At; hB by fr_err_below
(OnBytes/Slice/FullRecNum.lean).

What is left as a hypothesis: Cb.BCHKS46At; of the description D its four data (its plan's field is
the second; its rounds' data are the library's, read as the sibling's; its stored tables have the
positions of the tables' code; its openings of stored tables are the library's); in fr_row13_key
besides that the keys of each instance hold its pair of records, with the items 0 and 1.

Main theorems.
 fr_row13_key   the keys are a letter with its hypothesis.
 fr_row13_joh   at the written keys keysOfX, in the sizes of zFull.

Not claimed. This is no proof of soundness of an entry file's check. The written link is an
interactive protocol; nothing here is on hashes, on bytes, on a compiler, a wiring or a page, or on
the reader that makes a view and the keys of a file. That the keys keysOfX are those that a program
makes. That any description meets the four data (of asTypedCompilerDescription frD: OnBytes/TypedOracleCompiler/Slice/FullRecDesc.lean).
Each count is at most 2^-128 of its own round's written verifier messages; where a round has work
its test bits are among the message's bits, so part of the 128 bits is work
(OnBytes/Slice/FullRecNum.lean says where): one round's share, no bound on the chance of a false
proof. That the decision says yes on any view. The language (lgEX) has three ways out: the first
table does not decode with its record, and at each table a collision at its record's seed; where one
is open the theorem says nothing. How often a collision occurs, and where a seed comes from, is not
said. All that the heads of the files named above do not claim. The compiler under OnBytes/TypedOracleCompiler/ is
the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRow13
import OnBytes.Slice.FullRecYes
import OnBytes.Slice.FullRecNum

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open OnBytes OnBytes.Slice TypedOracleCompiler.Run
open OnBytes.Slice.Shapes (zFull)
open OnBytes.Params (recordRead)
open _root_.Iop (Err)
open scoped ENNReal

/-- At the full-size files, under Cb.BCHKS46At; the keys are a letter. D: any description
with the four data. key: for each instance a pair of keys that hold its pair of records. -/
theorem fr_row13_key (hA : Cb.BCHKS46At GF GE) {An : Type}
    (an : An → (decRec frS.P.T frS.P.v frS.eM 29 1).ix.Row ×
      (decRec frS.P.T frS.P.v frS.eM 29 1).Z.S → GE)
    (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map
      PQ.ofLib)
    (ha : D.a = frS.P.T.a) (hxs : D.xs = frD.xs)
    (key : XE An 29 1 → OnBytes.TableKey × OnBytes.TableKey)
    (hK : ∀ x, (key x).1.item = 0 ∧ (key x).2.item = 1 ∧
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index (key x).1
        (recOf frS 29 1 an x).1 ∧
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index (key x).2
        (recOf frS 29 1 an x).2) :
    ∃ ε : Err (link0Shape D),
      (∀ x, (Link0 D ((linkVerify recordRead.link (key x).1 (key x).2).decides
          (OnBytes.Entry.start recordRead))).Sound
        (fun _ => lgEX frS.P.T frS.P.v frS.eM 29 1 D an x) ε) ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  fr_row13 an D hf hds ha hxs
    (fun first further r h0 h1 k0 k1 dec hdec =>
      fr_link_sound first further h0 h1 frD.xs dec hdec r (fun _ _ => k0) (fun _ _ => k1) hA)
    (fr_err_below frD.xs fun _ => true) key hK

/-- At the full-size files, under Cb.BCHKS46At, at the written keys and in the sizes of
zFull. D: any description with the four data. -/
theorem fr_row13_joh (hA : Cb.BCHKS46At GF GE) {An : Type}
    (an : An → (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s).ix.Row ×
      (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s).Z.S → GE)
    (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map
      PQ.ofLib)
    (ha : D.a = frS.P.T.a) (hxs : D.xs = frD.xs) :
    ∃ ε : Err (link0Shape D),
      (∀ x, (Link0 D ((linkVerify recordRead.link (keysOfX zFull.v zFull.lg zFull.s an x).1
          (keysOfX zFull.v zFull.lg zFull.s an x).2).decides
            (OnBytes.Entry.start recordRead))).Sound
        (fun _ => lgEX zFull.T zFull.v zFull.eM zFull.lg zFull.s D an x) ε) ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  fr_row13_z an D hf hds ha hxs
    (fun first further r h0 h1 k0 k1 dec hdec =>
      fr_link_sound first further h0 h1 frD.xs dec hdec r (fun _ _ => k0) (fun _ _ => k1) hA)
    (fr_err_below frD.xs fun _ => true)

end TypedOracleCompiler.Slice
