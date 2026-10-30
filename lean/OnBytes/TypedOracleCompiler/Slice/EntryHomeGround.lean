-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryHomeGround.lean: the letters of the entry's part that a setting's one record
of typed facts fills: the description and the parameter bytes, as functions of the configuration's
digest.

`HomeData` (OnBytes/TypedOracleCompiler/Slice/EntryHome.lean) lists what is still a letter in the entry's part:
five. Two of them, with the test on the first, are written here of a ground G
(`Tie.EntryGround`, OnBytes/Tie/EntryGround.lean): the description `entryXD G c`
(OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean) and the bytes `G.bytesAt c`.

Main definition: `HomeData.ofGround`.
Main theorems: `entryXD_passes` (the second compiler's test, which asks a digest of 32 bytes, at
such a digest, if the ground's description is in order at an empty statement); `entryXD_depth`,
`entryXD_field`, `entryXD_blocks`: depth, field and blocks are read off the ground, and do not hang
on the digest.

What is not claimed. The decision and the page's code behind the escape stay letters. Nothing is
delivered. Nothing on soundness. No probability. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHome
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Slice.PartEntryFull

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice.Shapes (Size)
open OnBytes.Tie (EntryGround linkAtCfg)

variable (G : EntryGround)

/-- At a digest of 32 bytes the description's chain passes the second compiler's test, if the
ground's own description is in order at an empty statement. -/
theorem entryXD_passes (hb : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (c : ByteArray) (hc : c.size = 32) : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true :=
  okT_of_within (OnBytes.Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty)
    (fun _ _ => ByteArray.empty) (G.within_at c hc ByteArray.empty (by
      rw [OnBytes.Tie.baseOk_linkAtCfg G.q c G.rs ByteArray.empty (hc.trans G.cfg32.symm)
        G.spelled]
      exact hb))

/-- The stored tables' depth is read off the ground's rounds. -/
theorem entryXD_depth (c : ByteArray) :
    (entryXD G c).a = ((G.rs.map (·.2)).flatten.head?.map (·.sh.a)).getD 0 := rfl

/-- The field is the ground's plan's. -/
theorem entryXD_field (c : ByteArray) :
    (entryXD G c).base.plan.field = G.q.given.plan.field := rfl

/-- The blocks of a verifier's message are those of the ground's own description. -/
theorem entryXD_blocks (c : ByteArray) : (entryXD G c).K =
    _root_.Run.PQ.kOf (OnBytes.Tie.inFile (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base) :=
  TypedOracleCompiler.Run.PQ.kOf_congr _ _ rfl rfl rfl

/-- The entry's letters at a ground: the description, its test and the parameter bytes are
written; the decision and the page's code behind the escape are arguments. -/
def HomeData.ofGround (z : Size) (d₁ : Sd1 z.lg z.s)
    (hb : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (dec : ByteArray → XE (List T3) z.lg z.s → View → Bool)
    (back : ∀ c, StrCode (AllPts 256 ((entryXD G c).K + 1) (EntryFill.Ls (entryXD G c) d₁))) :
    HomeData z d₁ where
  DX := entryXD G
  ok := entryXD_passes G hb
  prm := G.bytesAt
  dec := dec
  back := back

end TypedOracleCompiler.Slice
