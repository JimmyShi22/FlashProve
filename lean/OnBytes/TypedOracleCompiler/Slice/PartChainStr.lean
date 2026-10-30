-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartChainStr.lean: the entry's part over the sibling with strings of bits as
leaves' bodies: all that OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean asks of bodies is met together. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler. "The
sibling": the files of OnBytes/TypedOracleCompiler/: the library's compiler said again, with a list of roots in a
query and a leaf's body of a type that the interface chooses.

`partChainAsk_ok` asks of the type of bodies: how stored symbols lie among them (`BodyD`), one code
of bodies for the page (`LeafD`), how the chain's own symbols lie among them, with a reading back
(`OwnE`), that the page's code writes every own symbol's body and none is read as a stored symbol
(`OwnFits`), and that each is spelled as the format spells its leaf (`hi`).
OnBytes/TypedOracleCompiler/StringsAt.lean, StringsOwn.lean, StringsList.lean, StringsMeet.lean and
StringsBounds.lean have each of these at `List Bool`: a body that the page's code of bodies writes
IS the string that the format hashes for the leaf, without the salt; a stored symbol that the format
cannot spell has a body behind an escape, which that code does not write (a leaf query on it the
page writes by its total code, behind the byte 2: OnBytes/TypedOracleCompiler/Slice/TieEscape.lean). Here they are
put together.

ALL NEW (7).
 `leafT D`, `leafT_is_leafS`, `ownFitsT`   `leafS D` under a name of its own: its serialiser of
                      bodies is `serTie` (OnBytes/TypedOracleCompiler/Run/SerTie.lean), so that behind the escape
                      the page writes stored leaves as the line's page does; `OwnFits` does not read
                      that field.
 `ownES D hok`        `OwnE` at strings: `StringsList.embT`, `prjT`, `prjT_embT`; no tree is deeper
                      than 63, by the sibling's `ok`.
 `hiS`                the spelling of own symbols: the second half of `okA_ownB_embTail`.
 `partChainStr`       `partChainAsk` at `bodyS`, `leafT`, `ownES`.
 `partChainStr_ok`    `Part.OK`, with no hypothesis on bodies.

WHAT IS NOT SAID. What the head of OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean does not say, but for the
bodies: soundness of the sibling's Link is a hypothesis; no description is shown to meet `FitsS`,
`ok`, `okX` here; one part of three. That
strings of bits are the bodies to be wished for: another type with the same data serves as well.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.PartChainAsk
import OnBytes.TypedOracleCompiler.Run.SerTie
import OnBytes.TypedOracleCompiler.StringsOwn

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run (IsCall169)
open TypedOracleCompiler.Run.PQ (XD xdOf inFile BodyD LeafD StmInv OwnE OwnFits FitsS leafSL okX bodyS leafS
  ownFitsS salt_of serTie)
open OnBytes.Slice (RootsIn s0Of)
open scoped ENNReal

/-! ## Strings of bits as bodies: all that the part asks of bodies, together -/

section
variable (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)

/-- The page's one code of bodies at strings of bits, with the serialiser that writes stored
symbols as the line's page does (`serTie`, OnBytes/TypedOracleCompiler/Run/SerTie.lean), which the page reads for
its total code behind the escape alone. It IS `leafS D` (`leafT_is_leafS`): `leafS` has that
serialiser itself; the name is kept for what is stated at it. -/
def leafT : LeafD D (bodyS D.a D.base.plan.salt) :=
  { leafS D with
    ser := serTie (bodyS D.a D.base.plan.salt) (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW))
      serBits }

/-- `leafT D` is `leafS D`. -/
theorem leafT_is_leafS : leafT D = leafS D := rfl

include hok in
/-- `OwnFits` does not read the serialiser: `ownFitsS` at `leafT`. -/
theorem ownFitsT : OwnFits (bodyS D.a D.base.plan.salt) D (leafT D)
    (StringsList.embT D.base.plan.salt D.C D.ds) :=
  ⟨(ownFitsS D hok).writes, (ownFitsS D hok).notStored⟩

/-- The chain's own symbols among strings of bits, with a reading back: a symbol's body is its
leaf's own string; it is read back by the code of its position's own tree. At a description whose
chain passes the sibling's `ok`. -/
def ownES : OwnE (List Bool) D where
  emb := StringsList.embT D.base.plan.salt D.C D.ds
  prj := StringsList.prjT D.base.plan.salt D.C D.ds
  prj_emb := StringsList.prjT_embT D.base.plan.salt D.C D.ds (smallL_of_ok D.base hok).shallow

/-- The body of every own symbol is spelled as the format spells its leaf. -/
theorem hiS (p : OPos (TypedOracleCompiler.Run.PQ.uL D.C D.ds)) (a : OSym (TypedOracleCompiler.Run.PQ.uL D.C D.ds)
            p) :
    (bodyS D.a D.base.plan.salt).own ((ownES D hok).emb (.inr p) a) =
      some (leafSL D.C D.base.plan.salt D.ds ⟨p, a⟩) :=
  (okA_ownB_embTail D.base.plan.salt D.C D.a D.base.plan.salt (salt_of D.base hok) D.ds
    (smallL_of_ok D.base hok) p a).2

end

/-! ## The part at strings of bits -/

section
variable {γ : Type} (S0 : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
  (dec : View → Bool) (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm))
  (hok : TypedOracleCompiler.Run.PQ.ok (xdOf S0 stm).base = true)
  (hwork : ∀ d ∈ (xdOf S0 stm).ds, d.entry.work ≤ 64)
  (hokx : okX (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs = true)
  (S : Finset (List Bool)) (T : List Bool → Dig 256) (Lg : LangT (List Bool) (xdOf S0 stm) dec)
  (εs : ℝ≥0∞) (pre : Pre γ)

/-- `partChainAsk` with strings of bits as leaves' bodies. -/
noncomputable def partChainStr : Part 256 γ SgX :=
  partChainAsk (bodyS (xdOf S0 stm).a (xdOf S0 stm).base.plan.salt) S0 stm (leafT (xdOf S0 stm)) dec
      hcfg V (ownES (xdOf S0 stm) hok) hwork hokx S T Lg εs pre

/-- That part meets what the step to one oracle asks of a part: NO HYPOTHESIS ON BODIES IS LEFT.
The definition takes: the configuration's digest has 32 bytes; a reader for the statement; the chain
passes the sibling's `ok`; no round asks more than 64 bits of work; the limits `okX`. Asked beside:
the string at which the checker asks for the digest of the parameter bytes lies in S; all strings of
S are strings of calls with the number 169; round-by-round soundness of the sibling's Link for the
language, with error e (`SoundLT`: a hypothesis); the statement holds the roots; the bounds `FitsS`.
`OwnFits` is `ownFitsT`; the spelling of own symbols is `hiS`. -/
theorem partChainStr_ok (h0S : s0Of S0.base.params ∈ S) (hS : ∀ s ∈ S, IsCall169 s)
    (hs : SoundLT (List Bool) (xdOf S0 stm) dec Lg εs) (hroots : RootsIn S0 stm)
    (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K) :
    (partChainStr S0 stm dec hcfg V hok hwork hokx S T Lg εs pre).OK :=
  partChainAsk_ok (bodyS (xdOf S0 stm).a (xdOf S0 stm).base.plan.salt) S0 stm (leafT (xdOf S0 stm))
      dec hcfg V (ownES (xdOf S0 stm) hok) hwork hokx S T Lg εs pre
    h0S hS hs hroots F (ownFitsT (xdOf S0 stm) hok) (hiS (xdOf S0 stm) hok)

end

end TypedOracleCompiler.Slice
