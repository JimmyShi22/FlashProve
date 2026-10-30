-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryX.lean: the entry's frame with instances: the written link of a description,
on two stored tables, as a protocol with an instance; an interface and a wire of the sibling that
hold it beside a second protocol; and it as a written batch protocol on two external strings.

WHY. With a record, what the entry's verifier decides hangs on both tables' records (answers and
seeds). The sibling's written link (`skeletonOverBothExternalStrings`, OnBytes/TypedOracleCompiler/Run/PlanQX.lean) has no instance: its
decision is a parameter. Here the decision is a function of an instance x, as
OnBytes/TypedOracleCompiler/Slice/Plain3X.lean has it for the key. The interface's Batch is on ONE external string,
so the link cannot be the interface's Batch: it is written under the tag of Link, whose protocol in
the interface has the same shape, and OnBytes/TypedOracleCompiler/Slice/WrittenE.lean takes it on two strings.

EVERYTHING IS A FUNCTION OF THE DESCRIPTION D: no size is written into a definition.

Main definitions.
 `Link0 D d`            the written link at a decision d, without an instance.
 `LinkX D dec`          THE WRITTEN LINK WITH AN INSTANCE: shape and what is read are `Link0`'s; at
                        x it accepts as `Link0 D (dec x)` does.
 `wq0`, `wqLX`          their wirings; the second has the fields of the first.
 `LXE`, `WXE`           the interface (Link: `Link0` at the decision "yes"; Test: a given protocol
                        T; Batch: no round; a first query holds `early x`) and a wire at it. With
                        `pX1`.
 `ZXE`                  `LinkX` as a `WrittenE` at `ext2R`, under the tag of Link.
 `testXE`               the interface's Test as a written protocol.
Main theorems.
 `linkX_local`, `linkX_sound_iff`   the verifier is local; soundness is soundness instance by
                        instance, with one list of counts.
 `wq0_okg`              the wiring of `Link0` is lawful, under the sibling's two conditions on a
                        description.
 `wqLX_okg`, `ZXE_ok`   the wiring is lawful, and `WrittenE.OK` holds, if the wiring of `Link0` is
                        lawful.

Not claimed. NO SOUNDNESS IS PROVED. No description, no decision, no bodies, no second protocol is
given: D, dec, the type of bodies with its two ways of writing, T and its wiring are letters. That
the typed first query, which holds `early x`, is spelled as any call of the format: no page is
written; the format's statement would have to hold both tables' answers. THE SIBLING'S PAGES, RUNS
AND PARTS OF AN ENTRY (OnBytes/TypedOracleCompiler/Run/PageXAsked.lean to AllRoots.lean,
OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean, PartEntryFull.lean) STAND AT `XD.L`, AN INTERFACE WITHOUT
INSTANCES AND WITHOUT A TEST: NONE OF THEM SPEAKS OF `LXE`. `XD.stm` takes two roots; nothing here
reads it. Nothing is asked of the whole wire (`QueryLayout.OKG`). Nothing speaks of a file or of the
program. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it
builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.JudgeE
import OnBytes.TypedOracleCompiler.Run.WireX

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE skeletonOverBothExternalStrings wX psofX_up wireTo wireTo_okg wireTo_ext psofX_local)
open _root_.Run.PQ (View SgX weX)
open scoped ENNReal

variable {X : Type} (D : XD) (dec : X → View → Bool)

/-! ## The protocol -/

/-- The written link of a description, at a decision, as a protocol without an instance on two
external strings. -/
abbrev Link0 (d : View → Bool) : InteractiveOracleProof Unit (twoExternalStrings (2 ^ D.a) SgX) :=
  (skeletonOverBothExternalStrings D.C D.ds D.a D.xs d).up.loc

/-- The written link with an instance: shape and what is read are `Link0`'s, which do not look
at the decision; at the instance x it accepts as `Link0 D (dec x)` does. -/
@[reducible] def LinkX : InteractiveOracleProof X (twoExternalStrings (2 ^ D.a) SgX) where
  shape := (Link0 D fun _ => true).shape
  blinded := (Link0 D fun _ => true).blinded
  extReads := fun _ ρ => (Link0 D fun _ => true).extReads () ρ
  reads := fun _ ρ π => (Link0 D fun _ => true).reads () ρ π
  accept := fun x y τ => (Link0 D (dec x)).accept () y τ

/-- The verifier is local, for every decision. -/
theorem linkX_local : (LinkX D dec).IsLocal :=
  fun x y y' τ τ' hρ hp he hr => psofX_local D.C D.ds D.a D.xs (dec x) () y y' τ τ' hρ hp he hr

/-- Soundness is soundness instance by instance, with one list of counts. -/
theorem linkX_sound_iff (Lg : X → (twoExternalStrings (2 ^ D.a) SgX).Str → Prop)
    (ε : Err (Link0 D fun _ => true).shape) :
    (LinkX D dec).Sound Lg ε ↔ ∀ x, (Link0 D (dec x)).Sound (fun _ => Lg x) ε :=
  ⟨fun h x _ y hn => h x y hn, fun h x y hn => h x () y hn⟩

/-! ## The wiring -/

/-- The wiring of `Link0`, all rounds local. -/
def wq0 (d : View → Bool) : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto (Link0 D d)) :=
  wireTo (psofX_up D.C D.ds D.a D.xs d) (wX D d)

/-- It is lawful, under the sibling's two conditions on a description: no round asks more than
64 bits of work; the limits `okX` on the stored tables' openings. (The term stands in the proof of
the sibling's `okgAny`, OnBytes/TypedOracleCompiler/Run/WireX.lean.) -/
theorem wq0_okg (d : View → Bool) (hwork : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true) : (wq0 D d).OKG :=
  wireTo_okg _ _ (TypedOracleCompiler.Run.PQ.wqX_okg D.C D.K (_root_.Run.chalP D.base.plan.field D.K) D.ds
    D.a D.xs d d (TypedOracleCompiler.Run.PQ.okX_own D.ds D.a D.xs hokx)
    (TypedOracleCompiler.Run.planPull_okg D.base.plan.field D.K D.ds d
      (TypedOracleCompiler.Run.PQ.blocks_le_kOf D.base) hwork))

/-- The wiring of the link with an instance: the fields of `wq0`, which do not look at the decision.
-/
def wqLX : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto (LinkX D dec)) :=
  ⟨(wq0 D fun _ => true).sh, (wq0 D fun _ => true).ext, (wq0 D fun _ => true).decO,
    (wq0 D fun _ => true).nOpen, (wq0 D fun _ => true).maxDepth⟩

/-- It is lawful if `wq0` is. -/
theorem wqLX_okg (h : (wq0 D fun _ => true).OKG) : (wqLX D dec).OKG :=
  ⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩

/-! ## The interface, the wire, the written protocol -/

/- Bd: the type of leaves' bodies, with how stored symbols (B) and the chain's own symbols (E) lie
among them; early: what of an instance the first query holds; T: the interface's Test, a second
protocol on one external string, without an instance; wT, eT, pT: its wiring and its two ways of
writing a symbol -/
variable {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (early : X → X)
  (T : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- A protocol without a round on one string, with instances. -/
@[reducible] def pX1 (X : Type) (n : ℕ) : InteractiveOracleProof X (oneExternalString n SgX) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }

/-- The interface of an entry with instances: strings of 2 ^ a symbols; its Link has the shape
of the written link (it is `Link0` at the decision "yes"); its Test is the given protocol T; its
Batch has no round; one slot; a first query holds `early x` of an instance x, and no later query
holds the instance; the honest sides are the library's dummies. -/
@[reducible] def LXE : BatchProtocolWithLeafBody Unit X where
  Bd := Bd
  annT := RoundSplits.allLocal _
  annL := RoundSplits.allLocal _
  wordLength := 2 ^ D.a
  Symbol := SgX
  EncodingRandomness := Unit
  encodeIndex := fun _ _ p => (p.val, [])
  decodeIndex := fun _ => some ()
  offline := T
  link := Link0 D fun _ => true
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto (pX1 X (2 ^ D.a))
  honestOfflineProver := _root_.Run.dummyH _ fun _ p => (p.val, [])
  honestLinkProver := _root_.Run.dummyH _ fun _ => (fun p => (p.val, []), fun p => (p.val, []))
  honestOnlineBatchProver := _root_.Run.dummyB _ fun _ p => (p.val, [])
  early := early
  late := none

variable (wT : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → Bd)
  (pT : (p : OPos T.shape) → Bd → Option (OSym T.shape p))

/-- A wire of the sibling at that interface. Test's wiring and ways of writing are given from
outside; nothing is asked of them here. -/
def WXE : QueryLayout 256 (LXE (Bd := Bd) D early T) where
  K := D.K + 1
  T := wT
  Lk := wq0 D fun _ => true
  B := ⟨(), WireE.one (2 ^ D.a) SgX (0, []), inferInstanceAs (DecidableEq Empty), 0, D.a⟩
  depth := D.a
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := B.embE
  prjE := B.getE
  embT := eT
  prjT := pT
  embL := E.emb
  prjL := E.prj
  embB := fun p => p.elim
  prjB := fun p => p.elim

/-- The link with an instance, written into the sibling's oracles: under the tag of Link; on two
external strings; plain parts as they are; symbols as E writes them. -/
def ZXE : WrittenE (WXE D B E early T wT eT pT) (ext2R (LXE (Bd := Bd) D early T)) where
  t := Tag.link
  Q := BatchInteractiveOracleProof.ofProto (LinkX D dec)
  wq := wqLX D dec
  embS := E.emb
  prjS := E.prj
  embP := id
  prjP := some

/-- It meets what is asked of a written batch protocol, if the wiring of `Link0` is lawful. -/
theorem ZXE_ok (h : (wq0 D fun _ => true).OKG) : (ZXE D dec B E early T wT eT pT).OK :=
  ⟨E.prj_emb, fun _ => rfl, wqLX_okg D dec h, linkX_local D dec,
    _root_.Iop.BatchOne.BAnn.allLocal_coherent _, (fun _ h => by cases h),
    (by
      show (wq0 D fun _ => true).ext.depth = D.a
      unfold wq0
      rw [wireTo_ext]
      rfl),
    fun p => by
      show (wq0 D fun _ => true).ext.which p = _ ∧ (wq0 D fun _ => true).ext.leaf p = _
      unfold wq0
      rw [wireTo_ext]
      cases p <;> exact ⟨rfl, rfl⟩⟩

/-- The interface's Test as a written protocol: under the tag of Test; plain parts as they are. -/
def testXE : Written (WXE D B E early T wT eT pT) where
  t := Tag.test
  P := T
  wq := wT
  embS := eT
  prjS := pT
  embP := id
  prjP := some

end TypedOracleCompiler.Slice
