-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/OklaSib.lean: what the entry's arm with the answers alone asks of the wires
(`OKLA`, Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean), at every object with records whose Link is the
written link of the second form of the compiler's verifier side, said over letters (`linkProtocolOfRoundData`,
OnBytes/Flat/LinkSib.lean); and at that link's two sizes (`linkSibFull`, `linkSibSmall`,
OnBytes/Flat/LinkSibAt.lean).

  `wSib`: Link's wire record: the five fields of OnBytes/TypedOracleCompiler/Run/PlanQX.lean's `wqX` at the same
    letters. `wSib_okg`: its laws, from those of the wiring of the rounds and "own trees have
    numbers below 2^16".
  `bodiesSib`: the eight maps of a leaf's body (`Bodies`, Johnson/EntryRec/WiringOfTypedOracleCarrier.lean), a body
    being a string of bits: for Link's oracles OnBytes/TypedOracleCompiler/StringsList.lean's `embT` and `prjT`, for
    a stored table's symbols those of OnBytes/TypedOracleCompiler/StringsAt.lean's `bodyS`; the four for Test and
    the session are letters.
  `okla_sib`: `OKLA` at `LrG T` (Johnson/EntryRec/Defs.lean), Link's annotation that of the written
    link (`Twin.allLo`), Link's wire record `wSib`, the bodies `bodiesSib`, any annotation and wire
    record of Test and any wire record of the session whose record of the stored table is lawful
    (`hB`).
  `okla_sib_ckP`: the same at verifier's messages as hash blocks, from numbers: no round has more
    than K blocks (`bL`) or more than 64 bits of work (`wL`), own trees have numbers below 2^16
    (`ownL`), no tree is deeper than 63 (`dL`).
  `okla_sibFull`, `okla_sibSmall`: at `linkSibFull` | `linkSibSmall`, at every number K of blocks
    from `frD.K` | `srD.K` on: beside that bound, `hB` alone.

The rounds' data `dsFull` | `dsSmall` are the library's `frRds` | `srRds` carried by `PQ.ofLib`
(`dsFull_eq` | `dsSmall_eq`, OnBytes/Flat/LinkSibAt.lean), which keeps entry, kind and opened trees
and lays the one tree as a list: so the four facts on numbers are
OnBytes/Slice/EntryWireNums.lean's and EntryWireDepth.lean's.

Limits. Nothing on a verifier's run, on Link's soundness, locality or errors. Test, the session,
their wire records and maps, the salt's length and the three depths of request trees are letters.
The wiring is one for the entry's arm alone: `OKLA` asks nothing of Test's wire record and of the
session's only that its record of the stored table is lawful; the laws of a whole wiring are not
shown of it. It is another value than the wiring of Johnson/EntryRec/AtMakerA.lean (`wireM`: there
Link stands over the library's rounds, with another wire record and other bodies): no equation joins
the two. No K is shown to be the number of blocks of a whole verifier. That `wSib` at the letters of
a description is that description's own wire record is not said here.


-/
import Johnson.EntryRec.Defs
import Johnson.EntryRec.WiringOfTypedOracleCarrier
import Johnson.TypedOracleCompiler.RecCompile.LinkAns
import OnBytes.Flat.LinkSibAt
import OnBytes.TypedOracleCompiler.StringsList
import OnBytes.TypedOracleCompiler.StringsAt
import OnBytes.TypedOracleCompiler.Run.PlanQXLawsProofs
import OnBytes.TypedOracleCompiler.Run.PlanPull
import OnBytes.Slice.EntryWireDepth

set_option autoImplicit false

namespace OnBytes.RunA

open Iop Compile OnBytes.Flat OnBytes.Slice Cb Cb.Ood
open _root_.Run (ckP chalP bsRound Twin.up)
open _root_.Run.PQ (CK XO View SgX)
open TypedOracleCompiler.Run.PQ (SOf wqX wqS bodyS)
open TypedOracleCompiler.Compile.Batch.Cms (Bodies wireOf2 batTC batLC)

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List XO}
  {dec : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- Link's wire record: the five fields of the written link's, at the same letters. -/
def wSib :
    TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds))) :=
  ⟨(wqX C K chal ds a xs fun _ => true).sh, (wqX C K chal ds a xs fun _ => true).ext,
    (wqX C K chal ds a xs fun _ => true).decO, (wqX C K chal ds a xs fun _ => true).nOpen,
    (wqX C K chal ds a xs fun _ => true).maxDepth⟩

/-- Its laws. -/
theorem wSib_okg (dec₀ : View → Bool) (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (h0 : (wqS C K chal ds dec₀).OKG) : (wSib T K chal).OKG :=
  have h := TypedOracleCompiler.Run.PQ.wqX_okg C K chal ds a xs (fun _ => true) dec₀ hown h0
  ⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩

/-- **The eight maps**: Link's and the stored tables' are the leaf's own string of bits. -/
def bodiesSib (salt : ℕ) (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
    (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
    (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
    (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p)) :
    Bodies (LrG T) (List Bool) where
  embE := (bodyS a salt).embE
  prjE := (bodyS a salt).getE
  embT := embT
  prjT := prjT
  embL := TypedOracleCompiler.StringsList.embT salt C ds
  prjL := TypedOracleCompiler.StringsList.prjT salt C ds
  embB := embB
  prjB := prjB

/-- **What the entry's arm asks of the wires, at the written link over letters.** -/
theorem okla_sib {aT : RoundSplits T.test.shape}
    (wT : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
    (wB : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) T.bat) (hB : wB.ext.OK)
    (depthReq depthReqT depthReqL salt : ℕ)
    (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
    (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
    (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
    (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))
    (dec₀ : View → Bool) (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (h0 : (wqS C K chal ds dec₀).OKG)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    TypedOracleCompiler.Compile.Batch.Cms.OKLA
      (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
        (wSib T K chal) wB a depthReq depthReqT depthReqL
        (bodiesSib T salt embT prjT embB prjB)) :=
  ⟨wSib_okg T K chal dec₀ hown h0, hB, (bodyS a salt).get_e,
    TypedOracleCompiler.StringsList.prjT_embT salt C ds dL, rfl,
    ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩⟩

end

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  (f : _root_.Fmt.Fld) (K : ℕ) {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List XO}
  {dec : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData (ckP f) ds a xs dec))

/-- **The same at verifier's messages as hash blocks, from numbers.** -/
theorem okla_sib_ckP {aT : RoundSplits T.test.shape}
    (wT : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
    (wB : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) T.bat) (hB : wB.ext.OK)
    (depthReq depthReqT depthReqL salt : ℕ)
    (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
    (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
    (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
    (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))
    (bL : ∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) (wL : ∀ d ∈ ds, d.entry.work ≤ 64)
    (ownL : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    TypedOracleCompiler.Compile.Batch.Cms.OKLA
      (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf (ckP f) ds)) (K + 1) wT
        (wSib T K (chalP f K)) wB a depthReq depthReqT depthReqL
        (bodiesSib T salt embT prjT embB prjB)) :=
  okla_sib T K (chalP f K) wT wB hB depthReq depthReqT depthReqL salt embT prjT embB prjB
    (fun _ => true) ownL (TypedOracleCompiler.Run.planPull_okg f K ds (fun _ => true) bL wL) dL

end

/-- The four facts on numbers pass from the library's rounds' data to the carried ones. -/
theorem nums_ofLib (f : _root_.Fmt.Fld) (K : ℕ) (l : List _root_.Run.PQ.RD)
    (bL : ∀ d ∈ l, (bsRound f d.entry d.kind).b ≤ K) (wL : ∀ d ∈ l, d.entry.work ≤ 64)
    (ownL : ∀ d ∈ l, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ l, _root_.Run.PQ.posN d.tree + _root_.Run.PQ.posN d.tree ≤ 2 ^ 64) :
    (∀ d ∈ l.map TypedOracleCompiler.Run.PQ.ofLib, (bsRound f d.entry d.kind).b ≤ K) ∧
      (∀ d ∈ l.map TypedOracleCompiler.Run.PQ.ofLib, d.entry.work ≤ 64) ∧
      (∀ d ∈ l.map TypedOracleCompiler.Run.PQ.ofLib, ∀ n ∈ d.opens, n < 2 ^ 16) ∧
      ∀ d ∈ l.map TypedOracleCompiler.Run.PQ.ofLib, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64 := by
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_, fun d hd s hs => ?_⟩ <;>
    obtain ⟨d0, h0, rfl⟩ := List.mem_map.1 hd
  · exact bL d0 h0
  · exact wL d0 h0
  · exact ownL d0 h0
  · have ht : d0.tree = some s := by
      have : s ∈ d0.tree.toList := hs
      simpa using this
    have := dL d0 h0
    rw [ht] at this
    exact this

variable {I X RI : Type} [Fintype RI] [Nonempty RI] (K : ℕ)

/-- **What the entry's arm asks of the wires, at the written link of the full size.** -/
theorem okla_sibFull
    (T : RestR I X RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE)
      frS.P.T.a linkSibFull) (hK : frD.K ≤ K)
    {aT : RoundSplits T.test.shape} (wT : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
    (wB : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) T.bat) (hB : wB.ext.OK)
    (depthReq depthReqT depthReqL salt : ℕ)
    (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
    (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
    (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
    (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p)) :
    TypedOracleCompiler.Compile.Batch.Cms.OKLA
      (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf (ckP .two) dsFull))
        (K + 1) wT (wSib T K (chalP .two K)) wB frS.P.T.a depthReq depthReqT depthReqL
        (bodiesSib T salt embT prjT embB prjB)) := by
  have h := nums_ofLib .two K frRds (fun d hd => (fr_wire_blocks d hd).trans hK) fr_wire_work
    fr_wire_own fr_wire_depth
  rw [← dsFull_eq] at h
  exact okla_sib_ckP .two K T wT wB hB depthReq depthReqT depthReqL salt embT prjT embB prjB h.1
    h.2.1 h.2.2.1 h.2.2.2

/-- **The same at the small example.** -/
theorem okla_sibSmall
    (T : RestR I X RI (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE)
      srS.P.T.a linkSibSmall) (hK : srD.K ≤ K)
    {aT : RoundSplits T.test.shape} (wT : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
    (wB : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) T.bat) (hB : wB.ext.OK)
    (depthReq depthReqT depthReqL salt : ℕ)
    (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
    (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
    (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
    (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p)) :
    TypedOracleCompiler.Compile.Batch.Cms.OKLA
      (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))
        (K + 1) wT (wSib T K (chalP .two K)) wB srS.P.T.a depthReq depthReqT depthReqL
        (bodiesSib T salt embT prjT embB prjB)) := by
  have h := nums_ofLib .two K srRds (fun d hd => (sr_wire_blocks d hd).trans hK) sr_wire_work
    sr_wire_own sr_wire_depth
  rw [← dsSmall_eq] at h
  exact okla_sib_ckP .two K T wT wB hB depthReq depthReqT depthReqL salt embT prjT embB prjB h.1
    h.2.1 h.2.2.1 h.2.2.2

end OnBytes.RunA
