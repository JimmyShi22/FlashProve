-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TopC.lean: the law of the proximity test at the chain of the place.

The chain is built, and its public clauses are paid by a Boolean on the place and the record's
codes: `pubOk` with `pub_of_ok` (Johnson/Desc/K12/Law/PubOk.lean, ChainOf.lean). Statements and
proofs.
Main names:
  `StartH`: what is still assumed in front of the test: `gp` and `keys` (public, on the group under
    test), `reads : ReadsK`, the claim, the layout and the places.
  `k12_step_accC`: `p.early = true`, `p.answers = 1`, the test on the plan and `pubOk p t0.st.codes
    = true` give a chain c, whose written rounds are the place's declared rounds behind "BAT" and
    whose stages are the place's, such that for all transcripts b: `StartH` and a yes of
    `Block.step` give `c.Acc` at the batched claim and at the words read off the members' and the
    first mask's written oracles.
Limits: The law of the proximity test is not proved for a view that comes from bytes: `ReadsK` is a
premise. That the premises on the view and the block's yes hold together on any view is not shown;
the two public fields of `StartK` have a member wherever `pubOk` says yes (`pub_of_ok`,
Johnson/Desc/K12/Law/ChainOf.lean). It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the
parts of Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves.
The chain's radii and error counts are letters (`Letters`): neither `Chain.Acc` nor `Chain.Pub`
reads them. `pubOk` was evaluated at the four proximity tests of the two stored example proofs, the
full-size one and the smaller one: true at each, and false at forty spoiled inputs [the prints are
not in this library]. No statement and no proof of this file reaches a routine that runs in a
context of the program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain
functions of that program, some with names that begin with `Blk.`, are reached. No soundness is
claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.TopG
import Johnson.Desc.K12.Law.ChainOf

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw (PartsP)
open H2K.Pub (Letters pubOk pub_of_ok sgOf writtenOf WR)

/-- What is still assumed in front of the test. -/
structure StartH (p : P12) {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (b : c.Bl) {G : Gp s}
    (P : GpData G) (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc)
    (g : ℕ → ℕ → Option (List UInt64)) (t0 : T12) (rs : List Fmt.RoundView) (gs : Gs) : Prop where
  /-- public -/
  gp : P.Pub p.nums.firstTree
  /-- public -/
  keys : ((cutS (laidS p) (s.h + s.g)).flatMap fun r =>
    r.opens.map fun x => x.1.tree - p.nums.firstTree) = P.ts.map P.key
  /-- on the reading of the view -/
  reads : ReadsK p c b P o oF g rs gs
  /-- which claim the law speaks of; and, on the record, the layout and the places -/
  behind : ∀ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
    rs.take 1 = [r] → First.Close.bat t0.st t0.g e r = .ok (row, L, S') →
    ClaimNow c q row ∧ P.LayG L ∧
    ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage) (id : Nat)
      (st : Statement) (book : TreeBook), p.nums.stages = first :: rest →
      stageAt p 0 first = some cu →
      MaskCase p { t0 with st := S', pass := .claim row L } (ioppFoldShape cu L) id st book →
      PartsP P st book id

/-- The law of the proximity test, of `Block.step`, at the chain of the place. -/
theorem k12_step_accC (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 : T12)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hpub : pubOk p t0.st.codes = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧ c.rds = l.map WR.rd ∧
          stagesOf c = p.nums.stages ∧
      ∀ (q : GE × ((sgOf a).cIn.J → GE)) (gW : (sgOf a).cIn.Word) (b : c.Bl) (G : Gp (sgOf a))
        (P : GpData G) (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc)
        (g : ℕ → ℕ → Option (List UInt64)) (firstTree : Nat) (tE : T12) (rs : List Fmt.RoundView)
        (cols : List OpenedColumn) (n : Nat),
        StartH p c q b P o oF g t0 (rs.map noDigest)
          (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
              (rs.map (·.drawn))).map (·.length))
            (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
              (rs.map (·.drawn))).flatMap id).length)) →
        (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n) →
        c.Acc q (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
          (frOf (sgOf a) P.aF P.oF P.dF oF) gW b := by
  obtain ⟨a, rest, w0, l, c, hs, hw, _, hrds, hst, hpb⟩ := pub_of_ok X p t0.st.codes hpub
  refine ⟨a, rest, w0, l, c, hs, hw, hrds, hst, ?_⟩
  intro q gW b G P o oF g firstTree tE rs cols n h0 h
  exact k12_step_accG p he ha c q gW b P o oF g firstTree t0 tE rs cols n hp
    ⟨hst, hpb, h0.gp, h0.keys, h0.reads, h0.behind⟩ h

end H2K.JointK
