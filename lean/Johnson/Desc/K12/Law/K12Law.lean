-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/K12Law.lean: the law of the proximity test with the two propositions on the
code switch laid in.

Lays `switchUnfolds` (Johnson/Desc/K12/Law/SwUnfold.lean) and `seatReads`
(Johnson/Desc/K12/Law/SwRead.lean) into `k12_law` (Johnson/Desc/K12/Law/Top.lean). What is left as
premises is `StartK` and two numbers of the place.
Main names:
  `k12_yes_acc`: the test on the plan, `StartK` and a yes of the decision of `proximityTestKind guardedProximityTestParts p` give
    `c.Acc q y z g b`.
  `k12_step_acc`: the same from a yes of `Block.step`.
Limits: The law of the proximity test is not proved for a view that comes from bytes: the fields of
`StartK` are premises here; Johnson/Desc/K12/Law/TopG.lean to TopF.lean pay all but the reading of
the view. That the premises on the view and the block's yes hold together on any view is not shown;
the two public fields of `StartK` have a member wherever `pubOk` says yes (`pub_of_ok`,
Johnson/Desc/K12/Law/ChainOf.lean). It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the
parts of Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves. No
statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain functions of that
program, some with names that begin with `Blk.`, are reached. No soundness is claimed. Nothing here
is about hiding.
-/
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.Law.SwRead
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem k12_yes_acc (p : P12) (he : p.early = true) (ha : p.answers = 1) {s : Sg} (c : Chain s)
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl)
    (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h0 : StartK p c q y z g b t0 rs gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : c.Acc q y z g b :=
  k12_law p he ha (H2K.Sw.switchUnfolds p) H2K.Sw.seatReads c q y z g b t0 tE rs gs hp h0 h

theorem k12_step_acc (p : P12) (he : p.early = true) (ha : p.answers = 1) {s : Sg} (c : Chain s)
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl)
    (firstTree : Nat) (t0 tE : T12) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h0 : StartK p c q y z g b t0 (rs.map noDigest)
      (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))).map
          (·.length))
        (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
          (rs.map (·.drawn))).flatMap id).length)))
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n)) : c.Acc q y z g b :=
  k12_law_of_step p he ha (H2K.Sw.switchUnfolds p) H2K.Sw.seatReads c q y z g b firstTree t0 tE rs
    cols n hp h0 h

end H2K.JointK
