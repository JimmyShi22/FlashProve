-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorOfFoldAt.lean

What it proves. doorUF_of_carried (DoorOfFold.lean) under the head P5J.AtMg, at the plan of the
proof file's shared chain: its public premise on what goes out with o_u is a theorem there. What
stays asked: the eight by name (hb; there are such: blocks_head, NearAtHead.lean; eight_of,
MarksBehind.lean), the three ties on one front and one view, and the fold's return.

Names.
  doorUF_of_carried_head   the theorem.

By what. doorUF_of_carried (DoorOfFold.lean); facts_at_head (NearAtHead.lean).

Limits. Those of DoorOfFold.lean: one front and one view; the three ties are premises; nothing where
the fold fails, and the fold's return can narrow the input; it moves no count; it gives no SaysAt;
the test on G_u alone. c, tests, last and the type of claims are free: that they are those of the
proof file's own description is not drawn here. No example of the head is shown here. It stands over
files that are not in the library yet, as MarksBehind.lean does. Nothing on completeness, on
soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorOfFold
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (Seat.enter)
open Desc.K14 (St blocks first chainOf)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head: wherever the fold over the library's shared chain, carried to another type of
claims, returns at the view v, doorUF's state is the one with which that fold enters the test on
G_u.** The ties hk, hr, hn, hc and the premise hv: as in doorUF_of_fold. True of one front and one
view; nothing where the fold fails; no SaysAt follows. -/
theorem doorUF_of_carried_head {Cl : Type} (h : P5J.AtMg o Z D r Zp Np cF)
    (c : OnBytes.Model.Verify.Chains) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (key : W → TableKey) (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (k : TableKey) (v : Fmt.View) (hk : key w = k)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hn : fr.seen.rounds.length =
      ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length)
    (hc : ∃ more, v.opened = colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds ++ more)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 ((chainOf c (K1.qAt Zp Np) tests last).retype (Cl' := Cl)).blocksInOrder
      (first (K1.qAt Zp Np).codes k) v.rounds v.opened = .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes k) v.rounds
        v.opened = .ok (d8, rest, more) ∧
      foldBlocks 0 (((chainOf c (K1.qAt Zp Np) tests last).retype (Cl' := Cl)).blocksInOrder.drop 9) d8 rest
        more = .ok out ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes (key w))
        fr.seen.rounds (colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) w fr) :=
  doorUF_of_carried c _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb (facts_at_head h).2.2 key stored w fr k v hk
    hr hn hc tests last out hv

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.doorUF_of_carried_head
