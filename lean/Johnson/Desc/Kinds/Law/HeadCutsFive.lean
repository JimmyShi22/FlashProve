-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/HeadCutsFive.lean: THE FIELD head_cuts OF THE TOWER's STRUCTURES FiveF AND
ThreeF, IN THE FIELD's OWN LETTERS AT THE COMPOSED MEANING's CONSTANT, FROM THE CONSTANT's HEAD AND
THE PUBLIC TEST madeRow. Joinings: no new weight.

The field reads (Johnson/P5J/TowerEnd.lean, FiveF; Johnson/P5J/KindsLaterAtMg.lean, ThreeF; the
same text): HeadCuts pp putReq HH headPart, HH a written call of hidAtSeat. AtMg.Five and AtMg.Three
(Johnson/P5J/RowsAtMg.lean, KindsLaterAtMg.lean) fill its letters in; AtMgA.Five and AtMgA.Three
(RowsAtAll.lean, KindsLaterAtAll.lean) lay the closed structure of parameters h.𝔇 for the last
letter. The conclusions below are that text with these arguments put in. It reads no field of the
structure Free and not the depth: so one statement serves both structures at every Free.

  head_cuts_of_guard     from the head and the test as a verifier's list of entry tests writes it
                         (not at the full size's key, or the test): Law/HeadCutsOfRow.lean's
                         headCuts_of_row, restated in the field's letters: equal by definition
  head_cuts_of_madeRow   the same from the bare test's accept
  five_head | three_head the term stands in the field's place of h.Five L n and of h.Three L, at
                         every L and n. TESTS OF FIT: they take a member and give a member: they
                         show nothing new, and no maker can call them (a maker has no member)

WHAT IT IS NOT. Implications. THE HEAD h IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). THE TEST's ACCEPT
IS A PREMISE HERE (Law/HeadCutsAtHead.lean has it from the head, where the list of entry tests holds
the test). Nothing on a prover, a run or an error bound. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.HeadCutsOfRow
import Johnson.P5J.KindsLaterAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (ppAtFiles)
open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey)
open OnBytes.Maker (WholeD)
open OnBytes.Flat (putReq numsFull)
open P5J (AtMgA TS F0T Free At.X At.cs At.arr At.ms At.N At.layout At.num At.d₀ At.EAt At.Tok
  hidAtSeat HidAt tokVOf dtK CellsM colsAt FiveF ThreeF)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD head_cuts IN ITS OWN LETTERS, FROM THE HEAD AND THE TEST AS A LIST WRITES IT.** -/
theorem head_cuts_of_guard (h : AtMgA o Z D r Zp Np cF x)
    (hr : (!Decidable.decide (keyOfScan Zp.p.X.P = fullKey) || madeRow Zp) = true) :
    P5J.HeadCuts (ppAtFiles Z.pol Z.KL) putReq
      (hidAtSeat (At.X Zp) (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
        (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp)
          (Meaning.sizesOf (At.X Zp))) tokVOf
        (fun a => (Meaning.backReq ((fun q : ProofFile.InstPub => q.request) a.1)).getD At.d₀)
        (fun a y => dtK (At.EAt Z) o Zp Np cF h.plan.shape 0 y.cell a) h.plan.hN h.plan.hG :
        HidAt (At.X Zp) (F0T o Zp Np cF).XiPub (Wit (CellsM numsFull) At.Tok MsgT) numsFull.rows
          (colsAt numsFull))
      (h.toAtMg.𝔇 h.𝔇).headPart :=
  headCuts_of_row h hr

/-- **The same from the bare test's accept.** -/
theorem head_cuts_of_madeRow (h : AtMgA o Z D r Zp Np cF x) (hm : madeRow Zp = true) :
    P5J.HeadCuts (ppAtFiles Z.pol Z.KL) putReq
      (hidAtSeat (At.X Zp) (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
        (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp)
          (Meaning.sizesOf (At.X Zp))) tokVOf
        (fun a => (Meaning.backReq ((fun q : ProofFile.InstPub => q.request) a.1)).getD At.d₀)
        (fun a y => dtK (At.EAt Z) o Zp Np cF h.plan.shape 0 y.cell a) h.plan.hN h.plan.hG :
        HidAt (At.X Zp) (F0T o Zp Np cF).XiPub (Wit (CellsM numsFull) At.Tok MsgT) numsFull.rows
          (colsAt numsFull))
      (h.toAtMg.𝔇 h.𝔇).headPart :=
  head_cuts_of_guard h (by rw [hm, Bool.or_true])

/-- A test of fit: the term stands in the field's place of the five rows, at every L and n. -/
theorem five_head (h : AtMgA o Z D r Zp Np cF x) (hm : madeRow Zp = true)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) (n : ℕ) (V : h.Five L n) : h.Five L n :=
  FiveF.mk (head_cuts_of_madeRow h hm) (FiveF.reply_leaves V) (FiveF.shared_joint_count V)
    (FiveF.leads3_last_chains_table V) (FiveF.tables_fit V)

/-- A test of fit: the term stands in the field's place of the three rows, at every L. -/
theorem three_head (h : AtMgA o Z D r Zp Np cF x) (hm : madeRow Zp = true)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) (V : h.Three L) : h.Three L :=
  ThreeF.mk (head_cuts_of_madeRow h hm) (ThreeF.reply_leaves V) (ThreeF.tables_fit V)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.head_cuts_of_guard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.head_cuts_of_madeRow
#print axioms VerifiableInference.Desc.Kinds.Head.Law.five_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.three_head
