-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ScriptAtJoin.lean: the kind "the code switch" (K2): THE
PREMISE's FORM `K2Script` (Honest/K2/Law/PlaysScript.lean: what the kind asks of a thread's tables
at the switch's member) AT THE FIRST THREAD's LETTERS AT THE LIBRARY's HEAD WHERE THE SCRIPT IS THE
JOINED ONE (`joinQ`, Honest/Thread/Join.lean), AT EVERY SWITCH OF THE PLAN. BY CONSTRUCTION OF THE
JOINED SCRIPT: it is laid from lots, the list is fit, and it holds the kind's share: so its tables
at the switch's trees are the share's. Two laws; no definition; nothing is evaluated here.

  `k2Script_of_ownTrees`   general in the thread: `K2Script` is the frame's form `OwnTrees`
                    (Honest/Thread/ScriptLots.lean) at the kind's own table, at no challenge of the
                    member's own, at as many trees as the numbers' roots or more
  `k2Script_at_join`   THE END: by `share_trees_fit` (Honest/K2/JoinShare.lean). AS IT LIES it is
                    the premise Sc of `switch_playsS_at` and its two arms (Honest/K2/Law/
                    PlaysAtArms.lean), at all 25 places; that `switchNo` p is 14 l + 2 at the place
                    of link l is `SwitchArm`'s first limb (BlockAtHead.lean)

By, ours: `share_trees_fit` · `borders_apart_at_head` (Honest/K2/Law/SwitchBorders.lean) ·
`k2_member_at_head`, `k2_block_at_head` (RecordAtHead.lean, BlockAtHead.lean); of other authors:
`borderNo_written` (Honest/K1/Law/MembersByBorder.lean) · `JoinFit` (Honest/Thread/JoinFit.lean). Of
the files named in this head Honest/Thread/ScriptLots.lean alone is sealed.

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THE END HOLDS EMPTILY. F (the list is fit) AND hin (it holds the kind's share) ARE
PREMISES. hroots (as many oracle messages as roots) is a premise: that of `switch_playsS` of the
same name; its payer: `rootsW` (PlaysAtArms.lean) at all 25 places.
IT IS NO PAYMENT BY A RUN: that a run has the
joined Script is not said. ON WHICH TABLE STANDS AT WHICH TREE, AND FROM WHICH BORDER ON IT TURNS NO
MORE: nothing on what a table holds: what `share_trees_fit`'s docstring says of the table without a
word holds here. A run's coins stand under "for all" in the form's first field and go whole to the
kind's table. NOT IN FRONT OF A LAW OVER COINS. The full size and the format's second hash function alone.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysScript
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchBorders
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open IM (k2P)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread

/-- **`K2Script` is `OwnTrees` at the kind's own table.** -/
theorem k2Script_of_ownTrees {Bk : ProverCoinCounts} {X W₀ Rc Xi Tr Pb : Type}
    {T : Thread Bk S ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b r : Nat} {Sd : Sender}
    {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {closing : Closing}
    {p : SwitchPlace} {q : P2}
    (h : OwnTrees T b r
      (fun j k w hd => (p.place, switchTableAt Bk T.chain Sd D readers closing p k w hd j))
      (fun _ => 0)) (hr : q.roots ≤ r) : K2Script T b Sd D readers closing p q :=
  ⟨fun j hj => h.table j (Nat.lt_of_lt_of_le hj hr),
    fun j hj => h.fixed j (Nat.lt_of_lt_of_le hj hr)⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Xj Xo : Type}
  {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn Xj} {own₀ : Xo}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Xo)}
  {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)} {D : RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {rest : Nat → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr)}

/-- **`K2Script` AT lettersHead WHERE THE SCRIPT IS THE JOINED ONE, AT EVERY SWITCH OF THE PLAN.**
a, nm, st: any: of the numbers the roots alone are read. NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2Script_at_join (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) (a : Place) (nm : String) (st : First.K2.At)
    (hroots : (k2P Zp a nm st n).sent.length = (k2P Zp a nm st n).roots) :
    K2Script (lettersHead h H
        (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).thread (switchNo p) (coreSender freshTable) D readers
      (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p (k2P Zp a nm st n) := by
  obtain ⟨blk, member, -⟩ := k2_member_at_head h O hp
  obtain ⟨Pp', n', nm', st', -, -, hP', hn', -, ⟨-, -, ho⟩, -, -⟩ := k2_block_at_head h O hp member
  obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  have eb : borderNo cF.blocksInOrder p.place = switchNo p := K1.borderNo_written h p.place
  unfold switchShareAt at hin
  have OT := share_trees_fit (F := F) (hin := hin) (cells := cells) (tok := tok)
    (T := (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
      carryX item n₁ n₂ b₀ Vd Rd Kp w).thread) (hbs := rfl) (hfr := rfl) (htab := rfl)
    (hfix := rfl) (hnd := borders_apart_at_head h O) (hp := hp) (blk := blk)
    (hblk := by rw [eb]; exact member)
  rw [eb] at OT
  refine k2Script_of_ownTrees OT ?_
  rw [ho, ← hroots]
  show (P1K2.oraclesAt n'.grp n'.codes n'.sent).length ≤ _
  simp
  exact Nat.le_refl _

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2Script_of_ownTrees
#print axioms ProofFile.Honest.K2.Law.k2Script_at_join
