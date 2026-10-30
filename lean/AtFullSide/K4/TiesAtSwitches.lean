-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K4/TiesAtSwitches.lean: CONDITIONAL. Two statements with their
proofs; no definition.

WHAT THAT IS, AND WHAT NOT. Given for the like tie
at group 0: it is an identity of two readings at each run's coins: no law over
coins; nothing on how the element is drawn, on who else reads or spends it, or that it stands at no
other entry; the ties' other premises stay, and no thread is shown to stand at any state. At the
later groups: «no law over coins» holds of this tie as
of group 0's: an equation at each run's coins. K2's authors' warning, which goes with every
quotation of their `share_msgs_fit`, to the letter: "that the frame hands the part its coins
(`handed`) is neither asked nor paid here: whoever quotes this law at a book names that at that book
beside it." AT THE BOOK A.B: THAT `handed` RETURNS AT THE SWITCH's PLACE IS SHOWN BY NO LAW THAT IS
CALLED HERE: where it
does not return, the switch's text answers nothing, and hA fails as soon as some input meets Vd and
K4 takes at least two slots; under hT the first is so.

What is here. THE TIE OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) ON THE MASK ROW,
`K4MaskTieAt` (Honest/K4/Law/ScriptAt.lean), AT THE JOINED SCRIPT `joinQ` (Honest/Thread/Join.lean,
of other writers) AND THE BOOK A.B THAT `onlineProverFromPublicFiles` RETURNS, AT THE ELEVEN LATER GROUPS g = 1, …, 11.
THE SENDER IS THE CODE SWITCH (the kind K2) AT THE PLACE WITH THE LINK 2 g; THE MESSAGE IS ITS
NUMBER 2 (AtFullSide/K4/MaskRowsLaterW.lean).
  `switchTxt_look_one`   no head; at any book, place and message n but the last, of one mask row:
      what the switch's text `switchMsgTxt` answers at (true, 0, ν), ν below the mask row's length,
      is the element number `maskBase` + ν of what the run holds at the address ⟨p.place, 0⟩. It is
      K2's authors' `msgTxt_mask` (Honest/K2/Law/MaskTxt.lean), which ends at the part's own cut,
      with the library's `cut_eAt` (Honest/K2/Law/Reads.lean) from the cut to the look. KIN: K1's
      authors' `msgTxt_mask_look_one` and `look_of_cut` (Honest/K1/Law/LookOfCut.lean) are the like
      at the shared sending's text: `look_of_cut` calls the same `cut_eAt`; not called here.
  `k4MaskTie_at_switch_fit`   our `k4MaskTie_of_lot` (Honest/K4/Law/W/MaskTieOfLot.lean) at Q :=
      the joined Script, Vq := Vd, Ls := the switch's lot for its message number 2.

WHICH PREMISE OF `k4MaskTie_of_lot` IS HAD BY WHICH CALL. An opening is drawn out of the head
(h.laid.opened); no letter of it stands in a statement; THE SEAM A.Z = Zp, A.G = Bs.G₀ is
`atPure_at_laid_ground` (Honest/AtHeadGround.lean): hin and hA are carried over it by rewriting.
  the place p   `later_seam` (AtFullSide/K4/MaskRowsLaterW.lean)
  J    our `k4Book_at_atPure` (Honest/K4/Law/W/BookAtPure.lean), at the row that `rowLater_at_head`
       names; its owner and start are rewritten by `later_seam` to ⟨p.place, 0⟩ and `maskBase` … 2
  hn   `later_seam` (through `maskNum_later`)
  hA   STAYS A PREMISE HERE, fenced by Vd and N, at each place of the plan's list with the link 2 g
  hE   `switchTxt_look_one`, at L := 8192
  hL   `maskReads_room` (AtFullSide/K1/OpeningRoomK4.lean),
       which speaks at every group below 12
  OS   `share_msgs_fit` (Honest/K2/JoinShare.lean) at F, hin
       and n := 2
  hV   the thread's own clause "valid" in hT, READ BY ITS POSITION (the seventh): if the thread's
       sentence gains a clause that line of the proof breaks
  hN   STAYS A PREMISE HERE
THE FORM THAT ASKS LESS OF THE LIST AND THE FORMS WITHOUT hA
AND hN ARE NOT LAID HERE.

Not shown here. EMPTINESS FIRST: NO INSTANCE OF ALL THE PREMISES OF THE SECOND STATEMENT TOGETHER
CAN BE SHOWN TODAY: the thread's sentence hT has no known instance at the full size at any Script.
hA IS MET IN NO FILE BENEATH THIS ONE: it asks that the frame hands the switch its coins at A.B,
that the lot's closing returns and that the rows are laid, at every input in Vd and all challenges
from N on.
F has K2's authors' `joinFit_full`
(AtFullSide/K2/JoinFitFull.lean; a trial) at one list, where hin is their `shareIn_add_left`, over
the seam. I found no two premises that bar each other. Where hT stands at no state the statement
says nothing. THAT THE SWITCH's LOT IS THE ONLY ONE OF THE LIST WITH THAT NUMBER is not said: F's
field msgs (in its own docstring's words "all lots of one message agree") is what `share_msgs_fit`
spends. WHO ELSE IS GIVEN THESE ELEMENTS OF THE RUN, AND UNDER WHICH MARK OF THE BOOK, IS NOT SAID
HERE. Group 0 is shut out by h1: AtFullSide/K4/TiesAtOpening.lean. Each statement is an equation at
a run's own coins, entry by entry: nothing is said on how an element of the coins is sampled, no
value of a coin is cut off, nothing is counted. The full size and the format's second hash function alone.
The limits of the files named hold here too. Nothing on soundness, on completeness or on any other
property.
No property is claimed.
-/
import AtFullSide.K4.MaskRowsLaterW
import AtFullSide.K1.OpeningRoomK4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskTieAtJoin
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (WtF lettersHead Others TreeLot joinQ JoinFit)
open ProofFile.Honest.K1 (SendJob PlaceIn)
open ProofFile.Honest.K2 (SwitchPlace Closing switchSent switchFresh switchMsgTxt switchPlaces
  switchShareAt switchNum sendingDue maskBase maskLength lotClosingAt segmentsOf)
open ProofFile.Honest.K2.Law (ShareIn share_msgs_fit msgTxt_mask)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open AtFullSide.K1 (maskReads_room)
open AtFullSide.K4 (rowLaterW rowLater_at_head later_seam)

/-- CONDITIONAL on hn, h1, hν and hy. **FROM THE SWITCH's TEXT TO THE LOOK, AT A MESSAGE OF ONE MASK
ROW THAT IS NOT THE LAST.** An identity of two readings of one element, at each run's coins. Where
the text answers nothing hy is met at no y. -/
theorem switchTxt_look_one {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (ch : ℕ) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) {n : ℕ}
    (hn : n + 1 < (switchSent p.sizes p.others).size)
    (h1 : ((switchSent p.sizes p.others).getD n default).shape.maskRows = 1) {ν : ℕ}
    (hν : ν < maskLength p.sizes.codes (switchSent p.sizes p.others) n) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (y : Cb.Gl.E)
    (hy : switchMsgTxt ch D readers closing p n k w hd true 0 ν = some y) :
    (k.look ch ⟨p.place, 0⟩).2.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n + ν) = .ok y := by
  have hA : (switchMsgTxt ch D readers closing p n k w hd true
      (ν % ((switchSent p.sizes p.others).getD n default).shape.maskRows)
      (ν / ((switchSent p.sizes p.others).getD n default).shape.maskRows)).isSome = true := by
    rw [h1, Nat.mod_one, Nat.div_one]
    exact Option.isSome_iff_exists.2 ⟨y, hy⟩
  have e := msgTxt_mask ch D readers closing p (by omega) (by omega) hν k w hd hA
  rw [h1, Nat.mod_one, Nat.div_one, hy] at e
  cases hc : K1.lentCut k ch ⟨p.place, 0⟩ (sendingDue p.sizes.codes
      (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) with
  | none =>
    rw [hc] at e
    have e0 : (some y : Option Cb.Gl.E) = none := e
    cases e0
  | some c =>
    rw [hc] at e
    have e1 : some y = (c.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n + ν)).toOption := e
    cases hx : c.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) n + ν) with
    | error s =>
      rw [hx] at e1
      have e0 : (some y : Option Cb.Gl.E) = none := e1
      cases e0
    | ok x =>
      rw [hx] at e1
      have e0 : (some y : Option Cb.Gl.E) = some x := e1
      obtain rfl : y = x := Option.some.inj e0
      have hc' : (k.look ch ⟨p.place, 0⟩).2.cut ⟨0, 0⟩ (sendingDue p.sizes.codes
          (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) = some c := hc
      have e2 : (k.look ch ⟨p.place, 0⟩).2.eAt (0 + (maskBase p.sizes.codes
          (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n + ν)) =
          .ok y := K2.Reads.cut_eAt hc' hx
      rw [Nat.zero_add] at e2
      exact e2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {W₀ Rc Ky Tr X₀ X' Xi Xj : Type} {Wa Rca Tra Xa₀ Xa : Type}
  {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (front : ℕ)
  (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xi)
  (own₀ : Xj) (jobs : List (ℕ × SendJob (PlaceIn Xi) Xj))
  (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, hAP, F, hin, Lh, h1, hQ, hA, hT and hN. **THE TIE ON THE MASK ROW AT A LATER
GROUP, AT A FIT LIST THAT HOLDS THE CODE SWITCH's SHARE.** The share is spelled at the public part
A.Z and the ground A.G of what `onlineProverFromPublicFiles` returns. hA: the switch's text for its message number 2
answers at the entries that K4 reads, at every input in Vd and all challenges from N on: at a book
that does not hand the switch its coins hA fails. The head says which premise of
`k4MaskTie_of_lot` is had by which call. -/
theorem k4MaskTie_at_switch_fit (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs O)
    (Dr : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rest : ℕ → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hin : ShareIn (switchShareAt A.B cF.blocksInOrder front A.Z A.G Dr readers rest) O)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (h1 : 1 ≤ g)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {N : ℕ}
    (hA : ∀ p ∈ switchPlaces A.Z A.G, p.link = 2 * g →
      ∀ (k : Coins A.B) w (hd : List Fmt.Drawn) ν, Vd w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (switchMsgTxt 0 Dr readers (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p 2 k w
        (hd.take (front + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))) true 0 ν).isSome = true)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
      carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hN : N ≤ mm.st.heard.length) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  obtain ⟨Bs, base₀, Op⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid Op.blank hAP
  rw [eZ, eG] at hin hA
  obtain ⟨p, hp, hl, hnum, ho, hb, hsz, hfs, hr1, hlen⟩ := later_seam h Op h1 Lh.lt
  have hP := k4PubG_of Lh hQ
  obtain ⟨-, -, row', idx, hr', -, J, -⟩ := k4Book_at_atPure h hAP (Rc := Rc) (X := X') cells
    weights tokens (look Qp) g Lh.lt Qp hP
  obtain rfl : row' = rowLaterW g :=
    Option.some.inj (hr'.symm.trans (rowLater_at_head h h1 Lh.lt))
  rw [ho, hb] at J
  unfold switchShareAt at hin
  have OS := share_msgs_fit _ _ _ _ _ _ _ _ _ _ _ _ F hin cellsQ tok Vd N hp
    (Nat.lt_of_succ_lt hsz) hfs
  have hv : mm.st.input = w₁ ∧ Vd mm.st.input := hT.2.2.2.2.2.2
  exact k4MaskTie_of_lot h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O) test
    carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ J
    ⟨switchNum Zp p 2, front + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place),
      switchMsgTxt 0 Dr readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p 2⟩
    hnum (fun k w hd ν hw hn a b => hA p hp hl k w hd ν hw hn a b) (L := 8192)
    (fun k w hd ν y' hν hy => switchTxt_look_one 0 Dr readers _ p hsz hr1
      (by rw [hlen]; exact hν) k w hd y' hy)
    (Nat.le_succ_of_le (maskReads_room h Op Lh.lt hP)) OS hT hv.2 hN

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.switchTxt_look_one
#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_switch_fit
