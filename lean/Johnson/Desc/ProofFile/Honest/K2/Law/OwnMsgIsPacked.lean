-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnMsgIsPacked.lean: the kind "the code switch" (K2): what the
joined `Script`'s witness holds at an entry of one of a switch's own messages at which the layout
lays an element of an array "M mu": the packing of the reader's cells. General in the plan, the list
and the place: no head. No definition. Lemmas with their proofs: joins; none of the library's goals.

  `switch_lays`, `switch_val`   where the layout lays element (i, c) of such an array of segment l,
                    in a message that fits, the switches' own data (`switchData`,
                    Honest/K2/OwnData.lean) lays an entry, and it is `packedCells` at (l, mu, i, c)
  `senderOwn_val`   so the own data that the switch's part is handed there, at the filling
                    `withSwitchData`, is that element, as the frame reads it (`asE`)
  `msg_own_packed`  THE END: at a fit joined list that holds the switches' share, at a run's coins
                    at which the part is handed its coins and its rows are laid: message number
                    num p n of the witness has that image at the main row and place

By, of other authors: `share_msgs_fit` (Honest/K2/JoinShare.lean) · `msgTxt_main_e`,
`msgTxt_main_f` (MainTxt.lean of this folder) · `with_own` (Honest/K2/OwnData.lean) ·
`lays_of_back`, `entry_of_back` (Honest/Law/LaidSent.lean) · `lays_clear`
(Honest/Law/LaidLaw.lean) · `fits_of_msgFits`, `laidBack_iff` (Honest/Law/) · `asE_inl`
(Honest/K1/AgreeTools.lean).

Kin, of other authors, none imported. On no row: Honest/K1/Law/FirstIsPacked.lean: its `cells_val`
says what `switch_val` shows in its closing lines; its `fill_val` says of the first sending's
messages what the three lemmas of section 1 say of a switch's. `K1.firstData` takes the seat as a
parameter, so a single lemma could serve the two kinds; there is none yet. In the library:
`cellsVals_pack`, `cellsVals_size` (Honest/K5/Law/PackedVals.lean).

What stays a hypothesis in the end. F, hin: the list is fit and holds the share. hw: no message of
the sending has main rows and no sample. hn, h1: the message is one of the sending's, and the switch
is its first sender. hH, hV: the part is handed its coins; its rows are laid. hv: the input is
valid. t1 to t6, hfit, ha, hrp, hmu, hz, hi: public: the own message's address has the seat (l, the
array's message); that message's shape in the request is the sending's; the codes are the ground's;
the code is there and its length is a power of two; the message fits; the array lies in it; the
layout's place; the name reads as mu; the values' size; the element lies inside it.

Limits. An equation on the Script's witness, at each run's coins: what is written where. The coins
stand on the left alone, inside the witness; the right side is a function of what the reader yields
of the input. It belongs to the argument that an honest run is accepted, and is not to be quoted
beside a law over coins. It speaks of the reader's cells (`readers w`): that these are any trace's
is not said. No list is laid and no letter is tied to a plan. Where the part is handed nothing, or
its rows are not laid, nothing is said. Nothing at a pad's place, at a mask row, at a kept copy's
own pad. That the joined Script is the honest prover's is not said here: it is laid from lots, and
holds what their texts say. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.OwnData
import Johnson.Desc.ProofFile.Honest.Law.LaidSent
import Johnson.Desc.ProofFile.Honest.K1.AgreeTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz packedCells)
open OnBytes.Params (ReqArray ReqMessage)
open VerifiableInference.Desc (Block laidAt)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread (TreeLot Others joinQ JoinFit)

/-! ## 1 The switches' own data -/

section
variable (S₀ : Sz) (Z : Pub) (G : Ground) {x : MsgAddr} {l : ℕ} {a : ReqArray}
  (t1 : switchSeat Z G x = some (l, a.message))
  (hfit : msgFits G.first.codes G.first.shape G.first.layout l a.message = true)
  (ha : a ∈ (G.first.layout.link.getD l []).filter fun y => y.message == a.message) {i c : ℕ}
  {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {z : ℕ × ℕ}
  (hz : (K1.cellsVals S₀).size l a.name = some z) (hi : i < z.1 ∧ c < z.2)
include hfit ha hrp

/-- From the layout's place the way back reads the element. -/
theorem switch_back : laidBack G.first.layout l a.message rp.1 rp.2 = some (a, i, c) := by
  obtain ⟨R', P', hf⟩ := fits_of_msgFits hfit ha
  exact (laidBack_iff G.first.layout l a.message R' P' hf a i c rp.1 rp.2).2 ⟨ha, hrp⟩

include t1 hz hi

/-- There the switches' own data lays an entry. -/
theorem switch_lays : (switchData S₀ Z G).lays x rp.1 rp.2 = true :=
  lays_of_back G.first.codes G.first.shape G.first.layout (switchSeat Z G) (fun _ => 0)
    (K1.cellsVals S₀) t1 hfit (switch_back G hfit ha hrp) hz hi

/-- **And the entry is the packing of the reader's cells.** -/
theorem switch_val (R : Readers) (hd : List Fmt.Drawn) {mu : ℕ}
    (hmu : K1.labelNo a.name = some mu) :
    (switchData S₀ Z G).at_ R hd x rp.1 rp.2 =
      some (.inl (packedCells S₀ R.cells.cell l mu i c)) := by
  show (if (switchData S₀ Z G).lays x rp.1 rp.2 then
    some ((switchData S₀ Z G).entry R (hd.take ((switchData S₀ Z G).heardAt x)) x rp.1 rp.2)
    else none) = _
  rw [if_pos (switch_lays S₀ Z G t1 hfit ha hrp hz hi)]
  refine congrArg some ((entry_of_back G.first.codes G.first.shape G.first.layout (switchSeat Z G)
    (fun _ => 0) (K1.cellsVals S₀) R _ t1 (switch_back G hfit ha hrp)).trans ?_)
  show (match K1.labelNo a.name with
    | some mu => (.inl (packedCells S₀ R.cells.cell l mu i c) : Cb.Gl.F ⊕ Cb.Gl.E)
    | none => .inl (OnBytes.Slice.toF 0)) = _
  rw [hmu]

end

/-- **The own data that the part is handed there**, at the switches' data joined to another lot's:
that element, as the frame reads an entry over the base field. -/
theorem senderOwn_val {Xi : Type} (S₀ : Sz) (D' : Pub → Ground → RowDataOf Xi) (Z : Pub)
    (G : Ground) (ξ : Xi) (R : Readers) (p : SwitchPlace) {m l : ℕ} {a : ReqArray}
    (t1 : switchSeat Z G (p.ownAddr m) = some (l, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout l a.message = true)
    (ha : a ∈ (G.first.layout.link.getD l []).filter fun y => y.message == a.message) {i c : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {z : ℕ × ℕ}
    (hz : (K1.cellsVals S₀).size l a.name = some z) (hi : i < z.1 ∧ c < z.2) {mu : ℕ}
    (hmu : K1.labelNo a.name = some mu) :
    senderOwn (withSwitchData S₀ D' Z G ξ) R p m rp.1 rp.2 =
      asE (some (.inl (packedCells S₀ R.cells.cell l mu i c))) := by
  show asRow _ ((withSwitchData S₀ D' Z G ξ).at_ R [] (p.ownAddr m) rp.1 rp.2) = _
  rw [with_own S₀ D' Z G ξ R [] (p.ownAddr m) rp.1 rp.2 (by rw [t1]; rfl),
    switch_val S₀ Z G t1 hfit ha hrp hz hi R [] hmu]
  rfl

/-! ## 2 The joined Script's witness -/

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts} {Xj X Cl Cells Tok : Type} {bs : List (Block S Cl)}
  {front : Nat} {arr : Nat → Nat → Nat} {seats : List (Nat × Nat)}
  {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {O : Others Bk (Local W₀ Rc Xi Tr)}

/-- **At a fit joined list that holds the switches' share, the witness's message holds the packing
of the reader's cells**, at the layout's place of an element of an array "M mu" in one of a
switch's own messages. -/
theorem msg_own_packed (ch : Nat) (Sd : Sender) (S₀ : Sz) (D' : Pub → Ground → RowDataOf Xi)
    (Z : Pub) (G : Ground) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (no fx : SwitchPlace → Nat) (num : SwitchPlace → Nat → Nat) (tree : SwitchPlace → Nat)
    (tenant : SwitchPlace → Nat → Nat) (places : List SwitchPlace)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))
    (F : JoinFit bs front arr seats wit own₀ jobs O)
    (hin : ShareIn (switchShare Bk ch Sd (withSwitchData S₀ D' Z G) readers closing no fx num tree
      tenant places rest) O)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) {p : SwitchPlace} (hp : p ∈ places)
    (hw : NoWord (switchSent p.sizes p.others)) {m : ℕ}
    (hn : 1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size)
    (h1 : firstSender p (1 + p.sizes.kept.length + m) = true) (k : Coins Bk)
    {cn : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some cn)
    (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid (withSwitchData S₀ D' Z G) readers closing p cn w (hd.take (fx p)) = .ok V)
    {l : ℕ} {a : ReqArray} {M : ReqMessage} {cd : OnBytes.Code}
    (t1 : switchSeat Z G (p.ownAddr m) = some (l, a.message))
    (t2 : (G.first.shape.link.getD l default).messages[a.message]? = some M)
    (t3 : ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape =
      M.shape)
    (t4 : p.sizes.codes = G.first.codes) (t5 : G.first.codes.base[M.shape.code]? = some cd)
    (t6 : OnBytes.powerOfTwo cd.ell = true)
    (hfit : msgFits G.first.codes G.first.shape G.first.layout l a.message = true)
    (ha : a ∈ (G.first.layout.link.getD l []).filter fun y => y.message == a.message) {i c : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {mu : ℕ} (hmu : K1.labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (K1.cellsVals S₀).size l a.name = some z) (hi : i < z.1 ∧ c < z.2) :
    ((joinQ bs front cells tok arr wit own₀ jobs O).wit k w hd).msg
        (num p (1 + p.sizes.kept.length + m)) false rp.1 rp.2 =
      algebraMap Cb.Gl.F Cb.Gl.E (packedCells S₀ (readers w).cells.cell l mu i c) := by
  obtain ⟨b1, b2, b3, b4⟩ := lays_clear G.first.codes G.first.shape G.first.layout
    (switchSeat Z G) (fun _ => 0) (K1.cellsVals S₀) (p.ownAddr m) rp.1 rp.2 l a.message M cd
    (switch_lays S₀ Z G t1 hfit ha hrp hz hi) t1 t2 t5 t6
  have ec : p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default = cd := by
    rw [t3, t4, Array.getD_eq_getD_getElem?, t5, Option.getD_some]
  have hs := senderOwn_val S₀ D' Z G w.x (readers w) p t1 hfit ha hrp hz hi hmu
  have hO := share_msgs_fit ch Sd (withSwitchData S₀ D' Z G) readers closing no fx num tree tenant
    places rest F hin cells tok Vd 0 hp hn h1 k w hd hv (Nat.zero_le _) false rp.1 rp.2
  cases h3 : ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3 with
  | true =>
    have e := msgTxt_main_e ch (withSwitchData S₀ D' Z G) readers closing p k w (hd.take (fx p)) hH
      hV hw hn h3 (by rw [t3]; exact b1) (by rw [ec]; exact b2) (by rw [t3]; exact b4)
      (by rw [ec, t3]; exact b3)
    exact (hO _ e).trans (hs.trans (K1.asE_inl _))
  | false =>
    have e := msgTxt_main_f ch (withSwitchData S₀ D' Z G) readers closing p k w (hd.take (fx p)) hH
      hV hw hn h3 (by rw [t3]; exact b1) (by rw [ec]; exact b2) (by rw [t3]; exact b4)
      (by rw [ec, t3]; exact b3)
    refine (hO _ e).trans ?_
    rw [hs]
    show algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (OnBytes.Slice.ofF _)) = _
    rw [OnBytes.Slice.toF_ofF]

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.switch_back
#print axioms ProofFile.Honest.K2.Law.switch_lays
#print axioms ProofFile.Honest.K2.Law.switch_val
#print axioms ProofFile.Honest.K2.Law.senderOwn_val
#print axioms ProofFile.Honest.K2.Law.msg_own_packed
