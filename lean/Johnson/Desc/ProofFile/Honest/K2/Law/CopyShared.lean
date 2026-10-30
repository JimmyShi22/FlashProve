-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyShared.lean: the kind "the code switch" (K2): WHAT A SWITCH
LAYS ANEW OF A CARRIED RUN OF THE SHARED SENDING's IS WHAT THE SHARED SENDING LAID: the sister of
`copy_carried` (Honest/K2/Law/CopyOne.lean) for a message whose sender is not a switch but a part of
the kind K1: the rows that `messageRows` (Honest/K2/Sending.lean) makes of the carried stretch are
`K1.rowsR` (Honest/K1/Coins.lean) of the sender's own coins, at that message. Statements with their
proofs: joins; no definition.

  `own_cut_of_whole`     a cut of the whole that lies within the part's own coins is the same cut of
                         these: the converse of `cut_through` (CopyOne.lean), under the two bounds
  `copyShared_one`       ONE MESSAGE, no book: of a cut of the sender's own coins at the message's
                         start
  `copyShared_carried`   THE END: of the stretch number i that the switch p carries

ITS PREMISES, BY KIND. RETURNS: the switch is handed its stretches; the sender's own coins are there
(`K1.lentCut`); `messageRows` returns R. THE BOOK's TIE, at the entry number i of what p carries:
its owner is the sender's address; its start is `K1.startR` at the message; its count is `K1.dueMsg`
there. PUBLIC, ON THE MESSAGE: q is a message of the sending; its shape fits (`ShapeFits`,
Honest/K2/Law/Counts.lean); it has no main row or is sampled; what rides at it in the sender's plan
is what the switch's text takes for the fold. ON THE DATA: the sender's data at the message are the
switch's, as the shared sending takes them (`asShared`, Honest/K2/Law/SameRows.lean).

By: `laid_shared`, `rowsR_shared` (SameRows.lean) · `messageRows_laid` (Honest/K2/Law/Laid.lean) ·
`carried_of_handed` (Honest/K2/Law/CarriedOfLend.lean) · `cut_of_le` (Honest/K2/Law/Room.lean) · the
shared sending's `msg_in_e`, `msg_in_f` (Honest/K1/CoinsIn.lean, of other authors). Kin of
`own_cut_of_whole`: `cut_again` (Honest/K2/Law/Reads.lean) and the frame's `cut_some`
(Honest/Law/ReadyAny.lean) say whether a cut returns, not which.

Limits. None of the premises is paid here. One message: nothing on a segment whole; the join with
`segmentGroupRows` is not typed. P, ride and the sender's address are letters: that a plan of the kind
K1's lot stands at the address is not said. An equation at each run's coins: what is WRITTEN where:
no sentence on what an element is for. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyOne
import Johnson.Desc.ProofFile.Honest.K2.Law.SameRows
import Johnson.Desc.ProofFile.Honest.K2.Law.Room
import Johnson.Desc.ProofFile.Honest.K1.CoinsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open Johnson.Prover.Send (shapeAt)
open Reads

variable {Bk : ProverCoinCounts}

/-- The converse of `cut_through`, under the two bounds. -/
theorem own_cut_of_whole {d t : Due} (c : Cs d) {own : Cs t} (h0 : c.cut ⟨0, 0⟩ t = some own)
    {a n : Due} {c' : Cs n} (h : c.cut a n = some c') (hf : a.f + n.f ≤ t.f)
    (he : a.e + n.e ≤ t.e) : own.cut a n = some c' := by
  obtain ⟨c'', h''⟩ := cut_of_le own hf he
  have e := cut_through c h0 h''
  rw [h] at e
  rw [h'']
  exact e.symm

/-- **ONE MESSAGE**, no book. q: the message's number in the sender's sending. -/
theorem copyShared_one (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    {cs : Cs (K1.dueR P ride)} {q : Nat} {fold : Option Nat} {data : Nat → Nat → Cb.Gl.E}
    {N : Due} {c' : Cs N} (H : ShapeFits P.codes (shapeAt P q) fold)
    (hw : (shapeAt P q).mainRows = 0 ∨ (shapeAt P q).answers ≠ 0)
    (hride : ride q = rideAs (shapeAt P q) fold)
    (hcut : cs.cut (K1.startR P ride q) N = some c') {R : Johnson.Prover.Send.Rows}
    (hR : messageRows freshTable P.codes (shapeAt P q) fold data ⟨N, c'⟩ = .ok R)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK q = asShared (shapeAt P q) data) :
    R = K1.rowsR P ride dataK cs q := by
  obtain ⟨-, -, -, cF, cE, cM, cT, a1, a2, a3, a4, e⟩ := messageRows_laid hR
  rw [e, laid_shared (table := freshTable) (data := data) H hw (fun _ _ _ _ _ => rfl) hcut a1 a2
    a3 a4, rowsR_shared, hride, hdat]

/-- **THE END.** p: the switch that carries. o: the sender's address. -/
theorem copyShared_carried (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (o : Addr)
    {cs : Cs (K1.dueR P ride)} (ho : K1.lentCut k ch o (K1.dueR P ride) = some cs) {q : Nat}
    (hq : q < P.sent.size) {fold : Option Nat} {data : Nat → Nat → Cb.Gl.E}
    (H : ShapeFits P.codes (shapeAt P q) fold)
    (hw : (shapeAt P q).mainRows = 0 ∨ (shapeAt P q).answers ≠ 0)
    (hride : ride q = rideAs (shapeAt P q) fold) (i : Nat) (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ride q)
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P q) (ride q))
    {R : Johnson.Prover.Send.Rows}
    (hR : (Stretch.carried p.carries c.2.2 i).bind
      (messageRows freshTable P.codes (shapeAt P q) fold data) = .ok R)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK q = asShared (shapeAt P q) data) :
    R = K1.rowsR P ride dataK cs q := by
  rw [carried_of_handed ch p k c h i e he, t1, t2, t3] at hR
  obtain ⟨s, hs, hm⟩ := bind_ok' hR
  obtain ⟨c', hc', rfl⟩ := stretch_cut_ok hs
  unfold K1.lentCut at ho
  exact copyShared_one P ride H hw hride
    (own_cut_of_whole _ ho hc' (K1.msg_in_f P ride q hq) (K1.msg_in_e P ride q hq)) hm dataK hdat

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.own_cut_of_whole
#print axioms ProofFile.Honest.K2.Law.copyShared_one
#print axioms ProofFile.Honest.K2.Law.copyShared_carried
