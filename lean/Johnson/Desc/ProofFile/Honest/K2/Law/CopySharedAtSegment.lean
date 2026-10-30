-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopySharedAtSegment.lean: the kind "the code switch" (K2):
WHERE A SWITCH's CLOSING LAYS A SEGMENT ANEW (`segmentGroupRows`, Honest/K2/Closing.lean) OF THE
STRETCHES THAT IT CARRIES, THE ROWS OF A MESSAGE WHOSE SENDER IS A PART OF THE KIND K1 ARE THE ROWS
THAT THAT PART LAID (`K1.rowsR`, Honest/K1/Coins.lean) OF ITS OWN COINS: the sister of
`copy_at_segment` and `copyMask_at_segment` (Honest/K2/Law/CopyAtSegment.lean,
CopyMaskAtSegment.lean), which speak of a switch's own sending in this kind's own terms. Statements
with their proofs: joins; no definition.

  `copyShared_at_first`   a message of the segment's first sending, in front of the fold's mask
  `copyShared_at_mask`    the fold's mask
  `copyShared_at_later`   a message of a later sending

THE PREMISES OF EACH, BY KIND. RETURNS: the switch is handed its stretches; `segmentGroupRows` returns R
at these; the sender's own coins are there (`K1.lentCut`). THE BOOK's TIE, at the entry number i of
what p carries, i the stretch's number (a letter with its equation): owner, start and count are the
sender's address and the message's run in the sender's plan (`K1.startR`, `K1.dueMsg`). PUBLIC TIES
OF THE SENDER's PLAN P TO THE SEGMENT: one codes; message q' of P has the segment's message's shape;
that shape fits; it has no main row or is sampled; what rides at q' in P is what the closing takes
for the fold. ON THE DATA: the sender's data at q' are the closing's, as the shared sending takes
them (`asShared`).

By: `copyShared_carried` (Honest/K2/Law/CopyShared.lean) · `segmentRows_row`, `segmentRows_mask`
(Honest/K2/Law/RowsOfSegment.lean) · `segmentRows_later` (Honest/K2/Law/RowsOfLater.lean).

Limits. None of the premises is paid here. P, ride, o and q' are letters: that a plan of the kind
K1's lot stands at the address, and which of its messages the segment's message is, is not said. P
IS ANY `K1.Par`: `copyShared_at_first` is general in what lies in front: where a segment lies in
front the first sending is a switch's, and that sending is such a P too (`sendingPar`,
Honest/K2/Sending.lean): there the public ties are laws of Honest/K2/Law/Counts.lean and
`rowsAll_shared_paid` (Honest/K2/Law/SameRows.lean) turns `K1.rowsR` into the switch's own rows: so
the law is a second road to `copy_at_segment`: by reading the statements: no theorem here says it.
An equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyShared
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsOfLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts}

/-- A message of the first sending, in front of the fold's mask. n: its number there. -/
theorem copyShared_at_first (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    {S : SegmentPub} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {base : Nat} {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable S prev prevKept own (Stretch.carried p.carries c.2.2) base
      withFresh = .ok R) {n : Nat} (hn : n < (S.sent.headD #[]).size - 1)
    (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (o : Addr)
    {cs : Cs (K1.dueR P ride)} (ho : K1.lentCut k ch o (K1.dueR P ride) = some cs) {q' : Nat}
    (hq' : q' < P.sent.size) (hc : P.codes = S.sizes.codes)
    (hs : shapeAt P q' = ((S.sent.headD #[]).getD n default).shape)
    (H : ShapeFits P.codes (shapeAt P q') none)
    (hw : (shapeAt P q').mainRows = 0 ∨ (shapeAt P q').answers ≠ 0)
    (hride : ride q' = rideAs (shapeAt P q') none)
    (e : Ahead) {i : Nat} (hi : i = base + n)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ride q')
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P q') (ride q'))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK q' = asShared (shapeAt P q') (dataAtOf S prev own n)) :
    R.rows[n]? = some (K1.rowsR P ride dataK cs q') := by
  subst hi
  obtain ⟨r, hr, hg⟩ := segmentRows_row hR hn
  rw [← hc, ← hs] at hg
  rw [hr, copyShared_carried ch p k c h P ride o ho hq' H hw hride _ e he t1 t2 t3 hg dataK hdat]

/-- The fold's mask. -/
theorem copyShared_at_mask (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    {S : SegmentPub} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {base : Nat} {R : GroupRows}
    (hR : segmentGroupRows freshTable S prev prevKept own (Stretch.carried p.carries c.2.2) base
      true = .ok R)
    (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (o : Addr)
    {cs : Cs (K1.dueR P ride)} (ho : K1.lentCut k ch o (K1.dueR P ride) = some cs) {q' : Nat}
    (hq' : q' < P.sent.size) (hc : P.codes = S.sizes.codes)
    (hs : shapeAt P q' = ((S.sent.headD #[]).getD ((S.sent.headD #[]).size - 1) default).shape)
    (H : ShapeFits P.codes (shapeAt P q') (some S.foldVars))
    (hw : (shapeAt P q').mainRows = 0 ∨ (shapeAt P q').answers ≠ 0)
    (hride : ride q' = rideAs (shapeAt P q') (some S.foldVars))
    (e : Ahead) {i : Nat} (hi : i = base + ((S.sent.headD #[]).size - 1))
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ride q')
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P q') (ride q'))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK q' = asShared (shapeAt P q') fun _ _ => zeroG) :
    R.fresh = some (K1.rowsR P ride dataK cs q') := by
  subst hi
  obtain ⟨r, hr, hg⟩ := segmentRows_mask hR
  rw [← hc, ← hs] at hg
  rw [hr, copyShared_carried ch p k c h P ride o ho hq' H hw hride _ e he t1 t2 t3 hg dataK hdat]

/-- A message of a later sending. q: its number among the messages behind the first sending. -/
theorem copyShared_at_later (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    {S : SegmentPub} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {base : Nat} {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable S prev prevKept own (Stretch.carried p.carries c.2.2) base
      withFresh = .ok R) {q : Nat} {x : OnBytes.OracleNotice}
    (hx : ((S.sent.drop 1).flatMap (·.toList))[q]? = some x)
    (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (o : Addr)
    {cs : Cs (K1.dueR P ride)} (ho : K1.lentCut k ch o (K1.dueR P ride) = some cs) {q' : Nat}
    (hq' : q' < P.sent.size) (hc : P.codes = S.sizes.codes)
    (hs : shapeAt P q' = x.shape) (H : ShapeFits P.codes (shapeAt P q') none)
    (hw : (shapeAt P q').mainRows = 0 ∨ (shapeAt P q').answers ≠ 0)
    (hride : ride q' = rideAs (shapeAt P q') none)
    (e : Ahead) {i : Nat}
    (hi : i = base + ((S.sent.headD #[]).size - 1) + (if withFresh then 1 else 0) + q)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ride q')
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P q') (ride q'))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK q' = asShared (shapeAt P q') (own ((S.sent.headD #[]).size - 1 -
      (if prev.isSome then 1 + S.sizes.kept.length else 0) + q))) :
    R.rows[(S.sent.headD #[]).size - 1 + q]? = some (K1.rowsR P ride dataK cs q') := by
  subst hi
  obtain ⟨r, hr, hg⟩ := segmentRows_later hR hx
  rw [← hc, ← hs] at hg
  rw [hr, copyShared_carried ch p k c h P ride o ho hq' H hw hride _ e he t1 t2 t3 hg dataK hdat]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copyShared_at_first
#print axioms ProofFile.Honest.K2.Law.copyShared_at_mask
#print axioms ProofFile.Honest.K2.Law.copyShared_at_later
