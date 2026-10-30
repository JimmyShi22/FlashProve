-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05AddrTieAt.lean: kind K5: THE LAST ASSEMBLY: AddrTie
(Johnson/Desc/First/Att/K05DataMats.lean: the law's reading of its tuple of messages, by address, is
the table of joints' data's) AT THE WITNESS OF THE RULE OF COMPOSITION: the tuple is msgsOf … w, the
data are dataQ at seatTab … w. NO PREMISE ON THE WITNESS w IS LEFT.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. No premise is evaluated at a plan or a record. D : Sent (the
codes, the request's shape, the layout, the links' lists of arrays) IS BUILT NOWHERE in this
library: the four equations below say that it is the live request's own plan.

ALL PREMISES of `addrTie_at`, BY SORT, each with who pays it, or NOBODY.
  PUBLIC (of D, x, tl and the table's list of members):
    hR : SymsOK x tl D rad (Johnson/Desc/First/Att/K05AddrTieOf.lean: what is spent of the guards of
    the
      caller's reading: a kept message has the shape of the message whose rows it took; every symbol
      address has a seat that lies in its table): paid from public tests with code in
      Johnson/Desc/First/Att/K05SymsOf.lean; these have not been run.
    hmk : masksUpTo D x hi = true (Johnson/Desc/First/Att/K05MasksAtt.lean: "evaluated in no file of
    this
      library"): it has not been run.
    hk : as many kept messages as entries of the group's list "born": NOBODY.
    hone : the message that holds the mask row has one mask row: the description's test on a link's
      first message asks it (messageHeld, Johnson/Desc/Ok/Links.lean); not joined here.
    hm : MemAt (Johnson/Desc/First/Att/K05MsgTieAt.lean) at the members in which a read address has
    its
      seat: a fact on the table's list of members: NOBODY.
    hcov, hcovM : the two lists of pairs ps and qs name, with its seat and its shape, every member
    in
      which a read address has its seat, and the member that holds the mask row: of whoever lays ps
      and qs: NOBODY yet.
  THREE BOOLS ON THE RECORD s (Johnson/Desc/First/Att/K05DoorB.lean): hB1 : liveReqB · hB2 :
  seatsOnB at ps
    · hB3 : shapesOnB at qs: AT THE MEMBERS THAT ARE NAMED, AND AT NO OTHER (at empty lists they say
    yes for nothing: hcov is what gives them weight); offered to the table's door; run nowhere.
  FOUR EQUATIONS ON THE RECORD: hlink : L.link = x.link (the promise's shapeAt) · hshape, hlay : the
    open link's own copy of the live request has D's shape and layout (the item "frame.liveIs" with
    two equations that whoever fills inOrder owes) · harr : L.arrayOf is D's at the link
    (linkFresh's second half).
  hok : LaidOkAt (Johnson/Desc/First/Att/K05AddrTieOf.lean): the symbol arrays that are read are
  laid
    lawfully at the statement's numbers of bits: paid in Johnson/Desc/First/Att/K05LayoutOk.lean
    from the programs' reqLayoutOk, hR, hB1, hB3 and "the statement's codes are D's".
  hpt, hL : the record's part and its open link.
  hslots : every slot that a form of fs names lies below hi: the forms' own bound: not joined here.
Main names: `seg_parts` (what segAt? lays into the part) · `fits_read` (every seat of a read address
lies in its table) · `addrTie_at`.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieAt
import Johnson.Desc.First.Att.K05DoorLaws
import Johnson.Desc.First.Att.K05MasksAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (Mem seatTab msgsOf MsgT dataQ)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt bornAt)

/-- What segAt? lays into the part. -/
theorem seg_parts {s : First.S} {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx}
    (hpt : segAt? s = some pt) (hL : s.link? = some L) :
    pt.L = L ∧ pt.d.st = s.st ∧ pt.d.book = s.book := by
  unfold segAt? at hpt
  rw [hL] at hpt
  cases hF : s.fork? with
  | none =>
    rw [hF] at hpt
    cases hpt
  | some F =>
    cases ht : s.tl? with
    | none =>
      rw [hF, ht] at hpt
      cases hpt
    | some tl =>
      rw [hF, ht] at hpt
      obtain rfl := Option.some.inj hpt
      exact ⟨rfl, rfl, rfl⟩

/-- Every seat of a read address lies in its table. -/
theorem fits_read {x : VerifiableInference.Desc.First.Look.Place}
    {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} {hi : ℕ} {fs : List Aff}
    (hR : SymsOK x tl D rad) (hmk : masksUpTo D x hi = true)
    (hslots : ∀ f ∈ fs, ∀ y ∈ f.slots.toList, y.1 < hi) {a : Addr}
    {z : VerifiableInference.Desc.First.Look.Seat} (ha : ReadAddr tl fs a)
    (hz : seatCalls D x.link a = some z) : z.Fits D.codes (sigListCalls D rad x.link) := by
  rcases ha with ⟨μ, i', c, rfl⟩ | ⟨f, hf, y, hy, rfl⟩
  · obtain ⟨z', e, h⟩ := hR.seated μ i' c
    obtain rfl : z' = z := Option.some.inj (e.symm.trans hz)
    exact h
  · obtain ⟨z', e, h⟩ := masks_seated hmk rad _ ⟨y.1, hslots f hf y hy, rfl⟩
    obtain rfl : z' = z := Option.some.inj (e.symm.trans hz)
    exact h

section
variable {Cells Tok : Type}

/-- **AddrTie at the witness: no premise on the witness is left.** -/
theorem addrTie_at (x : VerifiableInference.Desc.First.Look.Place)
    (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (w : Wit Cells Tok MsgT) (fs : List Aff) (hi : ℕ) (ps : List (ℕ × (ℕ × ℕ)))
    (qs : List (ℕ × OracleShape)) {s : First.S}
    {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx}
    (hR : SymsOK x tl D rad) (hmk : masksUpTo D x hi = true)
    (hk : (keptAt D x.link).length = (bornAt D x.link).size)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ k : Fin (sigListCalls D rad x.link).length, ReadMsg (ReadAddr tl fs) D x.link k.val →
      MemAt ms (sigListCalls D rad x.link) seat k)
    (hB1 : liveReqB (bornAt D x.link) s = true)
    (hcov : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hB2 : seatsOnB (keptAt D x.link).length ps own s = true)
    (hB3 : shapesOnB (keptAt D x.link).length qs s = true)
    (hlink : L.link = x.link) (hshape : L.check.frame.shape = D.shape)
    (hlay : L.check.rows.layout = D.layout) (harr : L.arrayOf = D.arrayOf.getD x.link #[])
    (hok : LaidOkAt x tl D L.check.frame s.st)
    (hpt : segAt? s = some pt) (hL : s.link? = some L)
    (hslots : ∀ f ∈ fs, ∀ y ∈ f.slots.toList, y.1 < hi) :
    AddrTie x tl D rad pt.L.arrayOf (msgsOf D.codes (sigListCalls D rad x.link) seat arr w)
      (dataQ own pt (seatTab D.codes arr ms w)) fs := by
  obtain ⟨e1, e2, e3⟩ := seg_parts hpt hL
  have hF : FrameIs D x.link L.check.frame := frameIs_of_B hB1 hL hlink hshape
  refine addrTie_of x tl D rad own pt _ _ fs (by rw [e1]; exact hF) hk (by rw [e1]; exact hlay)
    (by rw [e1]; exact harr) (by rw [e1, e2]; exact hok) (hS_of_seated hR) ?_ ?_
  · rw [e1, e2, e3]
    exact msgTie_at _ D rad x.link _ own _ _ arr seat ms w hm fun a z ha hz =>
      seatOk_on D.codes _ seat _ own ps qs hL hB2 hB3 z (fits_read hR hmk hslots ha hz)
        fun hk => hcov ⟨z.msg, hk⟩ ⟨a, z, ha, hz, rfl⟩
  · rw [e1, e2]
    intro o ho
    obtain ⟨_, k, hkk, hmm, _, _⟩ := masksUpTo_yes hmk rad
    obtain ⟨_, _, _, hw⟩ := maskOracle_mask hF (seat_mask hmm 0)
    rw [ho] at hw
    exact maskBits_on _ qs hL hB3 (hcovM k hkk hmm) hw.symm (hone k hkk hmm)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seg_parts
#print axioms VerifiableInference.Desc.First.Att.P.fits_read
#print axioms VerifiableInference.Desc.First.Att.P.addrTie_at
