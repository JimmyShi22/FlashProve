-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexEntryAt.lean: CONDITIONAL. One statement with its
proof.

What is here. THE MASK ENTRY THAT THE READER OF THE PILE OF PENDING ROWS READS, THROUGH A STATE OF
THE VERIFIER's, AT THE INDEX MASKS' MESSAGE AND THE ENTRY THAT ITS LEDGER HANDS OUT NEXT, IS ONE
ENTRY OF ONE MESSAGE OF THE WITNESS, AT A NUMBER, A ROW AND A PLACE THAT NAME NO STATE. The library
proves both halves for a state inside the table's promise, where the promise asks the public items
that are spent (`Rec.nextEntryIs`, Johnson/Road/K4/Rec/NextEntry.lean; `Rec.maskEntryIs`,
Johnson/Road/K4/Rec/MaskEntry.lean); at the composed meaning's own list of extra public tests the
promise does not ask all of them behind the member (the library's two negative tests,
`k4_openNext_small` and `k4_openMask_small`, Johnson/Road/K4/Rec/OpenNextWide.lean, at the border
behind K4's sub-protocol; what the two tests say at the border in front of it is not settled here),
so these two cannot be called there at the honest side's thread. Here the same argument is run from
the facts on the state themselves, named one by one; no promise and no meaning is named. That the
ledger is that of just so many takes is `ledgerAt_of_room` (Law/W/IndexLedgerAt.lean), after the
proof text of `nextEntryIs`.

  `index_entry_at`   **the entry's number; and the reader's mask entry there is the witness's
      message's entry.**

The hypotheses, all. On the state s: hi (its number of the index masks' message is im), h₁ (the
messages' shapes are the listed ones), h₂ (the book is in order, from tree 0), h₃ (the book's
places are the listed seats), hs (as many places as messages), hb (the listed seats name trees that
the book has), hc (the codes), hW (every ledger is that of some number of takes since it was made),
hR (the test of the public item "pile.room": what is left in the index masks' ledger is free0 less
the segments in front of m that leave a row). On public data: hsh, hq (the listed shape and seat at
im), hf (free0 is the count of free entries at that shape). hl, ht: the ledger hands out c. WHAT
GIVES «OFF THE PAD»: the library's core ends in the witness's table (`Wit.tab`), which reads the
pad at the pad's place and the message elsewhere; that the entry taken is no place of the pad is
`takeEntry_off_pad`, from hW's word on this ledger and from ht. THAT FEWER ENTRIES ARE TAKEN THAN
THE LEDGER HAD FREE WHEN IT WAS MADE IS NO HYPOTHESIS: a ledger that hands out an entry has one
left (`takeEntry_is`, from ht), and hR says how many are left.

Called, one call each. Of the library: `mask_entry_at` (the core of `maskEntryIs`;
Johnson/Road/K4/Rec/MaskEntry.lean) · `left_of_room` (Johnson/Road/K4/Rec/NextEntry.lean) ·
`takeEntry_no` (Johnson/Desc/K13/Law/LedgerNo.lean) · `takeEntry_is`
(Johnson/Desc/K13/Law/LedgerWithin.lean) · `shape_is` (Johnson/Desc/First/RecordPlan.lean). Handed
in with this file: `ledgerAt_of_room` (Law/W/IndexLedgerAt.lean) · `takeEntry_off_pad`
(Johnson/Road/K4/C/LedgerOffPad.lean).

Kin. `Rec.nextEntryIs` and `Rec.maskEntryIs`, named above: the same two ends inside the table's
promise; here from the facts on the state. `reader_mask_script` (Honest/K13/ReaderMaskScript.lean,
of other writers) makes the same join of `mask_entry_at` with «off the pad» at every number of
takes below the count of free entries, at a script's witness, with «a mask row», «an answer» and
«below the count» as hypotheses; here these three are drawn from hW, hR and ht, the number is the
one that "pile.room" tells, and the witness is any.

Not shown here. THAT ANY STATE MEETS THE NINE: Law/W/IndexFactsThr.lean and Law/W/IndexOfOwn.lean
have them where a thread of the first chain stands (these two files are no part of the library
yet). Where the ledger hands out nothing the statement is empty. Nothing on what the entry holds.
HOW LIGHT: following import lines, and stopping unopened at every module under Johnson/Goal/,
Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its
imports reach none of these. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexLedgerAt
import Johnson.Road.K4.Rec.MaskEntry
import Johnson.Road.K4.C.LedgerOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Road.K4.Rec (left_of_room mask_entry_at)
open OnBytes.Road.K4.C (takeEntry_off_pad)
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.RecordPlan (shape_is)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB)
open VerifiableInference.Desc.K13.Law (rwBook LedgersFit LedgerAt takeEntry_no takeEntry_is)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.Walk.Tied (roomIsB rowsBefore)

/-- CONDITIONAL: on every hypothesis named. **THE ENTRY THAT THE INDEX MASKS' LEDGER HANDS OUT NEXT
HAS A NUMBER THAT NAMES NO STATE; AND THE READER's MASK ENTRY THERE IS ONE ENTRY OF THE WITNESS's
MESSAGE.** t := rowsBefore fvs m: the segments in front of m that leave a row. -/
theorem index_entry_at {Pp Cells Tok : Type} {nR kC : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape) (L : Laid) (z : Pp)
    (s : S) (w : VerifiableInference.Desc.Wit Cells Tok MsgT) {cs : Codes} {free0 : ℕ}
    {fvs : List Bool} {m im : ℕ} {sh : OracleShape} {q : ℕ × ℕ}
    (hi : s.out.indexMasks = im) (h₁ : msgShapesB M s.st = true)
    (h₂ : bookInOrderB 0 s.book s.roots = true) (h₃ : seatsCarriedB L s.book = true)
    (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true) (hc : s.st.codes = cs)
    (hW : LedgersFit s.st) (hR : roomIsB free0 fvs m s = true) (hsh : M[im]? = some sh)
    (hq : L.places[im]? = some q)
    (hf : free0 =
      Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers)
    {l l' : Ledger} {c : ℕ} (hl : ledgerAt s = some l)
    (ht : takeEntry l = some (c, l')) :
    c = takenNo sh.maskRows (rowsBefore fvs m) ∧
      (rwBook arr mat (z, s) w).mask ⟨im, c⟩ =
        w.msg (arr q.1 q.2) true (rowsBefore fvs m % sh.maskRows)
          (rowsBefore fvs m / sh.maskRows) := by
  have hl0 := hl
  unfold ledgerAt at hl
  rw [hi] at hl
  obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨ho, _⟩ := Array.getElem?_eq_some_iff.1 hx
  have hxs : x.shape = sh := by
    have e := shape_is h₁ rfl im
    rw [hx, List.getElem?_take_of_lt ho, hsh] at e
    exact Option.some.inj e
  have hleft : l.left = free0 - rowsBefore fvs m := left_of_room hR hl0
  have h0 := (takeEntry_is ht).1
  have hk : LedgerAt s.st im (rowsBefore fvs m) :=
    ledgerAt_of_room hi h₁ hc hW hR hsh hf (by omega)
  obtain ⟨x₀, l₀, hx₀, hl₀, hm, ha, _, _, hsum, _⟩ := id hk
  obtain rfl : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hxl)
  rw [hxs, hc, ← hf] at hsum
  have hno := takeEntry_no hk hx hxl ht
  obtain ⟨_, hpad⟩ := takeEntry_off_pad hk hx hxl ht
  rw [hxs] at hno hpad hm ha
  refine ⟨hno, ?_⟩
  rw [hno, mask_entry_at arr mat M L z s w im _ sh q h₁ h₂ h₃ hs hb ho hsh hq hm ha
    (by rw [hc, ← hf]; omega)]
  show (if padB s.st.codes sh true _ _ = true then w.pad q.1 q.2 true _ _
    else w.msg (arr q.1 q.2) true _ _) = _
  rw [hpad]
  rfl

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.index_entry_at
