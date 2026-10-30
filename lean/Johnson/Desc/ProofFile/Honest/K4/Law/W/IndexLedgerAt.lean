-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexLedgerAt.lean: CONDITIONAL. Two statements with their
proofs.

What is here. FROM «JUST n ENTRIES ARE LEFT IN THE INDEX MASKS' LEDGER» TO «THAT LEDGER IS THE
LEDGER OF t TAKES SINCE IT WAS MADE», t the count of free entries of a ledger as it is made less n.
The library's `LedgersFit` (Johnson/Desc/K13/Law/OwedLedgers.lean) says of every ledger in a
statement that it is that of SOME number of takes (`LedgerAt st o k`,
Johnson/Desc/K13/Law/LedgerWithin.lean); its test `leftIsB n s`
(Johnson/Top/H0/Walk/FrameEntriesDefs.lean) says how many entries are left. `LedgerAt` holds that
what is left and k make the count: so k is told. It is the arithmetic inside the proof of the
library's `Rec.nextEntryIs` (Johnson/Road/K4/Rec/NextEntry.lean), as a statement of its own;
`index_entry_at` (Law/W/IndexEntryAt.lean) calls it. It names no thread, no promise, no meaning, no
kind, no border and no call of `takeEntry`.

  `ledgerAt_of_left`   **LedgerAt s.st im t**, from the state's number of the message, the shapes,
      the codes, `LedgersFit`, `leftIsB n s` and n + t = free0.
  `ledgerAt_of_room`   the same at the test of the public item "pile.room": t := the segments in
      front of m that leave a row.

The hypotheses, all. On the state s: hi (its number of the index masks' message is im), h₁ (the
messages' shapes are the listed ones), hc (the codes), hW, hL | hR. On public data: hsh (the listed
shape at im), hf (free0 is the count of free entries at that shape), hn (n + t = free0) | hle (the
segments in front are at most free0: without it the test's subtraction would stop at 0 and tell
nothing).

Called, of the library: `shape_is` (Johnson/Desc/First/RecordPlan.lean).

Kin. Beside `Rec.nextEntryIs`, named above. NEAREST: `made_of_pile`
(Johnson/Top/H0/MergeLaw/FrontFacts.lean) goes from the test on the ledgers and `leftIsB n s` to
`LedgerAt` at SOME number of takes, not which; `takes_of_ledgerAt`
(Johnson/Top/H0/MergeLaw/FrontTests.lean) has that `LedgerAt` holds at no other number than the
count less what is left, read off the state's own shape and codes. Here the number is told from the
listed shape and the public codes. Neither is called. Other laws open `leftIsB` for other ends,
among them `leftIsB_iff` (Johnson/Top/H0/Walk/FrameEntries.lean: the test as a sentence),
`roomLeft_of` (Honest/Thread/RoomAtHead.lean: there is room for what is still to be taken),
`taken_of_leftIs` (Honest/K13/TakenAtM3.lean: a taking of at most n entries returns),
`roomFor_of_leftIs` (Johnson/Road/K4/Riders/MoreFront.lean) and `entry_within`
(Johnson/Top/H0/MergeLaw/EntryFront.lean). Sought by the name `leftIsB` under Johnson/Road/K4,
Johnson/Desc/ProofFile/Honest, Johnson/Top/H0, Johnson/Desc/K13 and Johnson/P5J; not beyond.

Not shown here. THAT ANY STATE MEETS THE FIVE: Law/W/IndexFactsThr.lean has them where a thread of
the first chain stands, at the public files' own data and any prover. (Law/W/IndexEntryAt.lean and
Law/W/IndexFactsThr.lean are no part of the library yet.) Nothing on which entries the later takes
hand out: the library has that take by take (`takeEntry_no`, Johnson/Desc/K13/Law/LedgerNo.lean;
`takeMaskP_within`, Johnson/Desc/K13/Law/LedgerWithin.lean). Nothing on what any entry holds. HOW
LIGHT: it stands over the library alone; following import lines, and stopping unopened at every
module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose
name begins Cb.Bridge, its imports reach none of these. Nothing on soundness, on completeness or on
any other property.

No property is claimed.
-/
import Johnson.Road.K4.Rec.NextEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.RecordPlan (shape_is)
open VerifiableInference.Desc.K12.Door (msgShapesB)
open VerifiableInference.Desc.K13.Law (LedgersFit LedgerAt)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.Walk.Tied (leftIsB roomIsB rowsBefore)

/-- CONDITIONAL: on every hypothesis named. **WHERE JUST n ENTRIES ARE LEFT, THE INDEX MASKS' LEDGER
IS THAT OF t TAKES SINCE IT WAS MADE**, n + t the count of free entries of a ledger as it is
made. -/
theorem ledgerAt_of_left {s : S} {M : List OracleShape} {cs : Codes} {free0 n t im : ℕ}
    {sh : OracleShape} (hi : s.out.indexMasks = im) (h₁ : msgShapesB M s.st = true)
    (hc : s.st.codes = cs) (hW : LedgersFit s.st) (hL : leftIsB n s = true)
    (hsh : M[im]? = some sh)
    (hf : free0 =
      Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers)
    (hn : n + t = free0) : LedgerAt s.st im t := by
  unfold leftIsB at hL
  cases hl : ledgerAt s with
  | none =>
    rw [hl] at hL
    simp at hL
  | some l =>
    rw [hl] at hL
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hL
    have hleft : l.left = n := hL.2
    unfold ledgerAt at hl
    rw [hi] at hl
    obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
    obtain ⟨ho, _⟩ := Array.getElem?_eq_some_iff.1 hx
    have hxs : x.shape = sh := by
      have e := shape_is h₁ rfl im
      rw [hx, List.getElem?_take_of_lt ho, hsh] at e
      exact Option.some.inj e
    obtain ⟨k, hk⟩ := hW im x hx (by rw [hxl]; rfl)
    obtain ⟨x₀, l₀, hx₀, hl₀, _, _, _, _, hsum, _⟩ := id hk
    obtain rfl : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
    obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hxl)
    rw [hxs, hc, ← hf] at hsum
    have hkk : k = t := by omega
    subst hkk
    exact hk

/-- CONDITIONAL: on every hypothesis named. The same at the test of the public item "pile.room". -/
theorem ledgerAt_of_room {s : S} {M : List OracleShape} {cs : Codes} {free0 : ℕ}
    {fvs : List Bool} {m im : ℕ} {sh : OracleShape} (hi : s.out.indexMasks = im)
    (h₁ : msgShapesB M s.st = true) (hc : s.st.codes = cs) (hW : LedgersFit s.st)
    (hR : roomIsB free0 fvs m s = true) (hsh : M[im]? = some sh)
    (hf : free0 =
      Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers)
    (hle : rowsBefore fvs m ≤ free0) : LedgerAt s.st im (rowsBefore fvs m) :=
  ledgerAt_of_left hi h₁ hc hW hR hsh hf (by omega)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.ledgerAt_of_left
#print axioms ProofFile.Honest.K4.W.ledgerAt_of_room
