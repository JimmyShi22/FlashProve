-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LedgerOffPad.lean: CONDITIONAL. One statement with its proof; no definition.

What is here. AN ENTRY THAT A MESSAGE's LEDGER HANDS OUT IS NO PLACE AT WHICH THE LIBRARY's TEST FOR
A PAD's PLACE ANSWERS YES. A sampled oracle message with mask rows has a ledger, which hands out the
free entries of its mask table one by one (`takeEntry`, Johnson/Desc/First/Pend/Row.lean). Where the
ledger is that of k takes since it was made (the library's `LedgerAt`,
Johnson/Desc/K13/Law/LedgerWithin.lean), the entry that is taken next is the one in mask row k % m
at place k / m, m the number of mask rows, and the library's test for a pad's place (`padB`,
Johnson/Desc/SeatAt.lean: the last place of the last mask row) answers false there. So the one
accessor of a witness's table (`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean) reads the message there
and not the pad. The two laws that bear it are the library's `takeEntry_free`
(Johnson/Desc/K13/Law/LedgerNo.lean) and `freeAt_ne_pad` (Fmt/PlacesLaws.lean).

  `takeEntry_off_pad`   **the entry's row and place; it is no place of the pad**

Limits. `LedgerAt` IS A HYPOTHESIS: that the ledger of a verifier's state is that of some number of
takes since it was made is shown here of no state. The library draws it from a public test of the
table of joints ("K13.pileWithin": `ledgersFit_of_C`, Johnson/Road/K4/K04Within.lean); THAT THE
HONEST SIDE's THREAD HANDS THAT TEST's YES AT THE STATE BEHIND A STEP IS NOT TRACED HERE; AND THAT
YES IS NOT ALL THAT LIES BETWEEN THIS STATEMENT AND A TIE ON THE WITNESS's MASK ENTRY UNDER THE
ENTRY TAKEN (`K4IndexTieAt`, Johnson/Desc/ProofFile/Honest/K4/Law/WoTies.lean): the test gives some
number k of takes, not which; the reader of the pile of pending rows answers 0 from the mask table's
size on (`maskCut`, Johnson/Desc/K13/Law/ReaderByBook.lean) and reads a table of zeros where the
message has no seat in the book (`tabAt`, Johnson/Desc/Sound/TabAt.lean): that the entry lies inside
and the message is seated is not shown here; nor how the entry's number becomes a row and a place in
that reader. Nothing on what the message holds at the entry. `padB` speaks of one answer; with more
answers the statement holds of the last place of the last mask row and says nothing of the pad's
other places.

Kin. THE SECOND HALF IS THE LIBRARY's `free_off_pad` (Johnson/Desc/K13/Honest/TakenList.lean, of
other writers) at the state's codes, the message's shape and k: that law asks an answer and that k
lie below the count of free entries, which `LedgerAt` and a take that returns give. It is not
called: the proof here goes by `freeAt_ne_pad`. The first half is `takeEntry_free`'s end with
`freeAt` written out as k % m and k / m. That file's head names further kin on the pad. Sought: by
statement, among the library's theorems: no hit; by the name `padB`, in part: not every file that
names it was read.

No property is claimed.
-/
import Johnson.Desc.K13.Law.LedgerNo
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Fmt.Places (entryNo freeAt freeCount padEntry freeAt_ne_pad pad_first)
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K13.Law (LedgerAt takeEntry_free takeEntry_is free_is)

/-- **THE ENTRY THAT IS TAKEN: ITS ROW AND PLACE; IT IS NO PLACE OF THE PAD.** CONDITIONAL: on every
hypothesis named. -/
theorem takeEntry_off_pad {st : Statement} {o k c : ℕ} {x : Oracle} {l l' : Ledger}
    (h : LedgerAt st o k) (hx : st.oracles[o]? = some x) (hl : x.ledger = some l)
    (ht : takeEntry l = some (c, l')) :
    c = entryNo x.shape.maskRows (k % x.shape.maskRows) (k / x.shape.maskRows) ∧
      padB st.codes x.shape true (k % x.shape.maskRows) (k / x.shape.maskRows) = false := by
  refine ⟨takeEntry_free h hx hl ht, ?_⟩
  obtain ⟨x₀, l₀, hx₀, hl₀, hm, ha, _, _, hleft, _⟩ := h
  obtain rfl := Option.some.inj (hx₀.symm.trans hx)
  obtain rfl := Option.some.inj (hl₀.symm.trans hl)
  have h0 := (takeEntry_is ht).1
  rw [free_is] at hleft
  unfold padB
  rw [if_pos rfl]
  generalize (st.codes.mask.getD x₀.shape.maskCode default).ell = e at hleft ⊢
  have hk : k < freeCount x₀.shape.maskRows e x₀.shape.answers := by omega
  have hs : x₀.shape.answers ≤ e := by
    by_contra hn
    unfold freeCount at hk
    rw [if_pos (Or.inr (by omega))] at hk
    exact absurd hk (Nat.not_lt_zero _)
  have hne := freeAt_ne_pad (i := x₀.shape.answers - 1) 0 hm hs hk
  rw [(pad_first 0 e x₀.shape.answers hm).1] at hne
  have hpe : padEntry e x₀.shape.answers 1 (x₀.shape.answers - 1) 0 = e - 1 := by
    unfold padEntry
    omega
  rw [hpe] at hne
  refine Bool.eq_false_iff.mpr fun hp => hne ?_
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
  show (k % x₀.shape.maskRows, k / x₀.shape.maskRows) = (x₀.shape.maskRows - 1, e - 1)
  exact Prod.ext (by show k % x₀.shape.maskRows = x₀.shape.maskRows - 1; omega)
    (by show k / x₀.shape.maskRows = e - 1; omega)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.takeEntry_off_pad
