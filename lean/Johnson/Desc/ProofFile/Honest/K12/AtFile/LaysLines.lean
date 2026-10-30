-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LaysLines.lean: the test on the book and a job (`laysB`,
K12/StepsReturn.lean) at the written term `bookShort`, at the two tests of the shared chain: first by
Lean's evaluator, then by the kernel; and `laysB_maker`, which carries it to the book that the maker
returns at the written description. It is the closed line under the depths
of a test's trees (`testTbl_depth`, K12/DepthsOfText.lean) and under the laying of its steps (`lays_of_B`).
It can say no.

  `seatOf`       a written place with a seat's place: a book speaks of seats, and the written places
                 bear other pieces
  `bookShort`    the book's rows and cuts, and of its entries those outside the first chain
  `all_short`, `any_short`   a test on the entries that says yes, or no, of each entry spent in the first
                 chain has one answer at the whole list and at the short one
  `laysB_short`  so `laysB` at a place outside the first chain is `laysB` at `bookShort`
  `laysB_maker`  the same at the book that the maker returns at `WP`: its rows, cuts and entries are these
  `jobAtU`, `jobAtO`   the bare jobs at the written places, the seats' places and the sendings' members
  `lays_U`, `lays_O`   the test says yes
  `lays_U_piece`, `lays_O_members`   controls: at the written place's own piece no; with the other
                 test's members no

Limits.
- `bookShort` is a written term, at the written description and sendings. That a filling's book is the
  maker's is not shown here.
- `jobAtU`, `jobAtO` are bare jobs at written places with a seat's place. A job at a seated place differs
  from them in fields that `laysB` does not read, and in `p` itself: that carry is not typed here.
- The test on the last chain is `laysLastB`: not here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Bare
import AtFullSide.K12.TiesAtLaid
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawAheadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.K1 (realSized)
open P2Law.ProofPlan (WP)
open H2K.Member (piUFull piOFull)
open ProofFile.Honest.K12 (TestJob laysB inB)
open ProofFile.Honest.K12.AtProof (placeU placeO bareJob membersU membersO freshU freshO)
open AtFullSide.K12 (wants_first seg_first ahead_at)
open AtFullSide.K14 (rawAheadW rawShortW rawRowsFirstW rawRowsSharedW rawRowsSecondW rawWantsW rawSegW)

/-- A written place with a seat's place. -/
def seatOf (p : P12) (pl : Place) : P12 := { p with place := pl }

/-- The book's rows and cuts, and of its entries those outside the first chain. -/
def bookShort : ProverCoinCounts :=
  { first := rawRowsFirstW, shared := rawRowsSharedW, second := rawRowsSecondW, ahead := rawShortW
    cuts := cutsOf WP }

/-- A test that says yes of each entry spent in the first chain. -/
theorem all_short (f : Ahead → Bool) (hf : ∀ e : Ahead, e.spender.place.chain = 1 → f e = true) :
    rawAheadW.all f = rawShortW.all f := by
  have hw : (rawWantsW.map (·.entry)).all f = true := List.all_eq_true.2 fun e he =>
    hf e (beq_iff_eq.1 (List.all_eq_true.1 wants_first e he))
  have hs : rawSegW.all f = true := List.all_eq_true.2 fun e he =>
    hf e (beq_iff_eq.1 (List.all_eq_true.1 seg_first e he))
  unfold rawAheadW rawShortW
  simp only [List.all_append, hw, hs, Bool.true_and, Bool.and_true, List.all_nil, Bool.and_assoc]

/-- A test that says no of each entry spent in the first chain. -/
theorem any_short (g : Ahead → Bool) (hg : ∀ e : Ahead, e.spender.place.chain = 1 → g e = false) :
    rawAheadW.any g = rawShortW.any g := by
  have hw : (rawWantsW.map (·.entry)).any g = false := List.any_eq_false.2 fun e he => by
    rw [hg e (beq_iff_eq.1 (List.all_eq_true.1 wants_first e he))]
    simp
  have hs : rawSegW.any g = false := List.any_eq_false.2 fun e he => by
    rw [hg e (beq_iff_eq.1 (List.all_eq_true.1 seg_first e he))]
    simp
  unfold rawAheadW rawShortW
  simp only [List.any_append, hw, hs, Bool.false_or, Bool.or_false, List.any_nil, Bool.or_assoc]

/-- **`laysB` at a place outside the first chain is `laysB` at `bookShort`**, at a book with these rows,
cuts and entries. -/
theorem laysB_short {W X : Type} {B : ProverCoinCounts} (ch : ℕ) (hr : B.rowsOf ch = bookShort.rowsOf ch)
    (hc : B.cuts = bookShort.cuts) (ha : B.ahead = rawAheadW) (J : TestJob W X)
    (hch : J.p.place.chain ≠ 1) : laysB B ch J = laysB bookShort ch J := by
  have off : ∀ e : Ahead, e.spender.place.chain = 1 → (e.spender.place == J.p.place) = false :=
    fun e he => beq_eq_false_iff_ne.2 fun h => hch (by rw [← h]; exact he)
  have e1 := any_short (fun e => e.spender.place == J.p.place && decide (2 ≤ e.spender.part))
    fun e he => by simp only [off e he, Bool.false_and]
  have e2 := all_short (fun e => !(e.spender.place == J.p.place) || inB (bookShort.rowsOf ch) e)
    fun e he => by simp only [off e he, Bool.not_false, Bool.true_or]
  have e3 := ahead_at ⟨J.p.place, 0⟩ hch
  have e4 := ahead_at ⟨J.p.place, 1⟩ hch
  unfold laysB AtPublicFiles.KeyBook.hasFor
  rw [hr, hc, ha, e1, e2, e3, e4]
  rfl

/-- **`laysB` at the book that the maker returns at the written description.** -/
theorem laysB_maker {W X : Type} {B : ProverCoinCounts}
    (hB : bookWhole WP Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (ch : ℕ)
    (J : TestJob W X) (hch : J.p.place.chain ≠ 1) : laysB B ch J = laysB bookShort ch J := by
  unfold bookWhole at hB
  obtain ⟨R, hR, hc⟩ := BookShared.ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨e1, e2, e3⟩ := AtFullSide.K14.rawBookRows_written _ R hR
  have hcuts : R.cuts = cutsOf WP := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'⟩ := bookRaw_rows hR
    exact hc'
  refine laysB_short ch ?_ hcuts (AtFullSide.K14.rawAhead_written R hR) J hch
  unfold ProverCoinCounts.rowsOf
  rw [e1, e2, e3]
  rfl

/-- The bare job at the test on G_u, at a plan: the written place, the seat's place, the sendings'
members. -/
def jobAtU (A : ProofFile.Honest.K14.SendPub) : TestJob Unit Unit :=
  bareJob (seatOf piUFull placeU) (membersU A) freshU

/-- The same at the test on G_omega. -/
def jobAtO (A : ProofFile.Honest.K14.SendPub) : TestJob Unit Unit :=
  bareJob (seatOf piOFull placeO) (membersO A) freshO

-- Foretold: yes at both. Controls: no.
#guard realSized.all fun q => laysB bookShort 1 (jobAtU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))
#guard realSized.all fun q => laysB bookShort 1 (jobAtO (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))
#guard realSized.all fun q =>
  !laysB bookShort 1 (bareJob piUFull (membersU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) freshU : TestJob Unit Unit)
#guard realSized.all fun q =>
  !laysB bookShort 1
    (bareJob (seatOf piOFull placeO) (membersU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) freshO : TestJob Unit Unit)

theorem lays_U : (realSized.all fun q => laysB bookShort 1 (jobAtU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))) = true := by
  decide +kernel

theorem lays_O : (realSized.all fun q => laysB bookShort 1 (jobAtO (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))) = true := by
  decide +kernel

/-- Control: at the written place's own piece the book has no cut. -/
theorem lays_U_piece : (realSized.all fun q => !laysB bookShort 1
    (bareJob piUFull (membersU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) freshU : TestJob Unit Unit)) = true := by
  decide +kernel

/-- Control: the other test's members. -/
theorem lays_O_members : (realSized.all fun q => !laysB bookShort 1
    (bareJob (seatOf piOFull placeO) (membersU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) freshO :
      TestJob Unit Unit)) = true := by
  decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.all_short
#print axioms ProofFile.Honest.K12.AtFile.any_short
#print axioms ProofFile.Honest.K12.AtFile.laysB_short
#print axioms ProofFile.Honest.K12.AtFile.laysB_maker
#print axioms ProofFile.Honest.K12.AtFile.lays_U
#print axioms ProofFile.Honest.K12.AtFile.lays_O
#print axioms ProofFile.Honest.K12.AtFile.lays_U_piece
#print axioms ProofFile.Honest.K12.AtFile.lays_O_members
