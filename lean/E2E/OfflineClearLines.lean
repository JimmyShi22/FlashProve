-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineClearLines.lean: the test on the book under `fresh` at the three senders of the first
chain that own coins, at the written book, the written numbers of each sending, the order of the
written places. Each line can say no.

  `writtenOrder`        the order of the places of the written lists
  `parIndexMasks`, `parMultiplicities`, `parMessageW`   each sending's numbers at the written sizes
  `index_fast_full`, `multiplicities_fast_full`, `messageW_fast_full`   THE THREE LINES OF THE KERNEL:
      the fast test `fastOkB` (Johnson/SendSim/At/FastBook.lean) says yes
  `owned_full`          the test of emptiness: of the written book's 1,975 entries 27, 1,930 and 4 are
      on the three senders' coins, and 25, 1,927 and 1 of these are spent, the others carried
      (the kernel)
  `fast_full_no`        controls: the fast test says no at the same book where a sender's table that
      is sent along, or its numbers, are another sender's (the kernel); controls that turn the order
      and the book: `key_fast_no` (AtFullSide/K1/KeyBookClear.lean) turns the book, none the order
  `atFull_of`           a test that follows from another follows at the written value
  `index_clear_full`, `multiplicities_clear_full`, `messageW_clear_full`   the exact test
      `bookClearAnyB` (Johnson/SendSim/At/WideTest.lean) says yes: by `clearAny_of_fast` and
      `bookClearAnyB_iff`, not by evaluation

Why the fast test. `bookClearAnyB` goes address by address and at each through all entries: no line
here evaluates it. `fastOkB` walks the book a fixed number of times, is sufficient and not necessary,
and asks more: that the spent runs rise in the book's order across all spenders, and that they keep
off the pads and all mask rows' tails of every message (FastBook.lean, Limits).

Limits. Public numbers only: no coin, no input, nothing played. One owner at a time: nothing on the
coins of two senders together. The numbers' fields gp, work and groups are stand-ins: the tests read
the codes and the notices alone (`clear_same`, E2E/OfflineFirstSends.lean). Nothing on any property.
-/
import E2E.KeyBookHeldK1Jobs
import E2E.KeyBookAtWritten
import E2E.KeyBookPassesNamed
import E2E.KeyPlaces
import Johnson.SendSim.At.WideTest
import Johnson.SendSim.At.FastBook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open OnBytes (linMessageW)
open OnBytes.SendSim.At (bookClearAnyB fastOkB clearAny_of_fast bookClearAnyB_iff)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyBook (KeyPub keyBook atFull fullPub fullFirst fullShared fullSecond idxPlace msgPlace wPlace
  rideMsg rideW)

/-- The order of the written places. -/
def writtenOrder : List Place := (fullFirst ++ fullShared ++ fullSecond).map (·.1)

/-- The numbers of the sending of the index masks at the written sizes. -/
def parIndexMasks : VerifiableInference.Desc.K1.Par :=
  { place := idxPlace, codes := keyFull.codes, gp := { samples := 1, firstTree := 0 }, work := 0
    parts := [("the index masks", #[keyFull.once.input])], groups := [] }

/-- The numbers of the sending of the multiplicities at the written sizes. -/
def parMultiplicities : VerifiableInference.Desc.K1.Par :=
  { place := msgPlace, codes := keyFull.codes, gp := { samples := 1, firstTree := 0 }, work := 0
    parts := [("the lookups' own message and what rides with it",
      OnBytes.Wf.messageOf keyFull.ranges.x)]
    groups := [] }

/-- The numbers of the sending of W at the written sizes. -/
def parMessageW : VerifiableInference.Desc.K1.Par :=
  { place := wPlace, codes := keyFull.codes, gp := { samples := 1, firstTree := 0 }, work := 0
    parts := [("W and what rides with it", (linMessageW keyFull.once.shape).getD #[])]
    groups := [] }

/-- **The fast test says yes at the sender of the index masks.** By evaluation. -/
theorem index_fast_full : atFull (fun K =>
    fastOkB parIndexMasks (fun _ => none) (keyBook K) writtenOrder ⟨idxPlace, 0⟩) = true := by
  decide +kernel

/-- **The fast test says yes at the sender of the multiplicities.** By evaluation. -/
theorem multiplicities_fast_full : atFull (fun K =>
    fastOkB parMultiplicities rideMsg (keyBook K) writtenOrder ⟨msgPlace, 0⟩) = true := by
  decide +kernel

/-- **The fast test says yes at the sender of W.** By evaluation. -/
theorem messageW_fast_full : atFull (fun K =>
    fastOkB parMessageW rideW (keyBook K) writtenOrder ⟨wPlace, 0⟩) = true := by
  decide +kernel

/-- How many entries of a book are on an owner's coins, and how many of these are spent. -/
def ownedCount (B : ProverCoinCounts) (o : Addr) : Nat × Nat :=
  ((B.ahead.filter fun e => e.owner == o).length,
    (B.ahead.filter fun e => e.owner == o && e.once).length)

/-- **THE TEST OF EMPTINESS: the three lines speak of entries that are there.** By evaluation. -/
theorem owned_full : fullPub.map (fun K => ((keyBook K).ahead.length,
    ownedCount (keyBook K) ⟨idxPlace, 0⟩, ownedCount (keyBook K) ⟨msgPlace, 0⟩,
    ownedCount (keyBook K) ⟨wPlace, 0⟩)) = some (1975, (27, 25), (1930, 1927), (4, 1)) := by
  decide +kernel

/-- **Controls: the fast test says no at the same book**: at the multiplicities' sender with W's table
sent along; at W's sender with the multiplicities' table; at each of the two with no table sent
along; at the index masks' address with W's numbers. By evaluation. A no of this test shows that it
can say no, not that `BookClearAny` fails. -/
theorem fast_full_no : fullPub.map (fun K =>
    [fastOkB parMultiplicities rideW (keyBook K) writtenOrder ⟨msgPlace, 0⟩,
      fastOkB parMessageW rideMsg (keyBook K) writtenOrder ⟨wPlace, 0⟩,
      fastOkB parMultiplicities (fun _ => none) (keyBook K) writtenOrder ⟨msgPlace, 0⟩,
      fastOkB parMessageW (fun _ => none) (keyBook K) writtenOrder ⟨wPlace, 0⟩,
      fastOkB parMessageW rideW (keyBook K) writtenOrder ⟨idxPlace, 0⟩]) =
    some [false, false, false, false, false] := by
  decide +kernel

/-- A test that follows from another at every value follows at the written one. -/
theorem atFull_of {t u : KeyPub → Bool} (h : ∀ K, t K = true → u K = true)
    (ht : atFull t = true) : atFull u = true := by
  unfold atFull at ht ⊢
  cases hK : fullPub with
  | none => rw [hK] at ht; cases ht
  | some K =>
    rw [hK] at ht
    exact h K ht

/-- **The book is clear at the sender of the index masks.** -/
theorem index_clear_full : atFull (fun K =>
    bookClearAnyB parIndexMasks (fun _ => none) (keyBook K) writtenOrder ⟨idxPlace, 0⟩) = true :=
  atFull_of (fun _ h => (bookClearAnyB_iff _ _).2 (clearAny_of_fast h)) index_fast_full

/-- **The book is clear at the sender of the multiplicities.** -/
theorem multiplicities_clear_full : atFull (fun K =>
    bookClearAnyB parMultiplicities rideMsg (keyBook K) writtenOrder ⟨msgPlace, 0⟩) = true :=
  atFull_of (fun _ h => (bookClearAnyB_iff _ _).2 (clearAny_of_fast h)) multiplicities_fast_full

/-- **The book is clear at the sender of W.** -/
theorem messageW_clear_full : atFull (fun K =>
    bookClearAnyB parMessageW rideW (keyBook K) writtenOrder ⟨wPlace, 0⟩) = true :=
  atFull_of (fun _ h => (bookClearAnyB_iff _ _).2 (clearAny_of_fast h)) messageW_fast_full

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.index_fast_full
#print axioms AtPublicFiles.OfflineRows.multiplicities_fast_full
#print axioms AtPublicFiles.OfflineRows.messageW_fast_full
#print axioms AtPublicFiles.OfflineRows.owned_full
#print axioms AtPublicFiles.OfflineRows.fast_full_no
#print axioms AtPublicFiles.OfflineRows.atFull_of
#print axioms AtPublicFiles.OfflineRows.index_clear_full
#print axioms AtPublicFiles.OfflineRows.multiplicities_clear_full
#print axioms AtPublicFiles.OfflineRows.messageW_clear_full
