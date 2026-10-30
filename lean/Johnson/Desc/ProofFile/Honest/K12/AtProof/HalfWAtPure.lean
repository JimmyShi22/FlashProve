-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfWAtPure.lean: the pair at the last chain's proximity
test (`halfW`, HalfW.lean in this folder) at a filling of the honest prover (`OnlineProverParts`,
Johnson/Desc/ProofFile/Honest/AtPure.lean): the filling `widerFillOwnCPUO` (HalfOAtPure.lean in this
folder) with its field `second`, which is [] at all fillings before it.

  `secondW`     the last chain's sides: the pair, with the letters of `jobRealW` named; no side
                 where the shared chain's six, the places or the first chain are not made
  `widerFillOwnCPUOW`, `widerFillAtCPUOW`   `widerFillOwnCPUO` and `widerFillAtCPUO` with that field
  `secondW_ok`, `secondW_error`, `secondW_error_places`, `secondW_error_chain`   the arm
  `widerFillOwnCPUOW_second`, `_shared`, `_lots`, `_enc`   the fields

BY ITSELF FOR A TOY ALONE: no lot sends W's message: at these two fillings the term (h1),
«no laying before each is the sender's own, by rfl or a lemma», can never be met:
K1/Law/WSideAtFill.lean lays that lot. The eight letters (HalfW.lean's
Limits), at
`widerFillAtCPUOW` (at `LongLots.plain`; at another L, `widerFillOwnCPUOW`'s lots and these letters
part: nothing ties them), as far as they can be named. S: the filling's. `pile`: `O.pile`: what
part 5's lot `K13.k13Lot wt O.pile` reads, so the sender's `K13.wDataAt`'s pile, by text. `no`:
`K1.lotNo o Z`, by which
`K1.dataSideNo` numbers its places. `readers`: `⟨w.trace, I.weights Z w.w₀, w.rc⟩`, the lots' own
term. `weights`: `I.weights Z w.w₀`. `rand`: `randAt`, as at U and O. Fd: `P5J.F0T o Z N c`, at the
plan's numbers and the library's chain; `enter`: `Seat.enterOwn`. THESE ARE EIGHT READINGS OF
TEXTS: no lemma here holds any of them to the sender's. A NINTH: the first opening's job is
`K1.firstJob`; the filling's sender there is `placeJob … (firstFold …) (lotData …)`: the rides are
one at the written plan (`firstRide_written`, HalfAtHeadW.lean); the data is read by no row of the
index-mask message, which has mask rows alone [by reading]. `pile` is the one to hold first: the
filling holds no half at W's sending: `K1.wSide` is in no lot here. S and `no` reach no row of this
test, by reading.

Why the arm. As at U and O (Honest/AtPureWiderK12U.lean, «Why the arm»): the maker of the six
rejects where the tests on the shape refuse; this pair's Omega member reads `rowsOf` through
`askOf`. So the pair is laid only where the six are made. By reading; no lemma. `halfW` lays
without the arm:
`secondW` is the term to lay.

Limits.
- A SILENT DEFAULT, of three kinds: no side where `nowSharedBy`, `H2U.placesOfMade` or
  `ProofFile.onlineFirstChainAt` returns an error. A fourth, `halfW`'s: none where `four`, `sendPub` or
  `OnBytes.linMessageW` gives nothing.
- WHERE COLUMNS ARE HANDED THE TWO PARTS CANNOT REFUSE (Honest/K12/Parts.lean); at none they err, by
  the guard: having a side is no ground. That a part plays is not said here.
- THE FILLING's FIRST CHAIN HAS NO HALF AT W's SENDING: `OnlineProverParts.lots` is `widerFillOwnCPUO`'s: that a
  sender is without a side there is the older filling's limit, and this pair reads that sending's
  text anew: it does not read a stretch that anybody sent.
- That `onlineProverFromPublicFiles` returns at these fields, that `ready` does, that a part plays: none is stated.
- What may be said of this pair on hiding stands in the head of HalfW.lean in this folder.
- Nothing is evaluated here. It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure
import Johnson.Desc.K12.Seat.Own
import Johnson.P5J.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open ProofFile.Honest.K12.AtProof (halfW randAt widerFillOwnCPUO widerFillAtCPUO)

variable {W₀ X : Type}

/-- **The last chain's sides: the pair at the test, behind the guard.** A SILENT DEFAULT: no side
where the six, the places or the first chain are not made. THE ARM IS LOAD-BEARING: NEVER LAY
`halfW` WITHOUT IT (the file's head). WHERE COLUMNS ARE HANDED THE TWO PARTS CANNOT REFUSE: having a
side is no ground that they play. -/
def secondW (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub)
    (G : Ground) : List (Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X) :=
  match nowSharedBy (I.weights Z) Z, H2U.placesOfMade Z.made, ProofFile.onlineFirstChainAt Z with
  | .ok _, .ok N, .ok c =>
    halfW S (P5J.F0T o Z N c) VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo o Z)
      (fun w => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) (fun w => I.weights Z w.w₀)
      (fun P w => randAt P w.rc) Z G
  | _, _, _ => []

/-- **widerFillOwnCPUO with the pair at the last chain.** BY ITSELF FOR A TOY ALONE: no lot sends
W's message. widerFillOwnCPUOWM (Honest/K1/Law/WSideAtFill.lean) lays that lot behind its lots, and
the honest prover's filling is built on that. The arguments are widerFillOwn's. -/
def widerFillOwnCPUOW (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { widerFillOwnCPUO own₀ L I o S O with second := secondW I o S O }

/-- **widerFillAtCPUO's sister with that pair.** FOR A TOY ALONE: no lot sends W's message. -/
def widerFillAtCPUOW (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwnCPUOW () (LongLots.plain o S O) I o S O

/-- **Where the three are made**: the pair. -/
theorem secondW_ok (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Z : Pub} (G : Ground) {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    {N : H2U.Places4} {c : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (h : nowSharedBy (I.weights Z) Z = .ok six) (hN : H2U.placesOfMade Z.made = .ok N)
    (hc : ProofFile.onlineFirstChainAt Z = .ok c) :
    (secondW I o S O Z G : List (Placed _ _ X)) =
      halfW S (P5J.F0T o Z N c) VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo o Z)
        (fun w => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) (fun w => I.weights Z w.w₀)
        (fun P w => randAt P w.rc) Z G := by
  unfold secondW
  rw [h, hN, hc]

/-- **Where the six are not made**: no side. -/
theorem secondW_error (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Z : Pub} (G : Ground) {e : String} (h : nowSharedBy (I.weights Z) Z = .error e) :
    (secondW I o S O Z G : List (Placed _ _ X)) = [] := by
  unfold secondW
  rw [h]

/-- **Where the places are not made**: no side. -/
theorem secondW_error_places (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {Z : Pub} (G : Ground) {e : String} (h : H2U.placesOfMade Z.made = .error e) :
    (secondW I o S O Z G : List (Placed _ _ X)) = [] := by
  unfold secondW
  rw [h]
  cases nowSharedBy (I.weights Z) Z <;> cases ProofFile.onlineFirstChainAt Z <;> rfl

/-- **Where the first chain is not made**: no side. -/
theorem secondW_error_chain (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {Z : Pub} (G : Ground) {e : String} (h : ProofFile.onlineFirstChainAt Z = .error e) :
    (secondW I o S O Z G : List (Placed _ _ X)) = [] := by
  unfold secondW
  rw [h]
  cases nowSharedBy (I.weights Z) Z <;> cases H2U.placesOfMade Z.made <;> rfl

/-- The field `second`. -/
theorem widerFillOwnCPUOW_second (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    (widerFillOwnCPUOW own₀ L I o S O).second Z G = secondW I o S O Z G := rfl

/-- The field `shared` is widerFillOwnCPUO's. -/
theorem widerFillOwnCPUOW_shared (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    (widerFillOwnCPUOW own₀ L I o S O).shared Z G =
      (widerFillOwnCPUO own₀ L I o S O).shared Z G := rfl

/-- The field `lots` is widerFillOwnCPUO's. -/
theorem widerFillOwnCPUOW_lots (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCPUOW own₀ L I o S O).lots = (widerFillOwnCPUO own₀ L I o S O).lots := rfl

/-- The field `enc` is widerFillOwnCPUO's. -/
theorem widerFillOwnCPUOW_enc (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCPUOW own₀ L I o S O).enc = (widerFillOwnCPUO own₀ L I o S O).enc := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.secondW
#print axioms ProofFile.Honest.widerFillOwnCPUOW
#print axioms ProofFile.Honest.widerFillAtCPUOW
#print axioms ProofFile.Honest.secondW_ok
#print axioms ProofFile.Honest.secondW_error
#print axioms ProofFile.Honest.secondW_error_places
#print axioms ProofFile.Honest.secondW_error_chain
#print axioms ProofFile.Honest.widerFillOwnCPUOW_second
#print axioms ProofFile.Honest.widerFillOwnCPUOW_shared
#print axioms ProofFile.Honest.widerFillOwnCPUOW_lots
#print axioms ProofFile.Honest.widerFillOwnCPUOW_enc
