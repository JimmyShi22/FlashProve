-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/AtBaseMaker.lean: the linear claim (kind K14): THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean) AT THE TWO LATER CHAINS' THREADS, AT A
RETURN OF THE BASE MAKER (baseMaker, E2E/BaseMaker.lean: the maker onlineProverFromPublicFiles at the three public files
and the filling at the matrices, the format's second hash function, the reference sizes and the
honest
openings). Three theorems, all calls: the first at that filling's four arguments, the two others at
that maker's types.

  k14_five_shared_at_base   at the members 1 to 8 of the shared chain: five_at_sharedParts
                            (AtFullSide/K14/AtLaterThreads.lean)
  k14_five_last_at_base     at the member 0 of the last chain, where every rider of the letters
                            begins at border 2 or later: five_at_lastParts (the same file)
  k14_five_last_tied_at_base   at the member 0 of the last chain, where the letters' riders begin
                               with
                            tiedAheadRider and tiedRider: five_at_lastParts_tied
                            (AtFullSide/K14/AtLastTied.lean)

A LIMIT. THE BASE MAKER's PROVER IS NOT THE HONEST PROVER OF THE PROTOCOL: that one is made at the
filling onlineFilling, which is baseFilling read through, at another type of coins
(onlineFilling_eq, E2E/BaseMaker.lean). Nothing here carries the five over.
A SECOND. k14_five_last_at_base cannot be called at letters that hold tiedRider, which speaks at
border 1: there the third theorem is the one to call.

The premises, the two limits at the last chain, the label NOT IN FRONT OF A LAW OVER COINS on the
first of the three with its ground, and what is not claimed: the heads of
AtFullSide/K14/AtLaterThreads.lean and AtFullSide/K14/AtLastTied.lean: all of it binds here.
-/
import AtFullSide.K14.AtLastTied
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LaterLetters LastLetters
  sharedThread lastThread sharedParts lastParts tiedRider)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared)
open VerifiableInference.Desc.Third (S₃)
open Bind.ForProver (shapeOf)
open Desc.K14 (St)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit}

/-- **FiveAtBorder at a member b, 1 ≤ b ≤ 8, of the shared chain's thread at sharedParts, at a
return of the base maker**, at the committer's made input. htab: table is tableShared at the
filling's readers. h0, h1: fixed is 1 at own 0, and 4 at own 1 and 2. late: every rider begins at
border 10 or later. NOT IN FRONT OF A LAW OVER COINS (AtFullSide/K14/AtLaterThreads.lean's head). -/
theorem k14_five_shared_at_base (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (L : LaterLetters A) (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins) (sd : Bind.ForProver.Seed (shapeOf A.Z) × ℕ)
    (bytes : ByteArray × ByteArray) {JU JO : TestJob (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit}
    (htab : L.table = tableShared (qAt A.Z h.places) (matrixInput.weights A.Z)
      (randNow (qAt A.Z h.places)) JU JO ())
    (h0 : L.fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → L.fixed (.own (1 + i)) = 4)
    (late : ∀ c ∈ L.riders, 10 ≤ c.lo)
    (Said : Nat → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h ⟨matrixInput.weights A.Z, randNow (qAt A.Z h.places)⟩
      (sharedParts h L) ⟨w₀, rc, A.H.key (Bind.ForProver.xiAt (shapeOf A.Z) A.Z
        ⟨matrixInput.weights A.Z w₀, rc, sd⟩ bytes)⟩) Said fall b :=
  five_at_sharedParts matrixInput _ _ _ made h L w₀ rc sd bytes htab h0 h1 late Said fall b hb1 hb8

/-- **FiveAtBorder at the member 0 of the last chain's thread at lastParts, at a return of the base
maker.** BehindS and ExchangeS hold vacuously wherever fillZ's test at border 0 is false; ExchangeS
takes the items ev and dot, and AcceptedS secondDoor's tests, from the invariant in front. late:
every rider that L holds begins at border 2 or later. The return of the maker is not spent: it
stands in h. -/
theorem k14_five_last_at_base (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit →
      Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) (late : ∀ c ∈ L.riders, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 0 :=
  five_at_lastParts h first L reads w Said fall late

/-- **FiveAtBorder at the member 0 of the last chain's thread at lastParts, at a return of the base
maker, with tiedRider laid.** hrid, late: L's riders are tiedAheadRider at the own test's declared
rounds, tiedRider, and clauses that begin at border 2 or later. BehindS and ExchangeS hold vacuously
wherever fillZ's test at border 0 is false; ExchangeS takes the items ev and dot, AcceptedS
secondDoor's tests, and the laying of tiedRider the test tiedAheadB, from the invariant in front.
The return of the maker is not spent: it stands in h. -/
theorem k14_five_last_tied_at_base (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit →
      Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    {later : List (RiderCl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) S₃)}
    (hrid : L.riders = tiedAheadRider _ (LLT25.c2 h.places).rounds :: tiedRider _ h.places :: later)
    (late : ∀ c ∈ later, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 0 :=
  five_at_lastParts_tied h first L reads w Said fall hrid late

end AtFullSide.K14

#print axioms AtFullSide.K14.k14_five_shared_at_base
#print axioms AtFullSide.K14.k14_five_last_at_base
#print axioms AtFullSide.K14.k14_five_last_tied_at_base
