-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SeatedPair.lean: kind K13, the members' batching: THE KIND's
STATEMENTS AT ITS MEMBER IN THE FRAME's OWN FORMS OF A SHARE (`ExchangeAt`, `RidesPastAt`,
Honest/Thread/Shares.lean) AND FROM THE PAIR "the thread and what is said" (`PlaysS`, `BehindS`,
Honest/Thread/PaysS.lean; `ExchangeAtS`, `RidesPastAtS`, Honest/Thread/SharesS.lean), with the
sentence Said a variable. Statements with their proofs: calls and unfoldings alone.
Main names:
  `exchangeAt_iff`: this folder's `ExchangeOf` at a list of one item IS the frame's `ExchangeAt`: by
    unfolding. General in the thread.
  `k13_unmarked_at`: the share of `RidesPast` at "unmarked": from what is asked of `keeps`.
  `k13_riders_shares`: from `K13Riders` (SeatedRiders.lean): the share of `Exchange` at "pileOne"
    and the share of `RidesPast` at "unmarked".
  `k13_riders_pair`: **the four statements from the pair**, at every Said: from `K13Riders` and hst:
    the other members' clauses in force stay past this one (`StaysBy`).

What is not claimed. That `K13Riders` holds at any L. `StaysBy` for any clause. Nothing that
SeatedRiders.lean does not have: a form from the pair is weaker than the form from the thread.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.SeatedRiders
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.K13.AcceptedPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (Wit)
open ProofFile.Honest.FirstThread (Letters)

section
variable {S' Cl' V W X Pb : Type} {Bk : ProverCoinCounts}

/-- This folder's share at a list of one item is the frame's share at that item. -/
theorem exchangeAt_iff (T : Thread Bk S' Cl' V W X Pb) (b : Nat) (i : T.ι) :
    ExchangeOf T b [i] ↔ ExchangeAt T b i := Iff.rfl

end

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  {L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M} {b : Nat}

/-- The share of `RidesPast` at "unmarked": behind, the state bears no mark of failure. -/
theorem k13_unmarked_at (hkeep : ∀ s s', L.keeps b s s' → s'.failed = none) :
    RidesPastAt L.thread b Item.unmarked :=
  fun _ s _ _ s' _ _ _ hk _ => hkeep s s' hk

variable {weights : W₀ → Weights} {pile : PileOf Xi} {P : Where} {Cl' : Type}
  {rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol}
  {asked : Xi → E} {cs : List (RiderCl (Local W₀ Rc Xi Tr) S)} {b₀ : Nat}

/-- From the structure: the two shares, in the frame's own forms. -/
theorem k13_riders_shares (h : K13Riders L b weights pile P Cl' rd asked cs b₀) :
    ExchangeAt L.thread b Item.pileOne ∧ RidesPastAt L.thread b Item.unmarked :=
  ⟨k13_pileOne h.place h.opened h.member h.isAtM3 h.reads h.mat h.coins h.rows h.reply,
    k13_unmarked_at fun s s' hk => ((h.keepsIs s s').1 hk).1.1⟩

/-- **The four statements from the pair**, at every sentence Said on what earlier rounds showed:
from `K13Riders` and hst: the other members' clauses in force stay past this one. -/
theorem k13_riders_pair (h : K13Riders L b weights pile P Cl' rd asked cs b₀)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy L.thread b c)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧
      ExchangeAtS L.thread Said b Item.pileOne ∧ RidesPastAtS L.thread Said b Item.unmarked :=
  ⟨playsS_of L.thread Said (k13_riders h hst).1, behindS_of L.thread Said (k13_riders h hst).2.1,
    exchangeAtS_of L.thread Said (k13_riders_shares h).1,
    ridesPastAtS_of L.thread Said (k13_riders_shares h).2⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.exchangeAt_iff
#print axioms ProofFile.Honest.K13.k13_unmarked_at
#print axioms ProofFile.Honest.K13.k13_riders_shares
#print axioms ProofFile.Honest.K13.k13_riders_pair
