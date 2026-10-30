-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/Numbers.lean: M1's part (A) at the protocol's numbers, as the library has them written. Definitions, and each
theorem-to-be as a `def … : Prop`. No proof. The plain lines: the head of Johnson/M1/Statement.lean.
-/
import Johnson.SendSim.Seat.ReadsTab
import Johnson.G.RunsDefs
import Johnson.G.DryProofLit
import Johnson.Unfolds.DeclRecsLit
import Johnson.SendSim.At.BookWide
import Johnson.Desc.ProofFile.Honest.K2.Sending
import Johnson.G.SendsLit
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false

noncomputable section

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-! ## 0 The protocol's numbers, as the library has them written -/

/-- The written declared rounds of the proof file's three chains: the term of Johnson.AtFull.Pub.DW
(Johnson/AtFull/Pub/PubOfMade.lean:70), laid here over the three files of written values alone. That the two are one:
`Spec.sameRounds`, Johnson/M1/AtDescription.lean. -/
def declW : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound :=
  (Johnson.G.Runs.unrunG VerifiableInference.PlanWritten.declRecsFull Johnson.G.dryProofRunsFull0,
    Johnson.G.Runs.unrunG VerifiableInference.PlanWritten.declRecsFull Johnson.G.dryProofRunsFull1,
    Johnson.G.Runs.unrunG VerifiableInference.PlanWritten.declRecsFull Johnson.G.dryProofRunsFull2)

/-- The table of openings at the written declared rounds: each opening of a tree by a round of any of the three chains, with
the positions that the round draws. -/
def tabM : List ((Nat × Nat) × Nat) := readsTab declW

/-- The proof file's codes at the full size: base code 0 = (2^23, 2^22, r 219), mask code 0 = (2^17, 8192, r 219), … -/
def codesW : OnBytes.Codes := VerifiableInference.PlanWritten.proofSizedFull.codes

/-- The first chain's sendings: the proof file's (2), chain 0, in the order of sending. -/
def sendsW : List (Array OnBytes.OracleNotice) :=
  (Johnson.G.sendsFullLit.filter fun s => s.1 == 2 && s.2.1 == 0).map fun s => s.2.2.2.toArray

/-- The messages of sending number i. -/
def sentAt (i : Nat) : Array OnBytes.OracleNotice := sendsW.getD i #[]

/-- The sending's public letter, as the code switch's part makes it. -/
def parAt (i : Nat) : K1.Par := ProofFile.Honest.K2.sendingPar codesW (sentAt i)

/-- How many trees the sendings in front of number i have laid. -/
def treesBefore (i : Nat) : Nat :=
  ((List.range i).map fun j => ((Own.treesMade codesW (sentAt j)).getD {}).shapes.size).sum

/-- Which message of sending i is a fold's fresh mask, with that fold's row variables (foldAt's order: message, k). Laid by
program: the message from sendsFullLit (no main row, no answer); k from cutFirstFull's K10 rows (10 | 9 rounds: k = 8 at even
links, 7 at odd) and the last test's stages (1, 4, 3, 3, 4). Sending 3 l is link l's first message; 75 the finish; 76 to 79
the last test's switches; 80 has the masking word and no fresh mask; 81 is W's sending: its second message is the fresh mask of
the request's own test's first fold (5 row variables; two mask rows), as the library's own job for W has it. -/
def freshW (i : Nat) : Option (Nat × Nat) :=
  if i == 0 then some (3, 8)
  else if i == 72 then some (3, 8)
  else if i % 3 == 0 && i < 72 then (if (i / 3) % 2 == 0 then some (5, 8) else some (4, 7))
  else if i == 75 then some (1, 1)
  else if i == 76 then some (1, 4) else if i == 77 then some (1, 3)
  else if i == 78 then some (1, 3) else if i == 79 then some (1, 4)
  else if i == 81 then some (1, 5)
  else none

/-- The table that rides in sending i, as the shared sending says it. -/
def rideAt (i : Nat) : Nat → Option Ride := ProofFile.Honest.K2.rideOf (sentAt i) (freshW i)

/-- Number 80 is the last test's last sending. Its second message is the masking word: a main row with no sample. The shared
sender lays such a row OF COINS (stepsOf's field word, Johnson/Desc/ProofFile/Honest/K1/Coins.lean), so the sending passes the
shared sending's test like the others, and the law of its opened columns and answers is `Spec.rows`'s. What the last step then
shows of the word IN THE OPEN is no part of shownR: that is (A'), `Spec.baseRows` (Johnson/M1/Law.lean). -/
def wordAt : Nat := 80

/-! ## (A) The rows -/

/-- (A1) THE COUNT. Public and closed, for Lean's kernel, as readsW is for the 52. drawnTab SUMS the openings of a tree over
all three chains, so no «one list a tree» is asked. THE LOT THAT CAN REFUTE M1. -/
def Spec.count : Prop :=
  sendsW.length = 82 ∧ treesBefore 82 = 83 ∧
  ((List.range 82).all fun i =>
    (Own.treesMade codesW (sentAt i)).isSome && readsWithinT tabM (parAt i) (treesBefore i)) = true ∧
  ((List.range 82).all fun i => sendFits (parAt i) (rideAt i)) = true

/-- Every message of every sending lies in a tree, at which positions are drawn: so the test of `Spec.count` skips no message
and accepts none idly. (laidW's and askedW's form, at all 82.) -/
def Spec.laid : Prop :=
  ((List.range 82).all fun i => (List.range (sentAt i).size).all fun k =>
    match ((Own.treesMade codesW (sentAt i)).getD {}).tree[k]? with
    | none => false
    | some τ => drawnTab tabM (treesBefore i + τ) != 0) = true

/-- No slack: one more position drawn for any one of the 83 trees, and the test says no. -/
def Spec.countIsTight : Prop :=
  ∀ n < 83, ((List.range 82).all fun i =>
    readsWithinT (((0, n), 1) :: tabM) (parAt i) (treesBefore i)) = false

/-- What the honest sender discloses, over uniform coins: either side of Spec.rowsExact's equation. -/
def shownLaw (P : K1.Par) (first : Nat) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    PMF (List Shown) :=
  haveI : Nonempty (Cs (dueR P ride)) := ⟨default⟩
  (Prob.unif (Cs (dueR P ride))).map (shownR P first ride data ds asks)

/-- The law at one sending: Spec.rowsExact's own conclusion, at P and ride. -/
def RowsLaw (P : K1.Par) (ride : Nat → Option Ride) : Prop :=
  ∀ (first : Nat) (data data' : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))),
    seedsFit P ds = true → (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) → budAt P asks →
    shownLaw P first ride data ds asks = shownLaw P first ride data' ds asks

/-- (A2) AT EACH SENDING: the law, at every two data. One call of rowsExact behind `Spec.count`'s last clause. IT AVERAGES OVER ALL
OF THE SENDING's COINS, those that later parts spend among them: it is `exact` without `fresh`. WHOSE TEXT: shownR is the shared
sender's. It is the honest part's own text at K1's 52 sendings (0; 3 l + 1, 3 l + 2; 81); at the code switch's 25 and the last
test's five it is the shared sender's text at the written numbers. -/
def Spec.rows : Prop := ∀ i < 82, RowsLaw (parAt i) (rideAt i)

/-! (A3), at the description that verify is compiled from: Johnson/M1/AtDescription.lean (`Spec.atDescription`). -/

/-- (A4) THE LENT COINS. At each sending whose coins a later block spends (a link's mask row; the index-mask message; a fold's
fresh mask): the premise of sendFreshAtWide at the REAL book. Bk, ord, owner: letters. -/
def Spec.lent (Bk : ProverCoinCounts) (ord : List Place) (owner : Nat → Addr) : Prop :=
  ∀ i < 82, i ≠ wordAt → BookClearAny (parAt i) (rideAt i) Bk ord (owner i)

/-- M1's half on numbers, but for (A3) and (A4). -/
def Spec.numbers : Prop := Spec.count ∧ Spec.laid ∧ Spec.countIsTight ∧ Spec.rows

end OnBytes.M1
