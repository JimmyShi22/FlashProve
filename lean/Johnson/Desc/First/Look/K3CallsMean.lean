-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsMean.lean: the lookup on a link's CALLS: PAYERS OF FIELDS OF WHAT THE
KIND's FIFTY PLACES ASK OF THE TABLE OF JOINTS' MEANING (K3Means.lean's AttMean, LayMean; in them
AttAtTable, LayAtTable; and BehindParts, Johnson/Desc/First/Look/K3CallsBehind.lean), GENERAL IN THE
MEANING: (1) hsmp, hsmpW: a yes of K3.Law.blockVia at the calls' seat leaves whatever reads the
record's statement and book alone; (2) askIn, askFree, the ledger's item and askLive: what the
table's row asks is open in front of the block WHEREVER THE TABLE's TEST pubFit SAYS YES, at any
filling of the door. Statements and proofs. Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: K3.Law.blockVia's decide at seatCalls claim; the table's open public sets.
USER: K3CallsMeanOf.lean, K3CallsMeanR.lean (calls_hsmp); K3CallsAt.lean, K3CallsAtR.lean and others
  (calls_asks_open).
LETTERS: claim, piece, P free; T: any type of values; M: any filling of the door; sub: the segment's
  sort, the head's too.

Main names:
  `via_calls_sameBut`: a yes of blockVia whose own test on the plan says yes leaves all but the open
    link's own part (SameBut).
  `calls_hsmp`: so it leaves every reader rd with "st and book the same give the same value": the
    field hsmp (hsmpW) to the letter, at smp := rd.
  `calls_asks`: the table's row at the calls' place asks the ledger, lookIn and freeAbove.
  `calls_asks_open`: so these three are open in front of the block, under pubFit's yes.
  `calls_live_open`: and liveItem m, where the filling's row asks it there.

Limits. linkFresh m, which the row keeps and does not ask, is not reached by (2).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.OnParts
import Johnson.Desc.First.Look.K3LiveIs
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub More shift pubFit pubRowOf pubRowM pubStartM pubSets
  moreItem)

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (P : Desc.First.Look.P)

/-- A yes of the block with the hearing exchanged leaves all but the open link's own part. -/
theorem via_calls_sameBut (sent : List (ℕ × ℕ)) (laid : Array Nat)
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid sent P []).planOk = true)
    (s : Desc.First.S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (s' : Desc.First.S)
    (hd : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid sent P []).decide s rs cols =
      .ok s') : SameBut s s' :=
  k3_calls_sameBut claim piece laid sent P [] s s' rs cols (Desc.K3.Law.blockVia_decide hplan hd)

/-- **hsmp | hsmpW**, at a reader of the statement and the book. -/
theorem calls_hsmp {T : Type} (rd : Desc.First.S → T)
    (hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → rd s' = rd s) :
    ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid sent P []).planOk =
      true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid sent P
        []).decide s rs cols = .ok s' → rd s' = rd s :=
  fun sent laid hplan s rs cols s' hd =>
    hread s s' (via_calls_sameBut claim piece P sent laid hplan s rs cols s' hd).st
      (via_calls_sameBut claim piece P sent laid hplan s rs cols s' hd).book

end

/-- What the table's row asks at the calls' place. -/
theorem calls_asks (links : List ModelPart) (a : Desc.Place) (m : ℕ) (sub : ModelPart) (hl : a.link = some m)
    (hs : links[m]? = some sub) (hpc : a.piece = 2 + shift sub) :
    (pubRowOf links a).asks = [.ledger m, .lookIn m (2 + shift sub), .freeAbove m] := by
  cases sub <;> simp [pubRowOf, shift, hl, hs, hpc]

/-- **So, where the table's test says yes, these three are open in front of the block.** -/
theorem calls_asks_open (M : More) (links : List ModelPart) (ps : List Desc.Place) (k : ℕ)
    (a : Desc.Place) (m : ℕ) (sub : ModelPart) (hfit : pubFit M links ps = true) (hk : ps[k]? = some a)
    (hl : a.link = some m) (hs : links[m]? = some sub) (hpc : a.piece = 2 + shift sub) :
    ∀ x ∈ [Pub.ledger m, .lookIn m (2 + shift sub), .freeAbove m],
      x ∈ (pubSets M links ps)[k]?.getD [] := fun x hx =>
  asks_open (pubRowM M links) ps (pubStartM M) k a hfit hk x
    (List.mem_append_left _ (by rw [calls_asks links a m sub hl hs hpc]; exact hx))

/-- **And the door's item, where the filling's row asks it there.** -/
theorem calls_live_open (M : More) (links : List ModelPart) (ps : List Desc.Place) (k : ℕ)
    (a : Desc.Place) (m : ℕ) (hfit : pubFit M links ps = true) (hk : ps[k]? = some a)
    (hAsk : liveName m ∈ (M.rows links a).asks) : liveItem m ∈ (pubSets M links ps)[k]?.getD [] :=
  asks_open (pubRowM M links) ps (pubStartM M) k a hfit hk (liveItem m)
    (List.mem_append_right _ (List.mem_map_of_mem hAsk))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.via_calls_sameBut
#print axioms VerifiableInference.OnPublicFiles.calls_hsmp
#print axioms VerifiableInference.OnPublicFiles.calls_asks
#print axioms VerifiableInference.OnPublicFiles.calls_asks_open
#print axioms VerifiableInference.OnPublicFiles.calls_live_open
