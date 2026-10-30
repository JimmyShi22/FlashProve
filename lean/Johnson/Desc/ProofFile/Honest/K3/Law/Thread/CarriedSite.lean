-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CarriedSite.lean: the honest side of the kind "lookup"
(K3): WHAT AN ITEM SAYS IN FRONT OF THE MEMBER'S ACCEPTING STEP AT A LOOKUP'S PLACE, IT SAYS BEHIND
IT: in the form in which the debt `Exchange` asks it of the items that the sub-protocol's row of the
table reads and leaves (ExchangeRow.lean, `exchange_row`, premise hCar). One theorem.

It is the body of the debt `RidesPast` (RidesPast.lean), said at the step itself: at the rounds that
were played, and with the seat behind read at where the prover's run stands behind them. C: any list
of items.

  `carried_site`   **the theorem**

What is laid in: the two states stand in `SameBut`, and the input stays (BehindAt.lean,
`sameBut_site`, `site_step`); the first chain's strings stay below the number of trees sent, and the
library's sentence goes forward (RidesPast.lean, `strs_stay`, `goesOn_of_back`).

PREMISE · WHOSE. hbase: a line on numbers. hBack: for each item of C the library's sentence
`GoesBack (relOf SameBut base)`, at the items' meaning at the honest letters: the item's filler's.
At the items on pins it speaks of the honest side's letter for a pin: owed by whoever lays that
letter. At the library's composed meaning that sentence is shown at pins, under hypotheses
(`mgAll_pin_back`, `mgAll_pinW_back`, Johnson/Desc/Sound/MgAt/K3Rides.lean); at the honest letters'
own letter for a pin: at `pinW` and `pinI` `plainItemGoesBack` shows it, at `lettersHead` under
`P5J.AtMgA` (Honest/K3/Term/LookupPlainItemsRidePast.lean); at `pin m t` no file shows it. THE SAME
SENTENCE, at the items that are carried past and at the items that the row reads and leaves, pays
both debts: `RidesPast` and this part of `Exchange`.
`SiteAt` has the field half: the list of halves holds, at the site's place, the elder row `proverSideOfLookupInChainAtOneOwner`
at these summands. Who pays the field, each at the fast summands and under hypotheses on the list:
where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot` (HalfAtSite.lean
[not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean [not in this library]); where it
holds a lot with the halves of `theLotInst` at the public part: `half_like_ok`, `half_field_like`
(HalfOfLotLike.lean [not in this library]). A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. CONDITIONAL ON the description's return, `SiteAt`, hbase and hBack. No instance of these
hypotheses is exhibited in this file. Nothing on soundness, completeness or any other property of a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidesPast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (Sent)
open VerifiableInference.Desc.Sound (MsgT GoesBack)
open VerifiableInference.OnPublicFiles (K3Letters SameBut relOf)
open Johnson.Desc.First.Walk.Tied (Stays)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT}

/-- **CONDITIONAL ON what this file's head lists (no instance of them is exhibited in this file):
what an item of C says in front of the member's accepting step at a lookup's place, it says behind
it.** -/
theorem carried_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk) (n : Nat)
    (hbase : n ≤ treesTo L.bs b) (C : List Item)
    (hBack : ∀ w, ∀ x ∈ C, GoesBack (relOf SameBut n) (x.holds L.N (L.mg w))) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m E ds y cols st',
      Thr L.thread b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m E ds y cols st' → ∀ x ∈ C, ∀ v,
      L.thread.means m.st.input x (L.thread.seat k m st) (L.thread.strs E) v →
      L.thread.means m.st.input x (L.thread.seat k y.2 st') (L.thread.strs (E.add y.1)) v := by
  intro blk hb k st m E ds y cols st' hA _ hSt x hx v hm
  have hb' : L.bs[b]? = some blk := hb
  have hT := sameBut_site o pol lay KL Fd base A B O hS hb' hSt
  obtain ⟨_, _, _, _, _, _, hin⟩ := site_step o pol lay KL Fd base A B O hS hb' hSt
  have hsent : E.sent = treesTo L.bs b := hA.2.2.2.2.1.2.2.1
  have hst : Stays n (Env.strs L.item (srcAt 0 L.n₁ L.n₂) E)
      (Env.strs L.item (srcAt 0 L.n₁ L.n₂) (E.add y.1)) :=
    stays_mono (strs_stay L.item L.n₁ L.n₂ E y.1) (by rw [hsent]; exact hbase)
  have hseat : (L.thread.seat k m st).1 = (L.thread.seat k y.2 st').1 := by
    show L.pubOf m.st.input.x = L.pubOf y.2.st.input.x
    rw [hin]
  exact goesOn_of_back (hBack m.st.input x hx) (L.thread.seat k m st) _ (L.thread.seat k y.2 st') _
    v ⟨hseat, hT, hst⟩ hm

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.carried_site
