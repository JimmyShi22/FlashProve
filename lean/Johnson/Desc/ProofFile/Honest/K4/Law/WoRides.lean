-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoRides.lean

What is here. The threads' debt RidesPast at the pending row's item, which the row of the layers'
own rounds (kind K4) opens and nine later members ride past: what the item says in front of such a
member it says behind. General in the thread and in the member. Statements with their proofs, over
the library's `row_tie` (Johnson/Top/H0/MergeLaw/WoRow.lean) and its converse `pend_of`
(Johnson/Top/H0/MergeLaw/PendRow.lean).

  `K4WoSame`: what is left for the row, the number of the index masks' message and that message's
      ledger are as they were; the reader's matrix, and its mask entries at that message, are as
      they were. This defines a hypothesis.
  `rowAt_same`: under the first three the library's reader of the pending row gives in front
      whatever row it gives behind.
  `holds_same`: a row that holds of a witness holds of one with the same matrix and the same
      entries at the row's own mask places.
  `woAt_rides`: the library's sentence on the pending row, from the state in front to the state
      behind.
  `K4WoTableBack`: the thread's sentence at the item gives the library's: the converse of
      `K4WoTable` (Law/Wo.lean). This defines a hypothesis.
  `k4_ridesPastAtS_wo`: RidesPastAtS T Said b iWo.
  `woSame_quiet`: K4WoSame at a member that leaves the statement, the book, «out» and what is
      left, for a reader that reads of the state the statement and the book alone.

Limits. CONDITIONAL. THE HYPOTHESIS `K4WoSame` IS SHOWN OF NO MEMBER's CLAUSE OF keeps HERE: it is a
hypothesis's form: what a member that the pending row's item rides past must leave as it was. At a
member that turns the statement or the book (a sending's context is written back into both:
`S.back`, Johnson/Desc/First/State.lean) its last two clauses, on the reader of the pile of pending
rows, are real content: at the library's own reader Law/WoRidesGrown.lean [not in this library; so
here read: not proved in this library] brings them down to
sentences on the two states; `woSame_quiet` covers only a member that leaves the statement, the
book, «out» and what is left. Member by member: Law/WoPast.lean, Law/WoPastBehind.lean and
Law/WoRidesLook.lean (none of the three is in this library; so here read: not proved in this
library). `K4WoTable` and its converse are shown at the library's own parameters in
Law/WoRidesAt.lean; no example of a thread's sentence holding there is known. Nothing on soundness,
on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Wo
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Top.H0.MergeLaw.WoRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (TensorRow)
open OnBytes.Model (Reading WsLay)
open VerifiableInference.Desc (Claim First.S Strs)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData woAt)
open VerifiableInference.Desc.First.MergeLaw (row_tie pend_of)
open VerifiableInference.Desc.K13.Law (Holds lhs colOf formVal weights)
open Johnson.Desc.First.Walk.Law (leftOf ledgerAt rowAt rowAt_some)

/-- **What a member that the pending row's item rides past must leave as it was.** z: what was
handed to the chain. v: the witness. This defines a hypothesis; the definition claims nothing. -/
def K4WoSame {P Wt : Type} {nR kC : Nat} (rw : P × First.S → Wt → PileWit nR kC) (z : P)
    (s s' : First.S) (v : Wt) : Prop :=
  leftOf s' = leftOf s ∧ s'.out.indexMasks = s.out.indexMasks ∧ ledgerAt s' = ledgerAt s ∧
    (rw (z, s') v).mat = (rw (z, s) v).mat ∧
    ∀ c, (rw (z, s') v).mask ⟨s.out.indexMasks, c⟩ = (rw (z, s) v).mask ⟨s.out.indexMasks, c⟩

/-- The library's reader gives in front whatever row it gives behind. -/
theorem rowAt_same {lay : WsLay} {n : Nat} {lin : OnBytes.Params.LinShape} {s s' : First.S}
    (h1 : leftOf s' = leftOf s) (h2 : s'.out.indexMasks = s.out.indexMasks)
    (h3 : ledgerAt s' = ledgerAt s) {r : TensorRow} (hr : rowAt lay n lin s' = some r) :
    rowAt lay n lin s = some r := by
  obtain ⟨w0, w, l, c, l', b1, b2, b3, b4, rfl, -, -, -⟩ := row_tie hr
  rw [h1] at b1
  rw [h3] at b3
  rw [h2]
  exact rowAt_some.2 ⟨w0, _, b1, pend_of b2 b3 b4⟩

/-- A row that holds of a witness holds of one that agrees with it where the row reads. -/
theorem holds_same {nR kC : Nat} {w w' : PileWit nR kC} {r : TensorRow} (hm : w'.mat = w.mat)
    (hk : ∀ x ∈ r.masks, w'.mask x.1 = w.mask x.1) (h : Holds Reading.gl w r) :
    Holds Reading.gl w' r := by
  unfold Holds lhs at h ⊢
  have e1 : colOf w' (weights Reading.gl nR r.g) = colOf w (weights Reading.gl nR r.g) := by
    unfold colOf
    rw [hm]
  have e2 : formVal Reading.gl w'.mask r.masks = formVal Reading.gl w.mask r.masks := by
    unfold formVal
    exact congrArg List.sum (List.map_congr_left fun x hx => by rw [hk x hx])
  rw [e1, e2]
  exact h

/-- **The library's sentence on the pending row rides.** CONDITIONAL: on K4WoSame. -/
theorem woAt_rides {P Wt : Type} {d : PubData} {nR kC : Nat}
    {rw : P × First.S → Wt → PileWit nR kC} {m : Nat} {z : P} {s s' : First.S} {y y' : Strs}
    {v : Wt} (hS : K4WoSame rw z s s' v) (h : woAt d rw m (z, s) y v) :
    woAt d rw m (z, s') y' v := by
  obtain ⟨h1, h2, h3, hm, hk⟩ := hS
  intro r hr
  have hr0 : rowAt d.lay (d.ncl m) d.lin s = some r := rowAt_same h1 h2 h3 hr
  obtain ⟨_, w, _, c, _, _, _, _, _, e, -, -, -⟩ := row_tie hr0
  refine holds_same hm (fun x hx => ?_) (h r hr0)
  rw [e] at hx
  obtain rfl := List.mem_singleton.1 hx
  exact hk c

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **The thread's sentence at the item gives the library's.** A hypothesis's form. Nothing is
claimed by the definition. -/
structure K4WoTableBack (T : Thread Bk First.S Claim V W X Pb) (iWo : T.ι) {nR kC : Nat}
    (d : PubData) (rw : T.P × First.S → T.Wt → PileWit nR kC) (m : Nat) : Prop where
  /-- the thread's sentence gives the library's -/
  wo : ∀ w a y v, T.means w iWo a y v → woAt d rw m a y v

variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {iWo : T.ι} {nR kC : Nat} {d : PubData}
  {rw : T.P × First.S → T.Wt → PileWit nR kC} {mL : Nat}

/-- **`RidesPastAtS` AT THE PENDING ROW's ITEM.** CONDITIONAL: on the table both ways, and on hK:
wherever the pair of the thread's sentence and what has been said holds, the member's clause of
keeps gives K4WoSame at every witness. -/
theorem k4_ridesPastAtS_wo (Said : Nat → Coins Bk → Mid W X → Prop)
    (Tb : K4WoTable T iWo d rw mL) (Tc : K4WoTableBack T iWo d rw mL)
    (hK : ∀ k s m E s' v, ThrS T Said b k s m E → T.keeps b s s' →
      K4WoSame rw (T.seat k m s).1 s s' v) : RidesPastAtS T Said b iWo :=
  fun k s m E s' _ v hT hKp h0 =>
    Tb.wo _ _ _ _ (woAt_rides (hK k s m E s' v hT hKp) (Tc.wo _ _ _ _ h0))

/-- **At a member that leaves the statement, the book, «out» and what is left**, for a reader that
reads of the state the statement and the book alone. -/
theorem woSame_quiet {P Wt : Type} {nR kC : Nat} {rw : P × First.S → Wt → PileWit nR kC}
    (hrw : ∀ z s s', s'.st = s.st → s'.book = s.book → rw (z, s') = rw (z, s)) {z : P}
    {s s' : First.S} (hst : s'.st = s.st) (hbk : s'.book = s.book) (hout : s'.out = s.out)
    (hleft : leftOf s' = leftOf s) (v : Wt) : K4WoSame rw z s s' v := by
  refine ⟨hleft, by rw [hout], ?_, by rw [hrw z s s' hst hbk], fun c => by rw [hrw z s s' hst hbk]⟩
  unfold ledgerAt
  rw [hst, hout]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.rowAt_same
#print axioms ProofFile.Honest.K4.holds_same
#print axioms ProofFile.Honest.K4.woAt_rides
#print axioms ProofFile.Honest.K4.k4_ridesPastAtS_wo
#print axioms ProofFile.Honest.K4.woSame_quiet
