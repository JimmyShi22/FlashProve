-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CloseYes.lean: WHEN K9's TWO MEMBERS WITHOUT A ROUND SAY YES; AND `AcceptedS`
(Honest/Thread/PaysS.lean: the debt "accepted", asked from the pair of the thread and what is said) AT BOTH, FROM
NAMED PREMISES. THE THREAD T AND THE LETTER Said ARE VARIABLES. Statements and proofs; no goal is stated.
  **`eq_yes_iff`**, **`shut_yes_iff`**   at a block that seats the lot's block alone (`IM.LaidAlone`, at a place that
      is not K7's): its decision says yes at s, with s' behind, JUST IF the clause `EqKeeps s s'` (`ShutKeeps s s'`,
      Honest/K9/CloseKeeps.lean) holds: SO THE CLAUSE IS ALL THAT THE YES GIVES, AND ALL THAT IT ASKS OF THE DECISION
  `eq_yes`, `shut_yes`   so, from the state in front alone: no mark of failure, K9's lens reads a part, and K9's
      `door` returns at it ("the one equation"); no mark, and a segment's book-keeping is open ("the segment is shut")
`step_noRound`, `SeatedClose.stepE`, `SeatedClose.stepS`   carried to the description's own blocks' STEPS, at no round
and no column (that the prover's side of the step shows no round and reads no column there: `quiet_step`,
Honest/K9/ThrClose.lean)
**`K9Ends.acceptedE`**, **`K9Ends.acceptedS`**   `AcceptedS T Said fall e`, `AcceptedS T Said fall z`, AT EVERY LETTER
fall, from K9's structure `K9Ends` (Honest/K9/ThrClose.lean), ONE NAMED PREMISE ON T's LETTER form (`front`: a state
that has the form in front bears no mark of failure) AND ONE PREMISE THAT IS NO FACT ON A LETTER (`ready`): at every
stand of the pair (`ThrS T Said …`) AT WHICH fall SAYS NOTHING: K9's lens reads a part and `door` returns at it ("the
one equation"); a segment's book-keeping is open ("the segment is shut"): K9's OWN DEBTS, UNPAID. `door` holds tests
that read values of the ledger: whether one of them can refuse at a state that a run has reached, so that a fall is
owed at e, is not settled. This is the road from the pair in front. A second road for both members goes over "returns"
laws on shapes (Johnson/Desc/First/Batch/Shape/DoorChain.lean); nothing of that road is in this file. No member; the two last are called by no line.
WHAT IS NOT CLAIMED. That `door` returns at any state. Any premise at any thread. `Exchange`. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.ThrClose
import Johnson.Desc.ProofFile.Honest.K9.YesAtSeat
import Johnson.Desc.First.Batch.Law.KeepsField
import Johnson.Desc.First.StateOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **"The one equation" says yes just if the clause holds.** -/
theorem eq_yes_iff {b : Block S Claim} {p : Desc.K9.Where} {ok : Bool} {name : String} {a : Place}
    (hb : IM.LaidAlone ProofFile.sameReply b
      ({ Desc.K9.oneEquation (Cl := Unit) Desc.K9.atS p with planOk := ok } : Block S Unit).retype name a)
    (hk : a.kind ≠ KindName.K7) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok s' ↔ EqKeeps s s' := by
  refine ⟨eq_pays hb hk s s' rs gs, fun K => ?_⟩
  obtain ⟨x, o, hx, ho, rfl⟩ := K.laid
  refine (IM.yes_alone hb hk s _ rs gs).2 ⟨?_, K.mark, ?_⟩
  · show (Desc.K9.atS.part s).bind (fun y => (Desc.K9.door y.owed y.laid y.L y.F y.d).bind fun o =>
      (.ok (Desc.K9.atS.set s { y with owed := o.owed, L := o.L, F := o.F, d := o.d }) : Except String S)) = _
    have e : Desc.K9.atS.part s = .ok x := by unfold Desc.K9.Lens.part; rw [hx]; rfl
    rw [e]
    show (Desc.K9.door x.owed x.laid x.L x.F x.d).bind (fun o =>
      (.ok (Desc.K9.atS.set s { x with owed := o.owed, L := o.L, F := o.F, d := o.d }) : Except String S)) = _
    rw [ho]
    rfl
  · unfold ProofFile.sameReply
    rw [K.reply]
    exact beq_self_eq_true _

/-- **"The segment is shut" says yes just if the clause holds.** -/
theorem shut_yes_iff {b : Block S Claim} {p : Desc.K9.Where} {piece : ℕ} {name : String} {a : Place}
    (hb : IM.LaidAlone ProofFile.sameReply b (Desc.K9.shut (Cl := Unit) p piece).retype name a)
    (hk : a.kind ≠ KindName.K7) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok s' ↔ ShutKeeps s s' := by
  refine ⟨shut_pays hb hk s s' rs gs, fun K => ?_⟩
  obtain ⟨L, hL, rfl⟩ := K.laid
  refine (IM.yes_alone hb hk s _ rs gs).2 ⟨?_, K.mark, ?_⟩
  · show (Desc.K9.there "K9.in-a-segment" s.link?).bind (fun L =>
      (.ok (s.putLink (Desc.K9.closed L L.check.frame)) : Except String S)) = _
    rw [hL]
    rfl
  · unfold ProofFile.sameReply
    rw [K.reply]
    exact beq_self_eq_true _

/-- From the state in front alone. -/
theorem eq_yes (s : S) (x : Desc.K9.Part) (o : Desc.K9.Out Unit) (hf : s.failed = none)
    (hx : Desc.K9.atS.get? s = some x) (ho : Desc.K9.door x.owed x.laid x.L x.F x.d = .ok o) :
    EqKeeps s (Desc.K9.atS.set s { x with owed := o.owed, L := o.L, F := o.F, d := o.d }) :=
  ⟨(set_failed s _).trans hf, by rw [set_out], ⟨x, o, hx, ho, rfl⟩⟩

/-- From the state in front alone. -/
theorem shut_yes (s : S) (L : LinkCtx) (hf : s.failed = none) (hL : s.link? = some L) :
    ShutKeeps s (s.putLink (Desc.K9.closed L L.check.frame)) :=
  ⟨(Desc.K9L.failed_putLink s _).trans hf, by rw [S.out_putLink], ⟨L, hL, rfl⟩⟩

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {Q : Close.Par}
  {bE bS : Block S Claim}

/-- A block without a round: its step at no round and no column is its decision. -/
theorem step_noRound (b : Block S Claim) (hr : b.rounds = []) (ft : ℕ) (s s' : S)
    (hd : ∀ gs, b.decide s [] gs = .ok s') : b.step ft s [] [] = .ok (s', 0) := by
  refine (Sound.step_ok_iff ft b s s' [] [] 0).2 ⟨?_, ?_, ?_, hd _⟩
  · rw [hr]; rfl
  · rw [hr]; rfl
  · rw [hr]; rfl

/-- The step of "the one equation". -/
theorem SeatedClose.stepE (H : SeatedClose c Z l Lk p Q bE bS) (ft : ℕ) (s s' : S) (K : EqKeeps s s') :
    bE.step ft s [] [] = .ok (s', 0) :=
  step_noRound bE H.quiet.1 ft s s' fun gs =>
    (eq_yes_iff H.aloneE (show KindName.K9 ≠ KindName.K7 by decide) s s' [] gs).2 K

/-- The step of "the segment is shut". -/
theorem SeatedClose.stepS (H : SeatedClose c Z l Lk p Q bE bS) (ft : ℕ) (s s' : S) (K : ShutKeeps s s') :
    bS.step ft s [] [] = .ok (s', 0) :=
  step_noRound bS H.quiet.2.2.1 ft s s' fun gs =>
    (shut_yes_iff H.aloneS (show KindName.K9 ≠ KindName.K7 by decide) s s' [] gs).2 K

variable {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {e z : ℕ}
  {Said : ℕ → Coins Bk → Mid W X → Prop}

/-- **`AcceptedS` at "the one equation".** -/
theorem K9Ends.acceptedE (H : K9Ends T e z c Z l Lk p Q bE bS)
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (front : ∀ a s, T.form e (a, s) = true → s.failed = none)
    (ready : ∀ κ s m En, ThrS T Said e κ s m En → fall e s [] = none →
      ∃ x o, Desc.K9.atS.get? s = some x ∧ Desc.K9.door x.owed x.laid x.L x.F x.d = .ok o) :
    AcceptedS T Said fall e := by
  intro blk hblk κ s m En ds y cols hT hd _ hfall hM
  rw [H.bsE] at hblk
  cases hblk
  obtain ⟨rfl, rfl, rfl⟩ := quiet_step T bE H.seat.quiet.1 κ m En ds y cols hd hM
  have hf := front _ s hT.1.2.2.1.1
  obtain ⟨x, o, hx, ho⟩ := ready κ s m En hT hfall
  refine ⟨Desc.K9.atS.set s { x with owed := o.owed, L := o.L, F := o.F, d := o.d }, hM, ?_⟩
  exact H.seat.stepE T.ft s _ (eq_yes s x o hf hx ho)

/-- **`AcceptedS` at "the segment is shut".** -/
theorem K9Ends.acceptedS (H : K9Ends T e z c Z l Lk p Q bE bS)
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (front : ∀ a s, T.form z (a, s) = true → s.failed = none)
    (ready : ∀ κ s m En, ThrS T Said z κ s m En → fall z s [] = none → ∃ L, s.link? = some L) :
    AcceptedS T Said fall z := by
  intro blk hblk κ s m En ds y cols hT hd _ hfall hM
  rw [H.bsS] at hblk
  cases hblk
  obtain ⟨rfl, rfl, rfl⟩ := quiet_step T bS H.seat.quiet.2.2.1 κ m En ds y cols hd hM
  have hf := front _ s hT.1.2.2.1.1
  obtain ⟨L, hL⟩ := ready κ s m En hT hfall
  refine ⟨s.putLink (Desc.K9.closed L L.check.frame), hM, ?_⟩
  exact H.seat.stepS T.ft s _ (shut_yes s L hf hL)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_yes_iff
#print axioms ProofFile.Honest.K9.shut_yes_iff
#print axioms ProofFile.Honest.K9.eq_yes
#print axioms ProofFile.Honest.K9.shut_yes
#print axioms ProofFile.Honest.K9.step_noRound
#print axioms ProofFile.Honest.K9.SeatedClose.stepE
#print axioms ProofFile.Honest.K9.SeatedClose.stepS
#print axioms ProofFile.Honest.K9.K9Ends.acceptedE
#print axioms ProofFile.Honest.K9.K9Ends.acceptedS
