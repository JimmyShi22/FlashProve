-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ArmsQuiet.lean: nine clauses of the condition `keeps` of the
first chain leave three things of the verifier's state as they were: the statement (`st`), the book
of trees (`book`) and the rows on the table (`S.rows`). The clauses are those of K3 (three sorts of
lookup), K4, K5, K6, K8, and two of K9's three sorts (the batching, and the sub-protocol that ends a
segment's closing). Each of them writes only into the field `here`; K4's and K5's also into
`rowsOwed`. `ridesPastAt_pile` and `ridesPastAt_row` (RowPileRides.lean), `ridesPastAt_pin` and
`ridesPastAt_pinI` (PinRides.lean) ask just these equations of `keeps`. The lemmas are on two
states; no invariant and no size is named. Kin: `digitsArms_four`, `k3Head_four` (WoKinds.lean) and
`shutKeeps_four` (WoClose.lean) have the first two equations with two others in the place of the
rows; `keeps_rows` (Johnson/Desc/K5/Honest/Law/RidesK5.lean, of other authors) has the rows at K5's
clause without the mark. No definition.

  1  `quiet_set`   a state with other values of `rowsOwed` and `here` has the same three things, if
     neither value of `here` is `Here.mem` (the library's `rows_pile`,
     Johnson/Desc/K13/Law/PileReadsOut.lean: then `S.rows` is the pile)
  2  `putTl_rows`, `putLink_rows`   two of the library's writings leave `S.rows`
  3  `k3Calls_quiet`, `k3Digits_quiet`, `k3Head_quiet`, `k4_quiet`, `k5_quiet`, `k6_quiet`,
     `k8_quiet`, `rest9_quiet`, `shut_quiet`   the nine clauses

Limits.
  * Not treated: the clauses of K1, K2, K7, K10, K12, K13 and of K9's one equation, which let the
    statement or the book change; and K11's, which K11RowPile.lean treats.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps
import Johnson.Desc.ProofFile.Honest.K4.Law.Keeps
import Johnson.Desc.K5.Honest.Law.KeepsM
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.K8.Honest.Keeps
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.First.Link.Law.Rest9
import Johnson.Desc.K13.Law.PileReadsOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.K13.Law (rows_pile rows_not_end)

/-- A state with other values of `rowsOwed` and `here` has the same statement, book and rows. -/
theorem quiet_set (s : S) (ro : Option Nat) (X : Here) (h1 : ∀ a, s.here ≠ Here.mem a)
    (h2 : ∀ a, X ≠ Here.mem a) :
    ({ s with rowsOwed := ro, here := X } : S).st = s.st ∧
      ({ s with rowsOwed := ro, here := X } : S).book = s.book ∧
      ({ s with rowsOwed := ro, here := X } : S).rows = s.rows :=
  ⟨rfl, rfl, by rw [rows_pile (s := { s with rowsOwed := ro, here := X }) h2, rows_pile h1]⟩

/-- `putTl` leaves `S.rows`. -/
theorem putTl_rows (s : S) (tl : _) : (s.putTl tl).rows = s.rows := by
  unfold S.putTl
  split
  next a ha =>
    exact (quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
      (fun b hb => by cases hb)).2.2
  next a ha =>
    exact (quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
      (fun b hb => by cases hb)).2.2
  next a ha =>
    split
    · exact (quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
        (fun b hb => by cases hb)).2.2
    · rfl
  next => rfl

/-- `putLink` leaves `S.rows`. -/
theorem putLink_rows (s : S) (L : _) : (s.putLink L).rows = s.rows := by
  unfold S.putLink
  split
  next a ha =>
    exact (quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
      (fun b hb => by cases hb)).2.2
  next a ha =>
    exact (quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
      (fun b hb => by cases hb)).2.2
  next a ha =>
    split
    · exact (quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
        (fun b hb => by cases hb)).2.2
    · rfl
  next => rfl

/-- K3, the lookup on the calls. -/
theorem k3Calls_quiet {sh : _} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsCalls sh s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  obtain ⟨-, F, Hd, G, -, hc, -⟩ := k
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, ha, -, rfl⟩ <;>
    exact quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
      (fun b hb => by cases hb)

/-- K3, the lookup on the digits in a segment other than the output head's. -/
theorem k3Digits_quiet {sh : _} {claims : Nat} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsDigits sh claims s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  obtain ⟨-, tl, F, Hd, G, -, -, hc, -⟩ := k
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, ha, -, rfl⟩ <;>
    exact quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
      (fun b hb => by cases hb)

/-- K3, the lookup on the digits in the output head's segment. -/
theorem k3Head_quiet {sh : _} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsHead sh s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  obtain ⟨-, tl, F, Hd, G, a, claim, -, -, ha, -, rfl, -⟩ := k
  exact quiet_set s s.rowsOwed _ (fun b hb => by rw [ha] at hb; cases hb)
    (fun b hb => by cases hb)

/-- K4. -/
theorem k4_quiet {s s' : S} (k : ProofFile.Honest.K4.K4Keeps s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  obtain ⟨R, a, G, o, ha, -⟩ := k
  obtain ⟨a', ha', -⟩ := R.here a ha
  refine ⟨R.st, R.book, ?_⟩
  exact rows_not_end (fun b hb => by rw [ha] at hb; cases hb)
    (fun b hb => by rw [ha'] at hb; cases hb) R.out

/-- K5. -/
theorem k5_quiet {x : _} {s s' : S}
    (k : H2K5.Honest.K5KeepsM x s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  obtain ⟨-, a, hd, G, rs, ha, -, rfl⟩ := k
  exact quiet_set s none _ (fun b hb => by rw [ha] at hb; cases hb) (fun b hb => by cases hb)

/-- K6. -/
theorem k6_quiet {s s' : S} (k : VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  have e := k.here
  obtain ⟨-, -, o, o', ho, ho', -⟩ := k
  rw [e]
  exact quiet_set s s.rowsOwed _ (fun b hb => by rw [ho] at hb; cases hb)
    (fun b hb => by rw [ho'] at hb; cases hb)

/-- K8. -/
theorem k8_quiet {s s' : S} (k : VerifiableInference.Desc.First.K8.Honest.K8Keeps s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows :=
  ⟨k.rest.1, k.rest.2.1, k.leaves S.rows putTl_rows⟩

/-- K9, the batching: two states that are alike but for what K9's three sub-protocols write. -/
theorem rest9_quiet {L₀ : _} {F₀ : _} {t₀ : _} {s s' : S} (hr : s'.rows = s.rows)
    (e : VerifiableInference.Desc.LinkJoin.rest9 L₀ F₀ t₀ s' =
      VerifiableInference.Desc.LinkJoin.rest9 L₀ F₀ t₀ s) :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  have h1 := congrArg S.st e
  have h2 := congrArg S.book e
  exact ⟨h1, h2, hr⟩

/-- K9, the sub-protocol that ends a segment's closing. -/
theorem shut_quiet {s s' : S} (k : ProofFile.Honest.K9.ShutKeeps s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  obtain ⟨L, -, rfl⟩ := k.laid
  refine ⟨?_, ?_, putLink_rows s _⟩
  · unfold S.putLink
    split <;> first | rfl | (split <;> rfl)
  · unfold S.putLink
    split <;> first | rfl | (split <;> rfl)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.quiet_set
#print axioms ProofFile.Honest.FirstThread.putTl_rows
#print axioms ProofFile.Honest.FirstThread.putLink_rows
#print axioms ProofFile.Honest.FirstThread.k3Calls_quiet
#print axioms ProofFile.Honest.FirstThread.k3Digits_quiet
#print axioms ProofFile.Honest.FirstThread.k3Head_quiet
#print axioms ProofFile.Honest.FirstThread.k4_quiet
#print axioms ProofFile.Honest.FirstThread.k5_quiet
#print axioms ProofFile.Honest.FirstThread.k6_quiet
#print axioms ProofFile.Honest.FirstThread.k8_quiet
#print axioms ProofFile.Honest.FirstThread.rest9_quiet
#print axioms ProofFile.Honest.FirstThread.shut_quiet
