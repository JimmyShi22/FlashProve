-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/SeatBinders.lean: the premises on numbers and on the plan that K14's files' top for the
shared chain's ledger (ledger_whole, ledger_at_cap) takes at its parameters Q and its written list
Wr, in one structure under that top's own names, AT THE SEAT: Q := p14Of Z.p.chains (beforePointOf
N), Wr := the proof file's written list of the shared chain, from Written Z x
(Johnson/Goal/Numbers/WrittenAtZ.lean); and
at a key file's typed parameters.
  SeatBinders fl work Q Wr sentU rad2 rad5: hUw, hC2, hC5, hIx, hKR, hN64, hOB, hsL, hok, hm, hl,
      hS, ha, hix, hroom
  four_real, four_key: the four plain tests on the shape and the codes (the shape's own test, the
      masks ahead, the codes' lengths, the split): Lean's kernel
  binders_typed: at ⟨recordSet, .shared, codesFull2, x.shape, 0, bp⟩, every bp that is not empty
  seat_binders: at the seat, from Written Z x
  binders_key: at ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩

What is not claimed. Written Z x (its payers: WrittenOfPins.lean). The ties of the pieces'
written rounds to the written list (hdW, t2, t4, t5, t7): another row. The number of slots. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.WrittenAtZ
import Johnson.Goal.Numbers.K14OwnAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G
open VerifiableInference.Desc.K1
open Lk6.AtPlan (keyFull)

/-- **The top's premises on numbers and on the plan**, under its own names. -/
structure SeatBinders (fl work : ℕ) (Q : P14) (Wr : Rounds) (sentU : Array OracleNotice)
    (rad2 rad5 : ℕ → ℕ) : Prop where
  hUw : withU Q.S = some sentU
  hC2 : condPort (parU Q sentU) rad2 = true
  hC5 : condPort (parO Q) rad5 = true
  hIx : indexB Q.par.S = true
  hKR : K14Rounds Q.S Wr recordRadius cMax work
  hN64 : pointNB Q.S Wr cMax64 64 = true
  hOB : OursBelow Q Wr sentU rad2 rad5
  hsL : sendsLB fl ⟨Q.set, Q.scope, Q.codes, Q.S, 0, [(1, 0)]⟩ Wr = true
  hok : Q.S.ok = true
  hm : Q.par.S.masksAhead = true
  hl : Q.codes.lengthsOk = true
  hS : Q.S.sharedSplitNeeded = true
  ha : Q.par.S.fold.index.code.logN ≤ 32
  hix : Q.par.S.fold.index.ok = true
  hroom : Q.par.S.matrixRows * 2 ^ Q.par.S.kLo ≤ Q.par.S.fold.index.plain

/-- The four plain tests. -/
def fourB (cs : Codes) (S : LinShape) : Bool :=
  S.ok && S.masksAhead && cs.lengthsOk && S.sharedSplitNeeded

theorem four_real : (realSized.any fun p => fourB p.2 p.1.shape) = true := by decide +kernel

theorem four_key : fourB keyFull.codes keyFull.once.shape = true := by decide +kernel

/-- From the pieces. -/
theorem binders_of {fl work : ℕ} {set : Setting} {scope : Scope} {codes : Codes} {S : LinShape}
    {Wr : Rounds} {item : ℕ} {bp : List (ℕ × ℕ)}
    (hc : K14Cond fl ⟨set, scope, codes, S, item, bp⟩ Wr)
    (ho : OursAt ⟨set, scope, codes, S, item, bp⟩ Wr) (hi : indexB S = true)
    (hr : K14Rounds S Wr recordRadius cMax work) (h64 : pointNB S Wr cMax64 64 = true)
    (hs : sendsLB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ Wr = true)
    (hp : fourB codes S = true) :
    ∃ sentU rad2 rad5, SeatBinders fl work ⟨set, scope, codes, S, item, bp⟩ Wr sentU rad2 rad5 := by
  obtain ⟨sentU, rad2, rad5, a1, a2, a3, a4⟩ := ho
  unfold fourB at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hp
  exact ⟨sentU, rad2, rad5, a1, a2, a3, hi, hr, h64, a4, hs, p1, p2, p3, p4, hc.ha, hc.hi,
    hc.hroom⟩

/-- **At the typed parameters of a proof file.** -/
theorem binders_typed : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ (item : ℕ) (bp : List (ℕ × ℕ)), bp ≠ [] → ∃ sentU rad2 rad5,
      SeatBinders 2 28 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1
        sentU rad2 rad5 := by
  obtain ⟨x, a1, -, a3⟩ := k14_real
  obtain ⟨x1, b1, -, b3⟩ := ours_real
  obtain ⟨x2, c1, -, -, c4⟩ := k14_rounds_real
  obtain rfl := sized_one a1 b1
  obtain rfl := sized_one a1 c1
  have hi := index_real
  have h64 := real_test64
  have hs := real_testL
  have hp := four_real
  rw [a1, Option.any_some] at hi h64 hs hp
  exact ⟨x, a1, fun item bp hbp =>
    binders_of (a3 item bp hbp) (b3 item bp hbp) hi c4 h64 hs hp⟩

/-- **At the seat.** -/
theorem seat_binders {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) {N : H2U.Places4} (hN : H2U.placesOfMade Z.made = .ok N) :
    ∃ sentU rad2 rad5, SeatBinders 2 28 (p14Of Z.p.chains (Desc.K14.beforePointOf N))
      dryProofFull.2.1 sentU rad2 rad5 := by
  obtain ⟨x', a1, a2⟩ := binders_typed
  obtain rfl := sized_one hx a1
  have e : p14Of Z.p.chains (Desc.K14.beforePointOf N) =
      ⟨recordSet, .shared, codesFull2, x.shape, 0, Desc.K14.beforePointOf N⟩ := by
    unfold p14Of
    simp only [h.set, h.codes, h.shape, h.batch, Bool.false_eq_true, if_false]
  rw [e]
  exact a2 0 _ (h.before N hN)

/-- **At the typed parameters of a key file.** -/
theorem binders_key (item : ℕ) (bp : List (ℕ × ℕ)) (hbp : bp ≠ []) : ∃ sentU rad2 rad5,
    SeatBinders 0 32 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩
      dryKeyFull.2.1 sentU rad2 rad5 :=
  binders_of (k14_key item bp hbp) (ours_key item bp hbp) index_key k14_rounds_key key_test64
    key_testL four_key

end Desc.K14.Law

#print axioms Desc.K14.Law.four_real
#print axioms Desc.K14.Law.four_key
#print axioms Desc.K14.Law.binders_of
#print axioms Desc.K14.Law.binders_typed
#print axioms Desc.K14.Law.seat_binders
#print axioms Desc.K14.Law.binders_key
