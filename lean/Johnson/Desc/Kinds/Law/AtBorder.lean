-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AtBorder.lean.
WHAT IT DOES NOT SHOW. No soundness. No table, no piece, no meaning of a table's items: these are
other files'. Of the four tests with code on the record in front of the output head's block
(Law/K6OnB.lean) two are paid here from tests that run or from a promise that rides; TWO STAY WITH
OTHER FILES: wellLaidB (the ledger's three lists have the plan's count: whoever lays and turns the
ledger in front) and cEndB (the lookup's last claim's numbers are filled: the lookup's block).
OBJECT. Stored/HeadAddsAtS.lean's seatedClaims W l ms; Law/K6OnB.lean's planB, startB, tokenB.
USER. A rule that ties the output head's block into a chain of promises and takes planB W and these
Bools as premises on the plan and on a table's public items.
WHAT IT IS. THE KIND K6's OWN TESTS WITH CODE, PAID WHERE THEY CAN BE PAID AT THE SEATED BLOCK.
  planB_seated      the two tests on the plan: from the seated block's own test on the plan.
  startB_start      the test on the request: from the record's own test at the kind's numbers.
  startB_seated     so: WHERE THE SEATED BLOCK's STEP GOES ON, it held in front: no item of a table
                    need bring it.
  startB_yes        the same from a yes of the seated decision.
  tokenB_small      the test on the heard token: from TokSmall (Law/TokenSmall.lean): the next
                    token's block makes it, every step that leaves the reply keeps it.
  k6OnB_seated      at a yes: K6OnB W s follows from wellLaidB, TokSmall and cEndB alone.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6OnB
import Johnson.Desc.Kinds.Law.TokenSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open OnBytes

/-- **The two tests on the plan, from the seated block's own.** -/
theorem planB_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true) :
    planB W = true := by
  obtain ⟨hok, hl⟩ := seatedClaims_plan h hp
  rw [laidOk_is] at hl
  unfold planB
  rw [Bool.and_eq_true]
  exact ⟨hok, decide_eq_true (laid_says _ _ hl).1⟩

/-- The test on the request, from the record's own. -/
theorem startB_start (W : Model.Verify.Public) (s : S) (h : startOk W s = true) :
    startB W s = true := start_pays W s h

/-- **Where the seated block's step goes on, the test on the request held in front.** -/
theorem startB_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hs : b.step ft s rs cols = .ok (s', n)) :
    startB W s = true := by
  obtain ⟨_, _, _, h4⟩ := seated_step h hs
  exact startB_start W s h4

/-- The same from a yes of the seated decision. -/
theorem startB_yes {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    startB W s = true := by
  obtain ⟨b0, _, rfl⟩ := seatedClaims_some h
  exact startB_start W s ((tested_decide _ _ _ _ _ _ _ _).1 hd).2

/-- **The test on the heard token, from the promise that rides.** -/
theorem tokenB_small (W : Model.Verify.Public) (s : S) (h : TokSmall W.hS.V s) :
    tokenB W s = true := (Came.tokenB_iff W s).2 (tokSmall_pays W s h)

/-- **At a yes: the four tests on the record in front, from three.** -/
theorem k6OnB_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s')
    (h1 : wellLaidB ((seatAt W.hS (readsOf W)).ledger s) = true) (h3 : TokSmall W.hS.V s)
    (h4 : cEndB W s = true) : K6OnB W s = true := by
  unfold K6OnB
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, startB_yes h hd⟩, tokenB_small W s h3⟩, h4⟩

end VerifiableInference.Desc.Kinds.Head.Law
