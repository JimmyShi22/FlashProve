-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/BookBentD.lean: NEGATIVE TESTS FOR THE TESTS ON THE PLAN FOR THE TREES'
TENANTS AND OPENINGS (`BookPlan.allClausesHold`, Johnson/Desc/BookPlan.lean: eleven clauses) at the closed
description of a key file's protocol at the full size (`WK`, Johnson/HB/LLHARD/KB4/WK.lean) and the
written declared rounds (`declKeyFull`, Johnson/HB/LLHARD/KB8/Written.lean). That each clause
accepts there is Johnson/HB/LLHARD/KB4/CBook.lean's. Here one thing that a clause is about is bent,
and all eleven are asked again: so it is seen that the clause can reject, and which of the others
reject with it. By evaluations in Lean's kernel (`decide +kernel`).

  Bent in the declared rounds, each at the third chain's round that opens three trees (`a_bendD3`,
    Johnson/HB/LLHARD/KB9/BookBent.lean): `bent_told`: its last opening names a tree that the shared
    chain does not send: "told" rejects, and "inTime" with it (no round sends that tree). By the
    clauses' texts "told" never rejects alone: an opened tree that is not told is either sent by no
    round ("inTime" rejects) or sent and not told ("allTold" rejects). That is a reading; no
    theorem says it. `bent_range`: all its openings state trees of depth 99: "range" alone.
    `bent_once`: it opens the multiplicities' tree too, which holds a tenant without an
    out-of-domain sample and is opened by the ranges' test already: "once" alone. `bent_inOrder`:
    its openings in the reverse order: "inOrder" alone. And `bent_answered`: the third chain's first
    round takes in one answer more: "answered" alone.
  The two counts: `bent_places`: with the third chain's first block laid twice there are not 35
    places. `bent_oracles`: the three chains' blocks do not tell 6, 11 and 5 oracle messages (the
    count is 6, 11 and 4: `oracles_count`, Johnson/HB/LLHARD/KB4/COracles.lean).

The eleven stand in the order of `BookPlan.clauses`: sum, rows, told, range, alike, oneGroup, once,
answered, sentOraclesMatchEntries, inTime, inOrder. The tenth is asked through its eager twin `inTimeE`
(Johnson/HB/LLHARD/KB4/BeforeE.lean; `inTime_eq` ties the two).

Limits. Negative tests alone: nothing is shown of a key file's description at any public files.
Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.BookBent
import Johnson.HB.LLHARD.KB4.CPlaces
import Johnson.HB.LLHARD.KB4.COracles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open VerifiableInference.Desc VerifiableInference.Desc.BookPlan
open Johnson.KB4 (WK WKtwice oraclesW)
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
/-- There is such a round: else the four bends at it would bend nothing. -/
theorem three_opened :
    (declKeyFull.2.2.filter fun d => d.opens.length == 3).isEmpty = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: the round's last opening takes over tree number 11 of the shared chain, which sends
eleven, numbered from 0. "told" rejects, and "inTime" with it. -/
theorem bent_told :
    a_eleven (a_bendD3 declKeyFull fun d =>
      { d with opens := d.opens.dropLast ++ d.opens.getLast?.toList.map fun o =>
          (o.1, .taken 1 11) }) WK.roots =
      [true, true, false, true, true, true, true, true, true, false, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: the round's openings state trees of depth 99. "range" alone rejects. -/
theorem bent_range :
    a_eleven (a_bendD3 declKeyFull fun d =>
      { d with opens := d.opens.map fun o => ({ o.1 with a := 99 }, o.2) }) WK.roots =
      [true, true, true, false, true, true, true, true, true, true, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: behind its first opening the round opens the first chain's second tree too. "once" alone
rejects. -/
theorem bent_once :
    a_eleven (a_bendD3 declKeyFull fun d =>
      { d with opens := d.opens.take 1 ++ [(⟨22, 77, false, 1⟩, .taken 0 1)] ++ d.opens.drop 1 })
      WK.roots =
      [true, true, true, true, true, true, false, true, true, true, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: the third chain's first round takes in one answer more. "answered" alone rejects. -/
theorem bent_answered :
    a_eleven (declKeyFull.1, declKeyFull.2.1, declKeyFull.2.2.zipIdx.map fun x =>
      if x.2 == 0 then { x.1 with entry := { x.1.entry with answers := x.1.entry.answers + 1 } }
      else x.1) WK.roots =
      [true, true, true, true, true, true, true, false, true, true, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: the round's openings in the reverse order. "inOrder" alone rejects. -/
theorem bent_inOrder :
    a_eleven (a_bendD3 declKeyFull fun d => { d with opens := d.opens.reverse }) WK.roots =
      [true, true, true, true, true, true, true, true, true, true, false] := by decide +kernel

/-- Bent: with the third chain's first block laid twice there are not 35 places. -/
theorem bent_places : (WKtwice.places.length == 35) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The count of the oracle messages that the three chains' blocks tell, with one value moved: not
6, 11 and 5. -/
theorem bent_oracles :
    ((oraclesW.1.length, oraclesW.2.1.length, oraclesW.2.2.length) == (6, 11, 5)) = false := by
  decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.three_opened
#print axioms Johnson.KB9.bent_told
#print axioms Johnson.KB9.bent_range
#print axioms Johnson.KB9.bent_once
#print axioms Johnson.KB9.bent_answered
#print axioms Johnson.KB9.bent_inOrder
#print axioms Johnson.KB9.bent_places
#print axioms Johnson.KB9.bent_oracles
