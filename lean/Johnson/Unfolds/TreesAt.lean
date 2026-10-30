-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/TreesAt.lean: the value of `Johnson.G.OfPlan.treesSent` AT EVERY NAME, from: the
`mapM` of `sentAt` returns (at the empty name); the sorted trees' rounds are a list rs of numbers;
two tests on rs alone.

Definitions.
  `sentsOf c off`: what `sentAt` returns at a chain's sendings; the empty list where it refuses one.
  `rootsC es rs`: `rootsB` (Johnson/Unfolds/TreesLaw.lean) on the list of the trees' rounds alone.
Statements. General in the chain, the plan, the entries, the offset, the extra trees and the name.
  `ok_of_isOk`: what returns is `.ok` of what it holds.
  `rootsB_eq`: `rootsB es ts = rootsC es (ts.map (·.round))`.
  **`trees_at`**: `treesW`'s value. **`treesSent_at`**: `treesSent`'s, at a plan with these rounds
    and that offset.

Limits. THE FIVE FACTS (hs, hr, hc, hn, hb) AND THE TWO ON THE PLAN (he, ho) ARE PREMISES. `rootsC`
counts over all of rs at every round: measured outside this tree, at the proof file's first chain
(48,293 rounds, 83 numbers), its evaluation in Lean's kernel was ended by a cap on memory of 8 GiB;
Johnson/Unfolds/WalkRoots.lean gives it from one walk. No closed fact. Nothing on soundness.

-/
import Johnson.Unfolds.TreesLaw
import Johnson.Unfolds.ToldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Johnson.G Johnson.G.OfPlan

/-- What returns is `.ok` of what it holds. -/
theorem ok_of_isOk {ε α : Type} {x : Except ε α} (d : α) (h : x.isOk = true) :
    x = .ok (x.toOption.getD d) := by
  cases x with
  | error e => cases h
  | ok a => rfl

/-- What `sentAt` returns at a chain's sendings; the empty list where it refuses one. -/
def sentsOf (c : ChainSends) (off : Nat) : List (List Sent) :=
  ((c.sends.mapM (sentAt "" c.codes off)).toOption).getD []

/-- `rootsB` on the list of the trees' rounds alone. -/
def rootsC (es : List Fmt.Entry) (rs : List Nat) : Bool :=
  es.zipIdx.all fun e => rs.count e.2 == e.1.roots

/-- `rootsB` reads of the trees their rounds alone. -/
theorem rootsB_eq (es : List Fmt.Entry) (ts : List Sent) :
    rootsB es ts = rootsC es (ts.map (·.round)) := by
  unfold rootsB rootsC List.count
  simp only [List.countP_map]
  rfl

/-- **`treesW`'s value at every name.** -/
theorem trees_at {c : ChainSends} {es : List Fmt.Entry} {off : Nat} {extra : List Sent}
    {rs : List Nat} {n : Nat} (hs : (c.sends.mapM (sentAt "" c.codes off)).isOk = true)
    (hr : (sortedW (sentsOf c off) extra).map (·.round) = rs) (hc : rootsC es rs = true)
    (hn : es.length = n) (hb : (rs.all fun r => decide (r < n)) = true) (at_ : String) :
    treesW at_ c es off extra = .ok (sortedW (sentsOf c off) extra).zipIdx := by
  refine treesW_of (sent_any_name (ok_of_isOk [] hs) at_) ?_ ?_
  · rw [rootsB_eq]
    show rootsC es ((sortedW (sentsOf c off) extra).map (·.round)) = true
    rw [hr]
    exact hc
  · have h : ((sortedW (sentsOf c off) extra).all fun t => decide (t.round < es.length)) =
        ((sortedW (sentsOf c off) extra).map (·.round)).all fun r => decide (r < es.length) := by
      rw [List.all_map]
      rfl
    show ((sortedW (sentsOf c off) extra).all fun t => decide (t.round < es.length)) = true
    rw [h, hr, hn]
    exact hb

/-- **`treesSent`'s value at every name**, at a plan with these rounds and that offset. -/
theorem treesSent_at {c : ChainSends} {P : Fmt.Plan} {es : List Fmt.Entry} {off : Nat}
    {extra : List Sent} {rs : List Nat} {n : Nat} (he : P.rounds = es)
    (ho : P.entries.length - P.rounds.length = off)
    (hs : (c.sends.mapM (sentAt "" c.codes off)).isOk = true)
    (hr : (sortedW (sentsOf c off) extra).map (·.round) = rs) (hc : rootsC es rs = true)
    (hn : es.length = n) (hb : (rs.all fun r => decide (r < n)) = true) (at_ : String) :
    treesSent at_ c P extra = .ok (sortedW (sentsOf c off) extra).zipIdx := by
  rw [treesSent_eq, ho, he]
  exact trees_at hs hr hc hn hb at_

end Johnson.Unfolds

#print axioms Johnson.Unfolds.ok_of_isOk
#print axioms Johnson.Unfolds.rootsB_eq
#print axioms Johnson.Unfolds.trees_at
#print axioms Johnson.Unfolds.treesSent_at
