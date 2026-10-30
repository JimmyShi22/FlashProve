-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.AtFull.Desc.TreesValue
/-
Johnson/Loose/H2K12/K12TreesOf.lean: FOR THE PROXIMITY TEST's (the kind K12's) ROW:
THE VALUE OF Johnson.G.OfPlan.treesSent (Johnson/G/RoundsOfPlan.lean), WHERE IT RETURNS, AS A
ROUTINE THAT DOES NOT WALK THE PLAN's ROUNDS. General; nothing is evaluated here.
WHY. treesSent ends with a check of its own over all rounds of the plan (an array as long as the
plan, grown step by step, read inside a search): at the first chain's 48,293 rounds Lean's kernel
would pay the square of that length (by a reading of its text; not measured). But the VALUE that
it returns hangs on the chain's sendings
alone (82 on the first chain) and on one number of the plan: how many of its entries are no rounds.
  treesOf          that value: the sendings' trees (sentAt), with the extra ones, sorted by their
                   round, numbered. Where sentAt refuses at a sending: the empty list: a default
                   that trees_are never meets
  trees_are        where treesSent at_ c P extra returns ts, and P has off entries that are no
                   rounds: ts = treesOf at_ c off extra. BY ANOTHER FILE's THEOREM, CALLED:
                   Johnson.AtFull.Desc.treesSent_value (Johnson/AtFull/Desc/TreesValue.lean)
WHAT IT IS NOT: it does not say that treesSent returns. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan
open Johnson.G (ChainSends)

/-- **What `treesSent` returns, off the sendings alone.** -/
def treesOf (at_ : String) (c : ChainSends) (off : Nat) (extra : List Sent) : List (Sent × Nat) :=
  match c.sends.mapM (fun x => sentAt at_ c.codes off x) with
  | .ok l => ((l.flatten ++ extra).mergeSort fun a b => decide (a.round ≤ b.round)).zipIdx
  | .error _ => []

theorem trees_are {at_ : String} {c : ChainSends} {P : Fmt.Plan} {extra : List Sent}
    {ts : List (Sent × Nat)} {off : Nat} (h : treesSent at_ c P extra = .ok ts)
    (ho : P.entries.length - P.rounds.length = off) : ts = treesOf at_ c off extra := by
  obtain ⟨l, hl, rfl⟩ := Johnson.AtFull.Desc.treesSent_value h
  rw [ho] at hl
  have hl' : c.sends.mapM (fun x => sentAt at_ c.codes off x) = .ok l := hl
  unfold treesOf
  rw [hl']

end H2K12

#print axioms H2K12.trees_are
