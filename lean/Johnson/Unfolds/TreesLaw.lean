-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/TreesLaw.lean: the value of `Johnson.G.OfPlan.treesSent`
(Johnson/G/RoundsOfPlan.lean) from three facts that hold no array.

Why. `treesSent` fills an array with one counter a round and reads it at every round. At a first
chain of the full size that is an array of 18,851 counters (the key file: `dryKeyFull_length`,
Johnson/G/DryKeyLit.lean) or 48,293 (the proof file: `dryProofFull_length`,
Johnson/G/DryProofLit.lean). Johnson/Unfolds/CountLaw.lean says what that costs Lean's kernel, by
our reading.

Definitions.
  `treesW at_ c es off extra`: `treesSent`'s own text with what it reads of the plan handed in: the
    rounds' entries es, and the number off of the plan's entries that are no rounds.
  `sortedW l extra`: a chain's trees in the order of sending.
  `rootsB es ts`: at every round as many trees of ts as the entry has roots: a count, no array.
Statements. General in the chain, the entries, the offset, the extra trees and the name.
  `treesSent_eq`: `treesSent at_ c P extra` is `treesW` at P's rounds and offset. By `rfl`.
  `find_none`: where `rootsB` accepts, `treesSent`'s search for a round with another number of trees
    finds none.
  **`treesW_of`**: from (hl) what the `mapM` of `sentAt` returns, (hc) `rootsB` accepts the sorted
    trees, (hr) every tree's round lies below the number of rounds: the value is the sorted trees,
    numbered.
Whose text. `treesW` follows `treesSent` (Johnson/G/RoundsOfPlan.lean): this tree's own file.

Limits. THE THREE FACTS ARE PREMISES. No closed fact stands here. Nothing on soundness.

-/
import Johnson.Unfolds.CountLaw
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Johnson.G Johnson.G.OfPlan

/-- `treesSent`'s text with the rounds' entries and the offset handed in. -/
def treesW (at_ : String) (c : ChainSends) (es : List Fmt.Entry) (off : Nat) (extra : List Sent) :
    Except String (List (Sent × Nat)) := do
  let l ← c.sends.mapM (sentAt at_ c.codes off)
  let ts := (l.flatten ++ extra).mergeSort fun a b => a.round ≤ b.round
  let made := ts.foldl (fun (n : Array Nat) t => n.modify t.round (· + 1))
    (Array.replicate es.length 0)
  match es.zipIdx.find? fun e => made.getD e.2 0 != e.1.roots with
  | some e => throw <| refusal at_ <| s!"round {e.2} (\"{e.1.name}\"): the plan's entry has " ++
      s!"{e.1.roots} root(s), but {made.getD e.2 0} tree(s) were found for it"
  | none =>
    unless ts.all fun t => t.round < es.length do
      throw (refusal at_ "a tree was found for a round after the plan's last round")
    pure ts.zipIdx

/-- `treesSent` reads of its plan the rounds' entries and the number of entries that are no rounds.
-/
theorem treesSent_eq (at_ : String) (c : ChainSends) (P : Fmt.Plan) (extra : List Sent) :
    treesSent at_ c P extra =
      treesW at_ c P.rounds (P.entries.length - P.rounds.length) extra := rfl

/-- A chain's trees in the order of sending. -/
def sortedW (l : List (List Sent)) (extra : List Sent) : List Sent :=
  (l.flatten ++ extra).mergeSort fun a b => a.round ≤ b.round

/-- At every round: as many trees as the entry has roots. No array. -/
def rootsB (es : List Fmt.Entry) (ts : List Sent) : Bool :=
  es.zipIdx.all fun e => ts.countP (fun t => t.round == e.2) == e.1.roots

/-- Where `rootsB` accepts, `treesSent`'s search for a round with another number of trees finds
none. -/
theorem find_none (es : List Fmt.Entry) (ts : List Sent) (h : rootsB es ts = true) :
    (es.zipIdx.find? fun e =>
      (ts.foldl (fun (n : Array Nat) t => n.modify t.round (· + 1))
        (Array.replicate es.length 0)).getD e.2 0 != e.1.roots) = none := by
  rw [List.find?_eq_none]
  intro e he
  have hi : e.2 < es.length := by
    exact List.snd_lt_of_mem_zipIdx he
  have hc := List.all_eq_true.1 h e he
  rw [getD_foldl_modify (fun t : Sent => t.round)]
  simp only [Array.size_replicate, hi, if_true]
  have h0 : (Array.replicate es.length 0).getD e.2 0 = 0 := by
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [h0, Nat.zero_add]
  simp only [bne, hc, Bool.not_true]
  exact Bool.false_ne_true

/-- **`treesSent`'s value, from three facts without an array.** -/
theorem treesW_of {at_ : String} {c : ChainSends} {es : List Fmt.Entry} {off : Nat}
    {extra : List Sent} {l : List (List Sent)}
    (hl : c.sends.mapM (sentAt at_ c.codes off) = .ok l) (hc : rootsB es (sortedW l extra) = true)
    (hr : ((sortedW l extra).all fun t => t.round < es.length) = true) :
    treesW at_ c es off extra = .ok (sortedW l extra).zipIdx := by
  have hf := find_none es (sortedW l extra) hc
  unfold sortedW at hf hr ⊢
  unfold treesW
  simp only [hl, bind, Except.bind, hf, hr, ↓reduceIte, pure, Except.pure]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.treesSent_eq
#print axioms Johnson.Unfolds.find_none
#print axioms Johnson.Unfolds.treesW_of
