-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/Before.lean: for the kind «lookup» (K3) at a place of the proof's first
chain: which oracle messages must have been sent before the lookup's first draw (the shift): the
block's field `before` (Johnson/Desc/Block.lean). Definitions with code; no theorem; nothing is
evaluated in this file.

What it is for. A lookup's first condition of soundness is an order: the arrays that the keys read,
the planes of the counts' bits and the link's mask row are committed before the shift is drawn. The
file's description tests a block's `before` against the plan (`FileDescription.beforeOk`): every message
that is named there is sent in a round not later than the block's first round that draws.

What a member (1, n) is. The first chain's root number n, from 0, in the order of sending: the test
counts along the entries' field `roots`. In the verifier program several oracle messages share a
tree: a prover's message has as many roots as the one rule that lays oracle messages into trees
gives (`Params.treesOf`, OnBytes/Params/DeriveLin.lean, over `layTrees`).

How the numbers are made. `firstSend` and `laterSend` are the planner's own lists of what a link's
prover's messages hold (`Params.reqPlanFrom`: its `sent`; `Params.reqMoments`: its `sent`;
OnBytes/Params/DeriveReq.lean), line for line; `sendsOf` counts their roots by the planner's own
`treesOf`. A link sends once at its start: the message that carries the link before, the kept
messages of earlier links, its own messages of moment 0, the fold's mask; at link 0 also what is
sent at the very start. Then once for each later moment. Nothing else of a link sends a root.
  `beforeAt codes S i false`: the lookup on link i's calls: THE ROOTS OF LINK i's FIRST SEND.
  `beforeAt codes S i true`: the lookup on the digits of the smallness test: THESE, AND THE ROOTS OF
    THE LINK's LAST MOMENT's SEND (the digits and the planes of their counts' bits:
    OnBytes/Model/Tail.lean: rootInH [ZZ, BZ] stands right in front of the lookup).

Limits. TO THE GRAIN OF A TREE: the plan tells no finer. Which arrays each call's keys read is the
calling kinds' key forms' matter and is not read here; that these arrays lie in the link's first
send is not shown. The list may hold more than the lookup leans on (the carrying message; the fold's
mask): a longer list asks more of the plan, never less. Messages of earlier links are not named but
as far as they are kept and sent anew. That the digits' arrays lie in the LAST moment is read off
the program's text, not asked of the layout; at the two stored examples' public files every link was
seen to have three moments, so that the last is the third. AT THE DIGITS THE MIDDLE MOMENTS' ROOTS
ARE LEFT OUT, though they are sent by then: they hold the vector that the reads use (rootInH [iU3]:
OnBytes/Model/Layer.lean, Attention.lean, Head.lean), on which the lookup on the digits is not known
to lean; naming them too would ask more of the plan, never less. The test in
Johnson/Desc/Block.lean is called `beforeAt` as well (`Desc.beforeAt`): a file that opens both
namespaces writes the names in full. It is a function of the first chain's codes and shape
(the parameter bytes' items), which the record `Verify.Public` does not hold. NOT ASKED BY THE TEST
(Block.lean's own Limits): that a message's sample has been answered by then.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Params.DeriveReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Params

/-- What link l's first prover's message holds: `reqPlanFrom`'s `sent`. g: the link's group. msgs:
the link's oracle messages. -/
def firstSend (S : ReqShape) (l : Nat) (g : ReqGroup) (msgs : List ReqMessage) :
    List OracleNotice :=
  let members : List OracleNotice :=
    (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
    (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
    (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
    [foldMaskNotice (ioppFoldShape ⟨S.code, S.maskCode, g.k, g.h⟩ {})]
  if l == 0 then members ++ S.atStart else members

/-- What the prover's message of a later moment holds: `reqMoments`' `sent`. -/
def laterSend (msgs : List ReqMessage) (moment : Nat) : List OracleNotice :=
  (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩

/-- The number of a link's moments, as `reqPlanFrom` has it. -/
def momentsOf (msgs : List ReqMessage) : Nat := (msgs.getLast?.map (·.moment + 1)).getD 0

/-- **The roots of each of link l's sends**, moment by moment. None where there is no such link or
the rule that lays oracle messages into trees refuses. -/
def sendsOf (codes : Codes) (S : ReqShape) (l : Nat) : Option (List Nat) := do
  let g ← (reqGroups S)[l]?
  let link ← S.link[l]?
  let t0 ← treesOf codes (firstSend S l g link.messages).toArray
  let ts ← (List.range (momentsOf link.messages - 1)).mapM fun j =>
    treesOf codes (laterSend link.messages (j + 1)).toArray
  pure (t0 :: ts)

/-- The numbers from a on, n of them, as messages of the first chain. -/
def rootsFrom (a n : Nat) : List (Nat × Nat) := (List.range n).map fun j => (1, a + j)

/-- **What must have been sent before the shift of link i's lookup is drawn.** digits: the lookup on
the digits; else the one on the calls. None where `sendsOf` gives none at a link up to i, or, at the
digits, where the link has one moment alone. -/
def beforeAt (codes : Codes) (S : ReqShape) (i : Nat) (digits : Bool) :
    Option (List (Nat × Nat)) := do
  let earlier ← (List.range i).mapM (sendsOf codes S)
  let base := earlier.foldl (fun a l => l.foldl (· + ·) a) 0
  let mine ← sendsOf codes S i
  let t0 ← mine.head?
  if digits then
    if mine.length < 2 then none else
    let last ← mine.getLast?
    let all := mine.foldl (· + ·) 0
    pure (rootsFrom base t0 ++ rootsFrom (base + all - last) last)
  else pure (rootsFrom base t0)

end VerifiableInference.Desc.First.Look
