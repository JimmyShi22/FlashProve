-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/RoundsOfPlanLink.lean: the declared rounds of the entry file's one chain, from the three
public files: the third file of the rule of Johnson/G/RoundsOfPlan.lean, whose head says "The entry
file's chain is not made".

What is made. `declLOf pol lay KL`: for each round of the entry file's chain its plan's entry, the
stored tables' parts that it reads and the trees that it opens. The entries are those of the plan
that `Model.Verify.planned` returns. What each round of positions opens is a rule of this file
(`linkOpens`), in the make of that file's `sharedOpens`: the first round of positions ("LINK") opens
no tree and two stored tables: item 0 at the draws 0 … columnsFirst, item 1 at the next
columnsFurther (the link's shape's numbers); the next opens the tree(s) of the link's one message;
each further one the tree of one code switch of the link's test, in order.
What it calls. No dry run and no block of the verifier program is called: it calls
`Model.Verify.planned`, `sendsOf` (Johnson/G/Sends.lean: by its own head a reading of the verifier's
text, with no theorem), and the general pieces of RoundsOfPlan.lean as they are: `treesSent`,
`ownAt`, `switchOpens`, `fill`, `noStored`, `refusal`.
Two borrowed names. `treesSent` knows a sending by `sendTag` of its label, and `sendTag` has no word
for the entry chain's two labels ("the link's message"; "the link's test, the code switch of stage
i"). So the two labels are re-spelt in front of the call (`borrowed`) as the shared chain's ("the
folded row"; "the folded row's test, …"), whose tags this file then reads. Any other label is left
as it is: `treesSent` refuses it if `sendTag` does not know it; the shared chain's own two spellings
would pass for the link's; any other known label gives a tree that is opened nowhere, and is refused
there. The clean cure is two tags more in `SendTag`.
It refuses, with words: where the list of sendings has not seven chains; a label is unknown; a round
gets another number of trees than its entry has roots; the rounds that draw positions are not as
many as the lists; a round of positions would open nothing; a tree that the chain sends would be
opened nowhere (as `fileOf`'s last test).
Limits. All Limits of the head of RoundsOfPlan.lean hold here, "The hash" above all. That the rule
is right is not proved: it was compared by value once, outside the library, with the link's rounds
of the declared structure (`Params.declared`, which a dry run of the verifier program makes), at the
public files of two stored examples (24 and 41 rounds); no test that a build runs holds it. A mask
that a fold of the link's test sends itself (a root at "FOLD epsilon") is not made: `treesSent`
refuses such a plan by its count. Nothing on soundness.

-/
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan

open OnBytes OnBytes.Params OnBytes.Maker

/-- The entry chain's two labels, re-spelt as labels that `sendTag` knows: see the head. -/
def borrowed (label : String) : String :=
  if label == "the link's message" then "the folded row"
  else match label.splitOn "the link's test, " with
    | ["", rest] => "the folded row's test, " ++ rest
    | _ => label

/-- What the rounds of positions of the entry file's chain open, in order, with the two stored
tables. -/
def linkOpens (S : LinkShape) (ts : List (Sent × Nat)) : List (List Told × List Fmt.Stored) :=
  ([], [⟨S.table.tree, S.table.saltBytes, 0, 0, S.columnsFirst⟩,
        ⟨S.table.tree, S.table.saltBytes, 1, S.columnsFirst, S.columnsFurther⟩]) ::
  noStored ((ts.filter fun t => t.1.tag == .foldedRow).map (ownAt 0) :: switchOpens 0 .folded ts)

/-- The entry file's chain, of its shape, plan and sendings. -/
def linkOf (S : LinkShape) (P : Fmt.Plan) (c : ChainSends) :
    Except String (List Fmt.DeclaredRound) := do
  let ts ← treesSent "entry file"
    { c with sends := c.sends.map fun x => { x with label := borrowed x.label } } P []
  let D ← fill "entry file" P.rounds (linkOpens S ts)
  let told := (D.flatMap (·.opens)).filterMap fun o => match o.2 with
    | .own n => some n
    | .taken _ _ => none
  match ts.find? fun t => !told.contains t.2 with
  | some t =>
    throw (refusal "entry file" s!"tree {t.2}, from 0, would be opened nowhere in the file")
  | none => pure D

/-- **The declared rounds of the entry file's chain**, from policy.txt, layout.txt and KL.bin. -/
def declLOf (pol lay KL : ByteArray) : Except String (List Fmt.DeclaredRound) := do
  let p ← OnBytes.Model.Verify.planned pol KL (some lay)
  match ← sendsOf pol lay KL with
  | [_, _, _, e, _, _, _] => linkOf p.chains.link.link p.chains.link.given.plan e
  | _ => throw "the list of sendings has not seven chains (key 0 1 2, entry, proof 0 1 2)"

end Johnson.G.OfPlan
