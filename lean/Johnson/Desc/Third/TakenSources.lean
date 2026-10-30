-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/TakenSources.lean: a block without a round, in front of the last chain's own
proximity test: the sources of the trees that this chain has not sent. Definitions with code. No
theorem.

This chain has three names: "the last chain" and "the third chain" in these files, "the second
chain" in the format (Johnson/Desc/Block.lean: the field `second`; the refusal "the second chain's
start") and in `verify-on-bytes`.

Why. The own test reads columns of trees that the first chain sent (W's, the index masks', the
mask's) and of one that the shared chain sent (Omega's). A view has no root: the compiler holds each
opening to the root that the declared round's source names. So the decision must ask that the
declared sources are those of the very trees that its book holds.

What the block asks, of the declared rounds of the block `own` that is seated behind it: every
member of the own group, and the mask, has a tree in the book; each such tree is declared as "taken
c n" under the label n, n the tree's number in the book, c = 1 (the shared chain) for the message at
`loc.omega` and c = 0 (the first chain) for every other; no other tree is declared as taken. It
hands the record on. The code does not know who sent a tree: "1 for Omega, 0 for the rest" is right
only if the first chain has sent every other member of the group, and the mask: see Limits (1).

Main names: `opensTaken`, `takenOf`, `takenSources`.

Limits.
(1) That the own group's members beside Omega, and the mask, were all sent by the first chain is not
asked: the block goes over the members as it finds them.
(2) A tree's number in the book is taken for its place in its chain's order of sending, which is how
the format reads the n of "taken c n". The two agree only if the first and the shared chain number
their trees from 0 and count roots in step with the declared rounds. Nothing here asks it.
(3) Which of a round's openings belongs to which tree is not asked. The block asks sets, not order.
In the format every taken tree's columns bear the key 0, and `decide` is handed its groups without
keys: so the tie is the order of `own`'s openings against the order in which `own`'s `decide` reads.
Two trees that one chain reads can have one number: Omega's in the shared chain and an early tree's
in the first chain are both small.
(4) The declared width and depth of a taken tree are not compared with the book's tree's shape.
(5) That the compiler holds an opening to the root that its source names is another file's.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.K14BatchLinearConstraintsSecondPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third

/-- Some round opens, under the label n, a tree with the source "taken c n" (chains from 0). -/
def opensTaken (rounds : List Fmt.DeclaredRound) (c n : Nat) : Bool :=
  rounds.any fun r => r.opens.any fun o => decide (o.2 = Fmt.TreeSource.taken c n) && o.1.tree == n

/-- The trees that the own test reads and this chain has not sent, each as (1 for the message at
loc.omega, 0 for every other; the tree's number in the book): the own group's members', then the
mask's. -/
def takenOf (s : S₃) : Option (List (Nat × Nat)) :=
  (s.st.groups[s.loc.own]?).bind fun G =>
    (G.members.toList ++ s.loc.mask.toList).mapM fun i =>
      ((s.book.place[i]?).bind fun q => s.book.trees[q.1]?).map fun t =>
        (if i == s.loc.omega then 1 else 0, t.number)

/-- **The sources of the trees that are taken over.** No round. own: the block of the request's own
proximity test, which stands behind this one in the chain: the declared rounds that are read are
own's. -/
def takenSources {Cl : Type} (own : Block S₃ Cl) : Block S₃ Cl :=
  roundlessBlock "the taken trees' sources" 3 none 1 fun s => do
    let ts ← named "every member of the own group, and the mask, has a tree in the book" (takenOf s)
    need "every such tree is declared as taken from the chain that sent it"
      (ts.all fun x => opensTaken own.rounds x.1 x.2)
    need "no other tree is declared as taken"
      ((own.rounds.flatMap (·.opens)).all fun o =>
        match o.2 with
        | .own _ => true
        | .taken c n => ts.contains (c, n))
    pure s

end VerifiableInference.Desc.Third
