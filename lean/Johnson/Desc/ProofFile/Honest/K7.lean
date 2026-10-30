-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7.lean: the honest side of the kind "the next token" (K7), in the
types of Honest/Frame.lean and Honest/Side.lean. The kind's own text does not hold what the prover
sends (Johnson/Desc/Kinds/ReplyKind.lean): this file holds it. Executable definitions; no theorem.

What is sent. One round, one item in the clear: the token that the instance asks about
(`Inst.asked`, Johnson/Desc/ProofFile/Pub.lean), as an element of the extension field. The prover's
side is a list of one part. The part takes no coin, is given no block of another part's coins and
has no stop. Of its input it reads the public instance alone. It passes on the state that was passed
on to it.

  `replyOf`     the element
  `replyPart`   the part
  `replyHalf`   the kind's prover's side: at a link's number and a piece, as in `Reply.kind`
                (Johnson/Desc/Kinds/ReplyBlock.lean); its parameter is the kind's own: the size of
                the vocabulary, which the prover's side does not read
  `replyLot`    the prover's side at the place at which the proof file's description has the kind's
                sub-protocol, under the name of the lot that puts it there (`p4Pure`,
                Johnson/Desc/ProofFile/Lots/PureLots.lean; the sub-protocol: `h1Own`, Lots/H1.lean:
                `P4.k7Core`, which is the kind's sub-protocol under one more named test, after a
                guarded step without a round). The name is that list's, not that of the kind's own
                lot: `P4.k7Lot` has another name and is not among the lots of `onlineFirstChainBlockTables`
  `replySim`    a candidate simulator paired with the part: it takes no coin and computes the same
                item from the public instance
  `replyRow`    the list of the one pair
  `replySide`   the side: that list beside the description's own sub-protocol at the place, taken
                from its list (`Side.seated`): as the description's makers have wrapped it, not the
                lot's definition. It is supplied without a fall: no test of the sub-protocol on
                values involves a challenge

How it can fail. A test program, which is no part of the library (neither its source nor its
printout is in this tree), prints the rows of
Honest/Rows.lean at a stored run: an accepted run of the small example set with synthetic weights.
The part's item is compared with the stored run's, and the description decides on the played views.
Its line for this prover's side: "told 1 of 47 · equal 1 of 1 · idle 0
· the decision: yes · stored columns read: [(0, 53)] · the coins: the stored run's own", and after
it the last note of `Rows.print`: a yes shows nothing of what was taken from the stored run.
Two of its phrases need correcting. "the coins: the stored run's own" is what the program prints
where no prover's side takes a coin: its coins are all 0, and it holds none of the stored run's. The
last note says a little too much: a stored run's column of another width than the round declares is
rejected.
What that line shows: 46 of the 47 senders are played from the stored run; once "equal 1 of 1"
holds, the played views are the stored run's, and the acceptance repeats that of the stored run's
own proof. That line can fail on the place, on the item's class and number, and on the value's
encoding. The program tries each separately: a prover's side one piece further on is rejected; an
element of the base field is rejected; with the token plus 1, and with another token asked, "equal"
is 0 of 1. That line cannot see the size of the vocabulary, the lot's name, `replySim`, `replyRow`
or `replySide`. Other lines of the program check `replySide` (a sub-protocol is at its place; it
fits), the part played alone against the run, `replySim` against the part, and how many of the
description's lots lack an honest side, of all: "(14, 15)", and "(15, 15)" at a misspelt name. At
that run the asked token is not 0 and the run is accepted: so its last position is covered (see the
Limits); a request whose last position is not covered is tried nowhere.

Limits.
  * The element is computed from the instance's asked token, not from a model's output: that the two
    are the same at a true request is not stated here.
  * The part does not keep the range. The asked token is a 32-bit word, and the prover's side does
    not read the size V of the vocabulary: at an instance with asked ≥ V the part sends and the
    kind's decision rejects. This is not made a stop: by type the second stop could read
    the instance, but a stop is a set of challenges with a share, and no challenge is involved here.
    For the same reason it is no fall. It is a hypothesis on the instance and the verifier's state,
    to be supplied by whoever writes the condition A of `Good` at this side: asked < V and nothing
    heard yet (`Reply.decideE`, Johnson/Desc/Kinds/ReplyKind.lean), and what the guarded step before
    it asks of the state.
  * For a whole run's acceptance there is one thing more, which is no hypothesis at this side. Where
    the request's last position is not covered, the last test asks that the asked token is 0
    (`S.finAsked`, Johnson/Desc/First/State.lean): at another token the part sends, the kind's
    decision accepts, and the last test rejects.
  * By type the `bs` of `replySide` is any list of sub-protocols, and nothing ties its link and
    piece to those of `replyLot`.
  * Nothing is said of `Good` at this side.
  * Within the library no `#guard` compares the lot's name with the one in `p4Pure`, and no toy
    example plays the part alone.
  * It shows the form of a kind's part; it has no smaller input or state of its own and no
    `Part.lift`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ Rc Tr X : Type}

/-- The element that is sent: the token that the instance asks about. -/
def replyOf (x : Inst) : Cb.Gl.E := OnBytes.Slice.toE x.asked.triple

/-- **The part**: one round, one element in the clear. -/
def replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ t => .ok ⟨[.e (replyOf t.input.x)], []⟩, fun t => t.own⟩] }

/-- **The kind's prover's side**, at a link's number and a piece. -/
def replyHalf (link piece : Nat) :
    KindHalf Nat (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  fun _ => ⟨⟨1, some link, piece, .K7⟩, [replyPart]⟩

/-- **The lot's honest side**: at the place of the lot's own sub-protocol: piece 1 of the last link.
The name is written a second time here: the lot is in the list of `p4Pure`, which takes the public
part (`Pub`), and is no definition of its own. Nothing here compares the two strings. -/
def replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  { name := "the next token (K7), with the step that enters the head's link"
    halves := fun _ G => [replyHalf (G.built.size - 1) 1 G.W.hS.V] }

/-- A candidate simulator paired with the part, at the same address. -/
def replySim (link piece : Nat) : Sim Inst :=
  { addr := ⟨⟨1, some link, piece, .K7⟩, 0⟩, takes := ⟨0, 0⟩
    tell := fun x _ _ _ _ => some [⟨[.e (OnBytes.Slice.ofE (replyOf x))], []⟩] }

/-- The list: the part with its candidate simulator. -/
def replyRow (link piece : Nat) :
    List (Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × Sim Inst) :=
  [(replyPart, replySim link piece)]

/-- **The side**: the list beside the sub-protocol of a description's first chain that is at the
place; `none` if there is none. `bs`: that chain's list (`Chain.blocksInOrder`). -/
def replySide {S Cl : Type} (bs : List (VerifiableInference.Desc.Block S Cl)) (link piece : Nat) :
    Option (Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) :=
  Side.seated bs ⟨1, some link, piece, .K7⟩ (replyRow link piece)

end ProofFile.Honest
