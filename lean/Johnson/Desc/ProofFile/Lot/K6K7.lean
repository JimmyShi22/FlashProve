-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K6K7.lean: the blocks that two kinds bring to the proof file's first
chain: the output head's own rounds (K6), at the fourth place in front of the batching of the
head's link, and the next token (K7), at the first place there.

What the file holds.
  headBefore   the oracle messages that must have been sent in front of K6's first draw: those with
               the head's cells and those with the residual stream's, each by its chain and its
               number of sending. It fails closed: its own comment lists the cases.
  k6Hear       K6's block as it is seated: Head.seatedClaims (Johnson/Stored/HeadAddsAtS.lean), with
               that list. It states four runs of claims, typed at Claim: norm, join, policy, logits.
               These are just the names that the driver's order lists at that place, each once
               (Johnson/Desc/Kinds/Law/RunsListed.lean).
  k6Lot        the lot with that block. It takes the public part Z, from which the list is read.
  k7Core       K7's block: Reply.blockOf (Johnson/Stored/ReplySeatAt.lean). It states no run.
  k7Lot        the lot with that block.
  k6Own, k6Seated   K6's block at the unit type, without and with the seat's tests: names for files
               of tests. No lot seats them.
Neither block takes a letter of the instance: K6 reads the request off the carried record; K7 reads
the size of the vocabulary and the link's number.

What it does not give. Nothing on soundness. Definitions alone. That a message that headBefore names
is the one that a later read opens is not shown.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Stored.HeadAddsAtS
import Johnson.Stored.ReplySeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4
open ProofFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Kinds (Head.blockOf Head.seatedOf Head.seatedClaims)

/-- The oracle messages with the head's cells and with the stream's, by chain and number of sending.
It fails closed at every piece: none if there is no last link; if the head's own step names no
message; if the head's link has no foreign tree; if a foreign tree has no owner in the link's table
of arrays; if an owner's link is not among the built ones; or if an owner's link's step names no
message. So a list that is returned names a message for the head's cells and one for every owner. -/
def headBefore (Z : Pub) (G : Ground) : Option (List (Nat × Nat)) := do
  let X ← G.built.back?
  let own := k8Msgs Z (X.name ++ ".1.call")
  let born ← X.tl.ix.FT.toList.mapM fun tree => (X.arrayOf[tree]?).map (·.1)
  let theirs ← born.eraseDups.mapM fun l => (G.built[l]?).bind fun Y =>
    let ms := k8Msgs Z (Y.name ++ ".0.call")
    if ms.isEmpty then none else some ms
  if own.isEmpty || theirs.isEmpty then none else some ((own ++ theirs.flatten).map fun n => (1, n))

/-- K6's block at the unit type, without the seat's tests. A name for files of tests. -/
def k6Own (G : Ground) : List (Block S Unit) := (Head.blockOf G.W (G.built.size - 1)).toList

/-- The same with the seat's tests and the list of messages. A name for files of tests. -/
def k6Seated (Z : Pub) (G : Ground) : List (Block S Unit) :=
  ((headBefore Z G).bind fun ms => Head.seatedOf G.W (G.built.size - 1) ms).toList

/-- **K6's block as it is seated**, its four runs typed at Claim, at the head's link. -/
def k6Hear (Z : Pub) (G : Ground) : List (Block S Cl) :=
  ((headBefore Z G).bind fun ms => Head.seatedClaims G.W (G.built.size - 1) ms).toList

/-- K7's seat at the carried record. -/
abbrev k7Seat : VerifiableInference.Desc.Kinds.Reply.Seat S :=
  VerifiableInference.Desc.Kinds.Reply.seatAt

/-- The named test in front of K7's decision: the head's link is entered and not yet opened. -/
abbrev entered (b : Block S Unit) : Block S Unit := VerifiableInference.Desc.Kinds.Reply.entered b

/-- **K7's block**, without the place's quiet step. -/
def k7Core (G : Ground) : Block S Unit :=
  VerifiableInference.Desc.Kinds.Reply.blockOf G.W (G.built.size - 1)

def k6Lot (Z : Pub) : Lot :=
  { name := "the output head's own rounds (K6)", letters := false, own := fun _ => [],
    hearC := k6Hear Z }

def k7Lot : Lot :=
  { name := "the next token (K7)", letters := false, own := fun G => [k7Core G] }

end P4
