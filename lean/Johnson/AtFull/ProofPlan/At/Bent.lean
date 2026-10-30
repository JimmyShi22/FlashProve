-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/Bent.lean: THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean) WITH ONE THING TURNED, EIGHT TIMES: for the negative lines of the
tests on the plan. Definitions alone.

Each differs from `WP` in one number, chosen so that one named test must say no. The files under
At/No/ ask Lean's kernel, each alone.

  `wpDepth`: the depth is 31. The one stored part that is opened (a round "LOC" of the shared chain)
    has the depth 32.
  `wpPlans`: the plan's first list is empty.
  `wpSeal`: the first chain's last row declares no round.
  `wpPlaces`: the first chain's second row stands at the first row's place.
  `wpReads`: the first of the distinct declared rounds ("SEND seed", which opens nothing) draws one
    position.
  `wpShaped`: the first chain's third row says that its oracles have one member more than it has
    rounds.
  `wpLabels`: at the distinct declared round number 38 the first opened tree's label says 1; its
    source says: the chain's own tree 0.
  `wpSent`: the first tree that the first chain's third row tells has one word more than the shape
    at its opening.

Limits. Made-up values: none is any description's. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (declRecsFull cutFirstFull cutSharedFull cutSecondFull)
open Johnson.G (dryProofRunsFull0 dryProofRunsFull1 dryProofRunsFull2)
open Johnson.G.Runs (unrunG)

/-- The three lists of declared rounds, of other distinct rounds along the same runs. -/
def declOfRecs (recs : List Fmt.DeclaredRound) :
    List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound :=
  (unrunG recs dryProofRunsFull0, unrunG recs dryProofRunsFull1, unrunG recs dryProofRunsFull2)

def wpDepth : FileDescription Unit := wOf cutFirstFull cutSharedFull cutSecondFull declProofFull 31

def wpPlans : FileDescription Unit := { WP with plans := ([], WP.plans.2.1, WP.plans.2.2) }

def wpSeal : FileDescription Unit :=
  wOf (cutFirstFull.modify 357 fun r => (r.1, r.2.1, 0, r.2.2.2)) cutSharedFull cutSecondFull
    declProofFull 32

def wpPlaces : FileDescription Unit :=
  wOf (cutFirstFull.modify 1 fun r => (r.1, ⟨1, none, 0, .frame⟩, r.2.2)) cutSharedFull
    cutSecondFull declProofFull 32

def wpReads : FileDescription Unit :=
  wOf cutFirstFull cutSharedFull cutSecondFull
    (declOfRecs (declRecsFull.modify 0 fun r =>
      { r with entry := { r.entry with poss := r.entry.poss + 1 } })) 32

def wpShaped : FileDescription Unit :=
  wOf (cutFirstFull.modify 2 fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1 + 1, r.2.2.2.2))
    cutSharedFull cutSecondFull declProofFull 32

def wpLabels : FileDescription Unit :=
  wOf cutFirstFull cutSharedFull cutSecondFull
    (declOfRecs (declRecsFull.modify 38 fun r =>
      { r with opens := r.opens.modify 0 fun o => ({ o.1 with tree := o.1.tree + 1 }, o.2) })) 32

def wpSent : FileDescription Unit :=
  wOf (cutFirstFull.modify 2 fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1,
      r.2.2.2.2.1.modify 0 fun t => (t.1, t.2.modify 0 fun o => { o with words := o.words + 1 }),
      r.2.2.2.2.2))
    cutSharedFull cutSecondFull declProofFull 32

end P2Law.ProofPlan
