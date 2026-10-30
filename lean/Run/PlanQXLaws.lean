-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXLaws.lean: the protocol with two stored tables has a local verifier. If own trees have
numbers below 2^16, its wiring obeys the library's laws wherever the wiring without stored tables
does.

1. What the file contains. Five statements about Run/PlanQX.lean's protocol `skeletonOverBothExternalStrings` and wiring
   `wqX`, for every choice C of challenge types (`CK`, Run/PlanQTypes.lean), list ds of rounds,
   depth a, list xs of openings of stored tables, and decision dec. The proofs are in
   Run/PlanQXLawsProofs.lean.
   The protocol is an interactive oracle protocol made from a description of a proof's rounds; it
   reads two stored tables as external strings. Its wiring is the data that say how deep the trees
   are, where a position stands among a tree's leaves, and how blocks of a hash answer give a
   verifier message; the laws of a wiring are the conditions `ProtocolQueryLayout.OKG` (Iop/BatchWire.lean). Own
   trees are the Merkle trees whose roots the prover sends in the proof itself; that they have
   numbers below 2^16 means exactly: every number in a round's list `opens` is below 2^16.
   Many statements of this library are written twice: a definition in the namespace `Spec` states a
   proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

2. What is checked when the file compiles. Only the types.

3. Theorems stated.
   `okX_own`: okX ds a xs = true → every own tree that is opened has a number below 2^16 (from 2^16
     on are the keys of stored columns).
   `weX_ok`: the wiring of the two strings obeys the laws of an external wiring (Iop/Wire.lean:
     `WireE.OK`). By the library's `WireE.two_ok`: no law reads the flag for pruned sets or the
     depth.
   `xWanted_len`: if own trees have numbers below 2^16, the two strings together are read at no more
     positions than the openings' counts add up to. Why the hypothesis: `xWanted` tells a stored
     column by its key, and an own tree with a number from 2^16 on could be taken for one.
   `psofX_local`: `(skeletonOverBothExternalStrings C ds a xs dec).up.loc.IsLocal` (Iop/InteractiveOracleProof.lean): the decision depends on
     the prover's oracles and on the two external strings only at the positions read. This holds for
     every dec, by the form of the view and of the tests `everyOpeningHasItsDraws` and `symbolsCarryTheirPositions`.
   `wqX_okg`: if own trees have numbers below 2^16 and `(wqS C K chal ds dec₀).OKG`, then
     `(wqX C K chal ds a xs dec).OKG`. The laws of the own trees' wiring are those of
     Run/PlanQS.lean's wiring, unchanged; own reads plus external reads are at most nOpen ds plus
     the sum of the counts; depths.

4. What is not claimed.
   That a whole wiring of the interface obeys the laws (`QueryLayout.OKG`) is not claimed here. Of these
   laws `wqX_okg` is the clause `Lk` on Link's wiring. The whole claim is stated in
   Run/PlanQXDoor.lean (`okgWkX`), under the premises `wL.OKG`, `wL.ext = weX a` and
   `a ≤ wL.maxDepth`.
   That Run/PlanQS.lean's wiring obeys the laws at a given C: Run/PlanQSLaws.lean (`wqS_okg`),
   Run/PlanPull.lean (`planPull_okg`).
   No statement on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQX
import Run.PlanQSLaws

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.Twin (RS PS)

namespace Spec

def okX_own : Prop :=
  ∀ (ds : List RD) (a : Nat) (xs : List XO),
    okX ds a xs = true → ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16

def weX_ok : Prop := ∀ a : Nat, (weX a).OK

def xWanted_len : Prop :=
  ∀ (a : Nat) (ds : List RD) (xs : List XO) (Ds : List _root_.Fmt.Drawn),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) → (xWanted a ds xs Ds).length ≤ (xs.map (·.count)).sum

/-- States that the verifier is local. -/
def psofX_local : Prop :=
  ∀ (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool),
    (skeletonOverBothExternalStrings C ds a xs dec).up.loc.IsLocal

/-- States that the wiring obeys the laws, if own trees have numbers below 2^16 and the wiring `wqS`
of Run/PlanQS.lean obeys them. -/
def wqX_okg : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) (a : Nat)
      (xs : List XO) (dec dec₀ : View → Bool),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
    (wqS C K chal ds dec₀).OKG → (wqX C K chal ds a xs dec).OKG

end Spec
end Run.PQ
