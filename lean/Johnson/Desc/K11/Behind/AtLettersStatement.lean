-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Behind/AtLettersStatement.lean: `PromiseBehindStep` (ReachedStatement.lean of this
folder) AT THE LIBRARY's OWN NAMES FOR THE HEAD's LETTERS: P5J.At.N Zp cF · P5J.At.links · P5J.At.ps
for h.𝔇.N · linksFull · psFull: A STATEMENT ALONE: a definition of a proposition: that one's text
with the three names turned. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals:
it is a lemma's statement.

Why. An honest side's frame lays its first chain's letters at these three names and at P5J.mgAtAll
h. That the two triples are one is by definition; here Lean is asked to say so, at the whole
statement.

Limits. Those of `PromiseBehindStep`. Nothing on any property.
-/
import Johnson.Desc.K11.Behind.ReachedStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Behind
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First (S samplesHeld)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def PromiseBehindStepAt : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (blk : Block S ProofFile.Cl)
    (z : ProofFile.InstPub) (s s' : S),
    cF.blocksInOrder[346]? = some blk → IM.Yes 0 blk s s' →
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 346 (z, s) → s.failed = none →
    IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (P1K2.EQ (mgAtAll h) P5J.At.links P5J.At.ps z) 346 s = true →
    samplesHeld (P5J.At.N Zp cF) (mgAtAll h) (IM.openAt P5J.At.links P5J.At.ps 346) (z, s) = true →
    (∀ q ∈ P1K2.pubAt (mgAtAll h) P5J.At.links P5J.At.ps 346, (mgAtAll h).pubP q (z, s)) →
    s'.failed = none ∧
      IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
        (P1K2.EQ (mgAtAll h) P5J.At.links P5J.At.ps z) 347 s' = true ∧
      samplesHeld (P5J.At.N Zp cF) (mgAtAll h) (IM.openAt P5J.At.links P5J.At.ps 347) (z, s') =
        true ∧
      ∀ q ∈ P1K2.pubAt (mgAtAll h) P5J.At.links P5J.At.ps 347, (mgAtAll h).pubP q (z, s')

end Johnson.Desc.First.ForkMerge.Behind

#print axioms Johnson.Desc.First.ForkMerge.Behind.PromiseBehindStepAt
