-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/ClaimFitsStatement.lean: IN FRONT OF THE MERGE THE CLAIM THAT IS LAID FITS
THE LAYOUT: at every state that is reached at border 346 of the first chain's flat list by the
sub-protocols' own steps, under the library's hypothesis on the public files (`P5J.AtMgA`) at the
full size: A STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it
is none of the library's goals: it is a lemma's statement.

Why. `claimFits` (Johnson/Desc/First/Fork/MergeKind.lean: the layout has the claim's unit; one
factor for each of the unit's index groups; each factor has its group's sizes) is one of the twelve
clauses of "the state is ready" (`MergeReady`,
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedStatement.lean, a file that is not in this library),
and a test of the merge's own hearing.

Limits. "Reached" is a premise: that any state is reached is not said. The hypothesis is a premise;
it stands at the earlier hash. On the sizes alone: nothing on what the claim says. Nothing on any
property.
-/
import Johnson.Desc.K11.Front.FilledStatement
import Johnson.Desc.First.Fork.MergeKind
import Johnson.K11R.AtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def ClaimFitsRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF : S) (a : HeadOwn) (claim : WsClaim),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    sF.here = .head a → a.claim = some claim →
    claimFits (K11.parOf Zp Bs.G₀).lay claim = true

end Johnson.Desc.First.ForkMerge.Front

#print axioms Johnson.Desc.First.ForkMerge.Front.ClaimFitsRaw
