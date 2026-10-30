-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/FilledStatement.lean: IN FRONT OF THE MERGE THE SLOT OF THE CLAIM's VALUE IS
FILLED: at every state that is reached at border 346 of the first chain's flat list by the
sub-protocols' own steps, under the library's hypothesis on the public files (`P5J.AtMgA`) at the
full size: STATEMENTS ALONE: two definitions of propositions. NOTHING IS PROVED IN THIS FILE, and
neither is one of the library's goals: they are lemmas' statements.

Why. "The slot x.sV is filled in the ledger" is one of the twelve clauses of "the state is ready"
(`MergeReady`, Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedStatement.lean, a file that is not in
this library). The library has it BEHIND A YES OF THE OUTPUT HEAD's OWN BLOCK from a well-laid
ledger (`sv_at_yes`, Johnson/Desc/Kinds/Law/SvLaid.lean); its head leaves open "that no block
between H:4 and the merge turns x: the fold's".

  `BackToHeadRaw`   from a state reached at 346 back over five sub-protocols: a yes of the output
                    head's own block from some s, whose ledger is well laid, to some s'; and the
                    state at 346 goes on from s' as far as the library's sentence reads (`KeptW`): x
                    as it was; a later ledger
  `FilledRaw`       whatever own part a and hearing x the state at 346 holds: Filled a.F x.sV

Limits. "Reached" is a premise: that any state is reached is not said. The hypothesis is a premise;
it stands at the earlier hash. WHICH number x.sV is, is not said; nor what lies under it. Nothing on
any property.
-/
import Johnson.Desc.Kinds.Law.WtJointAt
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.P5J.MgAtAll
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes.Model
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head (blockAt seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf KeptW WellLaid)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The statement on the walk back. Not proved here; a lemma's statement, none of the library's
goals. -/
def BackToHeadRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF : S),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    ∃ (s s' : S) (rv : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      (blockAt Bs.G₀.W.hS (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)
        (workOf Bs.G₀.W) 24).decide s rv gs = .ok s' ∧
      WellLaid ((seatAt Bs.G₀.W.hS
        (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)).ledger s) ∧
      KeptW s' sF

/-- The statement on the slot. Not proved here; a lemma's statement, none of the library's goals.
-/
def FilledRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (z : ProofFile.InstPub) (sF : S) (a : HeadOwn) (x : Head.Heard),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    sF.here = .head a → a.x = some x → Filled a.F x.sV

end Johnson.Desc.First.ForkMerge.Front

#print axioms Johnson.Desc.First.ForkMerge.Front.BackToHeadRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.FilledRaw
