-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/CountStatement.lean: IN FRONT OF THE MERGE THE LEDGER's NEXT FREE NUMBER,
WITH THE 2 lk + 3 THAT THE MERGE TAKES, IS THE KIND's NUMBER OF SLOTS: at every state that is
reached at border 346 of the first chain's flat list by the sub-protocols' own steps, under the
library's hypothesis on the public files (`P5J.AtMgA`) at the full size: STATEMENTS ALONE: two
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's
goals: they are lemmas' statements.

Why. Behind its hearing the merge's decision asks that the next free slot be the plan's number of
slots (Johnson/Desc/First/Fork/MergeKind.lean: "the merge: the next free slot is not the plan's
number of slots"). So "the count" is one of the twelve clauses of "the state is ready"
(`MergeReady`, Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedStatement.lean, a file that is not in
this library). No sum over the sub-protocols of the head's link is wanted for it: the lookup's own
decision holds the ledger's next number against the plan's (`decide_first`,
Johnson/Top/H/K3DecideMore.lean), and number 345 is a lookup.

  `StatedYesHeadAt` `stated_yes_head` (Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean) with one end
                    more: the parameters of the bare lookup are the public data's own for that
                    link's digits (`placeAt`)
  `CountRaw`          whatever own part a the state at 346 holds: a.F.next + 2 * lk + 3 = nMsg

Limits. "Reached" is a premise: that any state is reached is not said. The hypothesis is a premise;
it stands at the earlier hash. AT THE FULL SIZE's WRITTEN NUMBERS ALONE. Nothing on any property.
-/
import Johnson.Desc.K11.Front.FilledStatement
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.K11R.AtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Block Place K3.theStated K3.pieceAt K3.isHead K3.block
  K3.seatDigits K3.quietHead K3.Readers)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The statement on the lookup on the digits at the head's link. The letters: those of
`stated_yes_head`. Not proved here; a lemma's statement, none of the library's goals. -/
def StatedYesHeadAt : Prop :=
  ∀ (Cl : Type) (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl),
    K3.theStated claim readers X codes shape a = some B → B.planOk = true →
    ∀ i : ℕ, a.link = some i → a.piece = K3.pieceAt X i true → K3.isHead X i = true →
    ∀ (s c : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    B.decide s rs gs = .ok c →
    ∃ P sent laid n gs' m,
      VerifiableInference.Desc.First.Look.placeAt X i true = some P ∧
      (K3.block (K3.seatDigits claim) a.piece laid sent P []).decide s (rs.take n) gs' = .ok m ∧
      K3.quietHead X m = .ok c

/-- The statement on the count. Not proved here; a lemma's statement, none of the library's goals.
-/
def CountRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF : S) (a : HeadOwn),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    sF.here = .head a →
    a.F.next + 2 * (K11.parOf Zp Bs.G₀).lay.lk + 3 = (K11.parOf Zp Bs.G₀).nMsg

end Johnson.Desc.First.ForkMerge.Front

#print axioms Johnson.Desc.First.ForkMerge.Front.StatedYesHeadAt
#print axioms Johnson.Desc.First.ForkMerge.Front.CountRaw
