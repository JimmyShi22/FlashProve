-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsD.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for the merge (K11), number
346. The lemma has the form that `head_hK_of_families` (SteppedYes.lean) takes. The proof calls two
lemmas of the authors of that kind: `headMergeAtFull` (Johnson/Desc/K11/Exchange/AtFull.lean) says
which sub-protocol stands at 346, and `headMergeKeepsYesAtOfStep`
(Johnson/Desc/K11/Returns/KeepsYes.lean) gives the clause from its accepting step. The argument
`P11` of `fHead` is the kind's own `K11.parOf Zp Bs.G₀`, where `Bs` is what `ProofFile.baseOf` returns at
the public part. No definition.

  1  `fHead_keeps_k11`   the lemma

Limits.
  * That a `StepYes` exists at any state is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.Desc.K11.Returns.KeepsYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At the merge, number 346. -/
theorem fHead_keeps_k11 {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ blk, cF.blocksInOrder[346]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take (K11.parOf Zp Bs.G₀) p12 P13 blk.place.kind blk.place s
        s' := by
  intro blk hb s s' hy
  obtain ⟨Bs', Lk, name, hB', -, -, -, -, h346, -⟩ :=
    Johnson.Desc.First.ForkMerge.Exchange.headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  obtain rfl := Option.some.inj (h346.symm.trans hb)
  exact Johnson.Desc.First.ForkMerge.Returns.headMergeKeepsYesAtOfStep 0 _ name IM.k11Place s s' hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k11
