-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSlotsK11.lean: THE SLOT OF THE RUN OF CLAIMS "the merge" (kind K11) AT THE
HEAD's LINK OF THE PROOF FILE's OWN FIRST CHAIN (Slot,
Johnson/Desc/First/Batch/Shape/BatchBuild.lean), under the head at which the library's laws on that
chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). A joining of laws; nothing is evaluated.

  `merge_same`, `merge_still`: the run keeps the reply, and leaves the statement, where it returns
    (it lays the head's ledger alone).
  **`k11_slot`**: Bs by baseOf's value · Lk by cF.links[24]?: there is a slot for the pair
    (8, "the merge") of Lk.hear whose bare run IS headMergeClaim, whose law's runG IS mergeRunG and
    whose pre IS fun _ _ => True (another house's Johnson/Desc/K11/Shape/ClaimRun.lean).

Limits. ONE OF THE FIFTEEN RUNS BY KIND AND NAME (1 of the 215 runs). UNDER THE HEAD: that it has a
member is shown at two triples of files alone, in a side library. At the earlier hash. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Batch.Shape.BatchBuild
import Johnson.Desc.K11.Shape.ClaimRun
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open Johnson.Desc.First.ForkMerge.ShapeStep (mergeRunLaw mergeRunG)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem merge_same (n : Nat) (s s' : S) (cs : List Claim)
    (h : headMergeClaim n s = .ok (cs, s')) : ProofFile.sameReply s s' = true := by
  obtain ⟨a, wo, G, -, -, rfl, -, -⟩ := claim_inv h
  unfold ProofFile.sameReply
  exact beq_self_eq_true _

theorem merge_still (n : Nat) (s s' : S) (cs : List Claim)
    (h : headMergeClaim n s = .ok (cs, s')) : s'.st = s.st := by
  obtain ⟨a, wo, G, -, -, rfl, -, -⟩ := claim_inv h
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k11_slot (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ cF.links[24]? = some Lk ∧
      ∃ T : Slot ProofFile.sameReply Lk.hear (8, "the merge"),
        T.bare = headMergeClaim ∧ T.law.runG = mergeRunG ∧ T.law.pre = fun _ _ => True := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, hla, -⟩ := IM.k11_of h.scope h.reads O
  exact ⟨Bs, Lk, O.made, e1,
    { lot := K11.blkAt Zp "H.8.call" Bs.G₀, name := b.name, place := IM.k11Place
      seated := e2.trans (congrArg some hla), bare := headMergeClaim, states := rfl
      law := mergeRunLaw, keeps := merge_same, still := merge_still }, rfl, rfl, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.merge_same
#print axioms Johnson.AtFull.Shape.merge_still
#print axioms Johnson.AtFull.Shape.k11_slot
