-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/BlockYesAll.lean: THE ONE NAMED PREMISE OF ShapeOfReached.lean (BlockYesGivesVals) AT THE FIRST
CHAIN: at the 12 feed-forward and the 12 attention batchings by vals_of_step_lay | vals_of_step_att; at the head's batching
(member 347) a named premise here, until that law lies.

Limits. Member 347 stands as a premise. Implications. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ShapeOfReached
import Johnson.AtFull.Shape.Scope.BatchYesAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **BlockYesGivesVals, from the head's batching alone.** -/
theorem blockYes_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hH : ∀ (z : ProofFile.InstPub) (blk : Block S ProofFile.Cl) (s s' : S) (R : List Fmt.RoundView) (c : List OpenedColumn),
      Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, s) → cF.blocksInOrder[347]? = some blk →
      blk.step 0 s R c = .ok (s', c.length) →
      Tab.vals Zp Bs.G₀ 347 s (R.map noDigest) (blk.shown 0 R c) = true) :
    BlockYesGivesVals (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) 0 cF.blocksInOrder (ProofFile.startS Zp)
      (ReqPasses Zp) := by
  intro b hw z _ blk s R c s' hr hb _ hs
  rcases weak_cases hw with ⟨l, hl, rfl⟩ | rfl
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact ProofFile.Honest.K9.vals_of_step_lay h (by omega) hB hb hr hs
    · exact ProofFile.Honest.K9.vals_of_step_att h (by omega) hB hb hr hs
  · exact hH z blk s s' R c hr hb hs

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.blockYes_of_head
