-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-



Johnson/Desc/AtSeats/K13KindRow2.lean: the two counts hNt and hNm of kind K13's row for the
join, at the closed constant.
  told_one      THERE ARE TWO FUNCTIONS «toldOf»: Sound.toldOf (Johnson/Desc/Sound/PieceFence.lean: b.oracles.flatMap id), which the closed constant lays, and First.toldOf (Johnson/Desc/First/NumbersAtBlocks.lean:
                b.oracles.flatten), of which atBlocks is made: NOT ONE BY UNFOLDING: one by a lemma on lists.
  atN_is        the closed constant's numbers ARE «numbers closed over the blocks»: P5J.At.N Zp cF = (P5T.numbersOf (At.pseats Zp)).atBlocks (At.shape Zp) At.links cF.blocksInOrder: the two texts part in «At.ps» against
                «blockPlaces cF.blocksInOrder» (blockPlaces_full: in scope the sub-protocols' own places are the written list) AND IN THE TWO toldOf (told_one).
  counts_atAll  hNt ∧ hNm at the closed constant: at355_in_scope (Johnson/Desc/AtSeats/CountsInScope.lean; in scope, under nothing, at N.atBlocks …): «nothing is declared at place 355».
SAID PLAINLY, AFTER THE PAYER's OWN WORD: the two counts say only that the sub-protocol at 355 declares no tree and no message: true of every N of that form: no example is needed or given.
What is not claimed. That any premise can be met. No member of h.Kind. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13KindRow
import Johnson.Desc.AtSeats.CountsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open OnBytes.Road OnBytes.RunA
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)
open VerifiableInference.Desc.Sound (TiedAtR HandsOn mgAll MgData CellsQ mgBase threeCap)
open Johnson.Desc.First.Walk.Tied (RchAt)

open Johnson.Desc.First.Walk.Tied (handsOn_map)
open VerifiableInference.Desc.Sound (threeCap_ofDesc)

/-- **Two functions of one name are one**: what each sub-protocol tells, all rounds together. -/
theorem told_one {St Cl' : Type} (bs : List (Block St Cl')) : Sound.toldOf bs = First.toldOf bs := by
  unfold Sound.toldOf First.toldOf
  exact List.map_congr_left fun b _ => by simp

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

theorem atN_is : P5J.At.N Zp cF =
    (P5T.numbersOf (P5J.At.pseats Zp)).atBlocks (P5J.At.shape Zp) P5J.At.links cF.blocksInOrder := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  unfold First.Numbers.atBlocks P5J.At.N P5J.At.told
  rw [LPFK9.blockPlaces_full hA.scope hA.reads O, ← P5J.kind_ps, told_one]

theorem counts_atAll :
    hA.𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
        hA.𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[355]? ∧
      hA.𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
        hA.𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[355]? := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  show (P5J.At.N Zp cF).treesAt _ = (P5J.At.N Zp cF).treesAt _ ∧
    (P5J.At.N Zp cF).msgsAt _ = (P5J.At.N Zp cF).msgsAt _
  rw [atN_is hA]
  exact HashBuild.at355_in_scope _ _ _ hA.scope hA.reads O

end

end VerifiableInference.Desc.K13.Law
