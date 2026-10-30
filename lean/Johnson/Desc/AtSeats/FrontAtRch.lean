-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FrontAtRch.lean: THE TWO FACTS ALONG REACHED STATES THAT THE TIE AT THE FIRST
SEGMENT's OPENING SPENDS AND NO FIELD OF `First.FoldFacts` GIVES, PAID IN THE GOALS' SCOPE ALONG
"REACHED AT THE DESCRIPTION's FIRST CHAIN" (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean):
at borders 2 and 3, at a state without a mark: the walk's copy of the frame stands at
link 0; nothing is kept. Statements with their proofs: calls. `front_at_rchAt`: the test `frontB`
  (Johnson/Desc/K13/Law/BridgeG.lean) there: by `front_23_seat`
  (Johnson/Desc/AtSeats/FrontAtSeat.lean), whose two premises are paid by two other files'
  lemmas: at border 2 the reached state is the first state (`P1L20.reach_two`,
  Johnson/P1L20R/RoomFold.lean); the sub-protocol at number 2 stands under the joined opening
  (`IM.first_under`, Johnson/IMR/FirstUnder.lean). `link0_at_rchAt`, `kept0_at_rchAt`: its two
  halves: IN THE LETTERS OF THE BINDERS hl0, hk0 of `k01_kind_atThreeF`
  (Johnson/Desc/AtSeats/K01KindAtThreeF.lean [not in this library]) at Rch := `RchAt` of the
  seated description; under
  any narrower condition they hold the more.
THE PREMISES: the scope alone (hS, hR, O).
What is not claimed. That the scope can be met. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.AtSeats.FrontAtSeat
import Johnson.P1L20R.RoomFold
import Johnson.IMR.FirstUnder
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (frontB frontB_iff)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The test at the reached states of borders 2 and 3, in scope.** -/
theorem front_at_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type} (j : ℕ)
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) j a) (hj : j = 2 ∨ j = 2 + 1) (hm : a.1.2.failed = none) : frontB a.1.2 = true := by
  obtain ⟨e, nm, X, hb, _, hu⟩ := IM.first_under hS hR O
  exact front_23_seat O.pub (fun z s h2 => P1L20.reach_two hS hR O h2) hb hu j a.1 (rchAt_raw h) hj
    hm

theorem link0_at_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type} (j : ℕ)
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) j a) (hj : j = 2 ∨ j = 2 + 1) (hm : a.1.2.failed = none) :
    a.1.2.check.frame.link = 0 :=
  ((frontB_iff _).1 (front_at_rchAt hS hR O j a h hj hm)).2.1

theorem kept0_at_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type} (j : ℕ)
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) j a) (hj : j = 2 ∨ j = 2 + 1) (hm : a.1.2.failed = none) :
    a.1.2.check.frame.keptBefore = #[] :=
  ((frontB_iff _).1 (front_at_rchAt hS hR O j a h hj hm)).2.2

end HashBuild
