-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/FreeAt341N.lean.
WHAT IT DOES NOT SHOW. No soundness. ONE PREMISE BESIDE "REACHED": hplan: THE SUB-PROTOCOL THAT
STANDS AT 340 PASSES ITS TEST ON THE PLAN: "reached" brings no test on the plan, and without it the
lookup's law on the exchanged hearing says nothing. plan_at HAS IT FROM THE IOP's OWN TEST
ON THE PLAN (F.planOk = true), which passes wherever the IOP's own decision accepts
(Desc/PlanPasses.lean: planOk_of_runEnd). It is a test with code on public data; no example shows
here that it accepts at the release's values.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "The ledger": the
open link's Fork, as S.fork? reads it. "Well laid": its three lists have one entry for each of its
numbers.
LETTERS. "There is": FreeAt's own: the ledger.
OBJECT. In the goals' scope, at the opened value of the IOP as written in Lean: a state reached at
the border 341, in front of the output head's own sub-protocol.
USER. The law on the output head's twelve reads at a reached state (Desc/Reads/RunIsAtBorder.lean:
ReachGives: its third clause).
WHAT IT IS. A FACT ALONG THE CHAIN's FOLD: IN FRONT OF THE OUTPUT HEAD's OWN SUB-PROTOCOL A LEDGER
IS THERE, WELL LAID AND FREE ABOVE: MADE AT 339, KEPT AT 340.
  plan_at           hplan, at any number, from F.planOk = true.
  free_at_341       by P4.back_341, Law/HeadLedgerMade.lean: placeH2_free, and
                    via_freeAt (Desc/First/Look/K3KeepsFree.lean).
  wellLaid_341      so the seat's ledger there is well laid, in the output head's law's own word.

-/
import Johnson.P4R.Back341N
import Johnson.Desc.Kinds.Law.HeadLedgerMade
import Johnson.Stored.HeadSeatAt
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid placeH2_free wellLaid_of_sized)
open VerifiableInference.OnPublicFiles (FreeAt via_freeAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Whence the premise on the plan**: where the IOP's own test on the plan accepts, so does the
test of every sub-protocol of the first chain's flat list (Desc/PlanPasses.lean: planOk_blocks). -/
theorem plan_at (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : F.planOk = true) (k : Nat) : ∀ b, c.blocksInOrder[k]? = some b → b.planOk = true := by
  intro b hb
  have hp0 : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true := O.desc ▸ hOk
  exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hp0).1 b (List.mem_of_getElem? hb)

/-- **In front of the output head's own sub-protocol a ledger is there, well laid and free
above.** -/
theorem free_at_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hplan : ∀ b, c.blocksInOrder[340]? = some b → b.planOk = true) {XP : Type} {start : XP → S} {z : XP}
    {s0 : S} (h : Reach 0 c.blocksInOrder start 341 (z, s0)) : FreeAt (fun s : S => s.fork?) s0 := by
  obtain ⟨_, _, s340, -, -, ⟨p, n, HP, rs, gs, a2⟩, b3, Q, sent, laid, rs3, gs3, f3, hv, hp⟩ :=
    back_341 hS hR O h
  obtain ⟨G, hG, hs, hf, -⟩ := placeH2_free a2
  exact via_freeAt K3Lot.ofForm 3 laid sent Q [] (hp (hplan b3 f3)) s340 rs3 gs3 s0 hv
    ⟨G, hG, hs, hf⟩

/-- So the seat's ledger there is well laid. -/
theorem wellLaid_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hplan : ∀ b, c.blocksInOrder[340]? = some b → b.planOk = true) {XP : Type} {start : XP → S} {z : XP}
    {s0 : S} (h : Reach 0 c.blocksInOrder start 341 (z, s0)) (hh : OnBytes.Model.Head.Shape) (iU3 : Nat) :
    WellLaid ((seatAt hh iU3).ledger s0) := by
  obtain ⟨G, hG, hs, -⟩ := free_at_341 hS hR O hplan h
  have hG' : s0.fork? = some G := hG
  show WellLaid (s0.fork?.getD {})
  rw [hG']
  exact wellLaid_of_sized hs

end P4

#print axioms P4.plan_at
#print axioms P4.free_at_341
#print axioms P4.wellLaid_341
