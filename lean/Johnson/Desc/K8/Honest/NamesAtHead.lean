-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/NamesAtHead.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: `AllFront`
(Johnson/Desc/K8/Honest/LeftAtLink.lean) UNDER THE LIBRARY's HEAD `P5J.AtMgA` ALONE, AT EVERY STATE
THAT THE FIRST CHAIN's BLOCKS WITH THE TEST ON WORDS IN FRONT (`Sound.below`) REACH IN FRONT OF THE
BATCHING OF ONE OF THE 24 SEGMENTS IN FRONT OF THE HEAD's. AND: THE PREMISES OF
Johnson/Desc/K8/Honest/NamesAtBatch.lean CAN BE MET TOGETHER WHEREVER THERE IS A HEAD. Two joinings;
none of the library's goals.

  **`premises_of_head`** out of a head: the scope, the files read, an opening of the description,
                   its test on its plan, and a built segment at each l < 25: together, at the head's
                   own letters
  **`allFront_at_head`** the head · l < 24 · a state that the wrapped blocks reach at 14 l + 9 ⊢
                   there are tl, G, g, nbW, Wn with s.tl? = some tl, s.fork? = some G, tl.heard =
                   some g and AllFront tl G g nbW Wn
By: `allFront_at_wrapped_shown` (NamesAtBatch.lean) · the head's fields scope, reads, laid.opened,
laid.planOk (Johnson/P5J/MgAtAll.lean) · IM.ground_gets (Johnson/IMR/PureJoin.lean: there are 25
built segments).
IS THERE A HEAD? At the three full-size public files `VerifierAndGoals.storedPublicFiles` the library has a member with no
premise: `AtFullSide.Top.headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean), in a side library
that nothing under Johnson/ imports, this file neither: with that file's own limits (one example;
closed facts by evaluation in Lean's kernel; replayed by no independent checker).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED IN FRONT OF A BATCHING: where none is,
`allFront_at_head` is idle; the library's own word at the full size: that the verifier accepts any
proof at these files is not shown. AT THE WRAPPED FAMILY ALONE. NOTHING AT THE HEAD's SEGMENT. At
OnBytes.secondHashFunction alone. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.NamesAtBatch
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker OnBytes.Flat
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA)
open ProofFile (Cl)

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE FOUR PREMISES COME TOGETHER OUT OF THE HEAD**, with a built segment at each l < 25. -/
theorem premises_of_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      VerifierAndGoals.InScope Z = true ∧ VerifierAndGoals.readFiles Z = .ok pp ∧
        IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B ∧
        F.planOk = true ∧ ∀ l, l < 25 → ∃ Xl, Bs.G₀.built[l]? = some Xl := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨_, _, Bs, base, _, _, h.scope, h.reads, O, h.laid.planOk, fun l hl => ?_⟩
  have e := (IM.ground_gets h.scope h.reads O.pub O.blank).1
  exact ⟨_, Array.getElem?_eq_getElem (by rw [e]; exact hl)⟩

/-- **`AllFront` UNDER THE HEAD ALONE**, at every state that the blocks with the test on words in
front reach in front of the batching of a segment l < 24. -/
theorem allFront_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l < 24)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * l + 9) (z, s)) :
    ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat) (Wn : List HTailF2.Want),
      s.tl? = some tl ∧ s.fork? = some G ∧ tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := (IM.ground_gets h.scope h.reads O.pub O.blank).1
  have e3 : Bs.G₀.built[l]? = some (Bs.G₀.built[l]'(by rw [e]; omega)) :=
    Array.getElem?_eq_getElem _
  exact allFront_at_wrapped_shown h.scope h.reads O h.laid.planOk hl e3 hr

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.premises_of_head
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_head
