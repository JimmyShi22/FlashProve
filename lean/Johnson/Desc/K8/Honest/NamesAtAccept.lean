-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/NamesAtAccept.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: `AllFront`
(Johnson/Desc/K8/Honest/LeftAtLink.lean) ALONG EVERY ACCEPTED PROOF: WHEREVER THE VERIFIER's GATE
`theProofGate` SAYS YES TO A PROOF, IN THE GOALS' SCOPE, `AllFront` HOLDS AT THAT RUN's OWN STATE IN
FRONT OF THE BATCHING OF EACH OF THE 24 SEGMENTS IN FRONT OF THE HEAD's. So
Johnson/Desc/K8/Honest/NamesAtBatch.lean is idle nowhere where the verifier accepts. One joining;
none of the library's goals.

  **`allFront_at_accept`** the scope · a yes of theProofGate at (z, v₁, v₂, v₃) ⊢ there are the
                   files' reading, an opening of the description, a yes of its run, and a list of
                   states st: st 0 is the description's own first state; each st k steps to st (k +
                   1) by the block number k with the test on words in front, k < 358; and for each l
                   < 24 there are tl, G, g, nbW, Wn with (st (14 l + 9)).tl? = some tl, (st (14 l +
                   9)).fork? = some G, tl.heard = some g and AllFront tl G g nbW Wn
By: the library's IM.member_path (Johnson/IMR/MemberPath.lean: one list of states, each stepping to
the next, none with a mark, from the two tests on verify()'s own road) · LPFD.Full.planOk_of_run
(Johnson/Desc/Laid/ProofFullLaw.lean) · IM.ground_gets · `allFront_at_wrapped_shown`
(NamesAtBatch.lean).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`.
Limits. THAT THE GATE SAYS YES TO ANY PROOF IS NOT SHOWN, from an honest prover or from anybody:
where it says yes to none, this is idle. It speaks of whatever proof is accepted, not of an honest
prover's. NOTHING AT THE HEAD's SEGMENT. IN SCOPE ALONE; at OnBytes.secondHashFunction alone. No prover stands
in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.NamesAtBatch
import Johnson.IMR.MemberPath
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile (Cl)

/-- **WHEREVER THE VERIFIER's GATE SAYS YES TO A PROOF IN SCOPE: there is the list of states of that
run, each stepping to the next by a block with the test on words in front, and at its state in front
of the batching of each segment l < 24 `AllFront` holds.** -/
theorem allFront_at_accept {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
      (st : ℕ → S),
      VerifierAndGoals.readFiles P = .ok pp ∧
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true ∧
      st 0 = ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub ∧
      (∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧ StepYes 0 (Sound.below b) (st k) (st (k + 1))) ∧
      ∀ l < 24, ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat) (Wn : List Want),
        (st (14 * l + 9)).tl? = some tl ∧ (st (14 * l + 9)).fork? = some G ∧
          tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, st, hR, -, O, hr, -, -, -, h0, hs, hk, -⟩ :=
    IM.member_path hS hg
  refine ⟨pp, F, Z, Bs, base, c, A, B, st, hR, O, hr, h0, hs, fun l hl => ?_⟩
  have e := (IM.ground_gets hS hR O.pub O.blank).1
  have e3 : Bs.G₀.built[l]? = some (Bs.G₀.built[l]'(by rw [e]; omega)) :=
    Array.getElem?_eq_getElem _
  exact allFront_at_wrapped_shown hS hR O (LPFD.Full.planOk_of_run F hr) hl e3
    (hk (14 * l + 9) (by omega)).1

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_accept
